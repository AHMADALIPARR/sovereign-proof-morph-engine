-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Haskell semantic reference model of the Morph IR. Independent of the
-- Rust interpreter: reads a program in canonical syntax (as written by the
-- runtime to versions/vNNNN/program.ir) and evaluates `main` on each input
-- value with unbounded Integer arithmetic, the same semantics as
-- `agda/Morph/IR.agda` (ℕ subtraction is truncated). Used for differential
-- testing; it is not a proof authority.
--
--   ref PROGRAM.ir INPUTS     (one value per line, canonical value syntax)
module Main (main) where

import Data.Char (isSpace)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

data Sx = A String | L [Sx]

tokenize :: String -> [String]
tokenize [] = []
tokenize (c : cs)
  | c == '(' || c == ')' = [c] : tokenize cs
  | c == ';' = tokenize (dropWhile (/= '\n') cs)
  | isSpace c = tokenize cs
  | otherwise = let (w, r) = break (\x -> isSpace x || x == '(' || x == ')') (c : cs) in w : tokenize r

parseSx :: [String] -> Either String (Sx, [String])
parseSx [] = Left "unexpected end of input"
parseSx ("(" : ts) = go [] ts
  where
    go acc (")" : r) = Right (L (reverse acc), r)
    go acc r = do
      (x, r') <- parseSx r
      go (x : acc) r'
parseSx (")" : _) = Left "unexpected )"
parseSx (t : ts) = Right (A t, ts)

data Val = VN Integer | VZ Integer | VB Bool | VP Val Val | VL Val | VR Val
  deriving (Eq)

render :: Val -> String
render (VN n) = "(nat " ++ show n ++ ")"
render (VZ i) = "(int " ++ show i ++ ")"
render (VB b) = if b then "true" else "false"
render (VP a b) = "(pair " ++ render a ++ " " ++ render b ++ ")"
render (VL a) = "(inl " ++ render a ++ ")"
render (VR a) = "(inr " ++ render a ++ ")"

data E
  = Lit Val | Var Int | Op1 String E | Op2 String E E | Ite E E E | Let E E
  | Pair E E | Fst E | Snd E | Inl E | Inr E | Case E E E | Iter E E E | Call Int E

val :: Sx -> Either String Val
val (A "true") = Right (VB True)
val (A "false") = Right (VB False)
val (L [A "nat", A n]) = VN <$> num n
val (L [A "int", A n]) = VZ <$> num n
val (L [A "pair", a, b]) = VP <$> val a <*> val b
val (L [A "inl", a]) = VL <$> val a
val (L [A "inr", a]) = VR <$> val a
val _ = Left "malformed value"

num :: String -> Either String Integer
num s = case reads s of
  [(n, "")] -> Right n
  _ -> Left ("bad numeral " ++ s)

expr :: Sx -> Either String E
expr (A ('#' : k)) = Var . fromInteger <$> num k
expr s@(A _) = Lit <$> val s
expr s@(L [A "nat", _]) = Lit <$> val s
expr s@(L [A "int", _]) = Lit <$> val s
expr (L [A o, a]) | o `elem` ["negZ", "notB", "toInt"] = Op1 o <$> expr a
expr (L [A "fst", a]) = Fst <$> expr a
expr (L [A "snd", a]) = Snd <$> expr a
expr (L [A o, a, b]) | o `elem` ops2 = Op2 o <$> expr a <*> expr b
expr (L [A "let", a, b]) = Let <$> expr a <*> expr b
expr (L [A "pair", a, b]) = Pair <$> expr a <*> expr b
expr (L [A "inl", _, a]) = Inl <$> expr a
expr (L [A "inr", _, a]) = Inr <$> expr a
expr (L [A "call", A j, a]) = Call . fromInteger <$> num j <*> expr a
expr (L [A "if", c, a, b]) = Ite <$> expr c <*> expr a <*> expr b
expr (L [A "case", c, a, b]) = Case <$> expr c <*> expr a <*> expr b
expr (L [A "iter", n, z, s]) = Iter <$> expr n <*> expr z <*> expr s
expr _ = Left "malformed expression"

ops2 :: [String]
ops2 = ["addN", "subN", "mulN", "ltN", "eqN", "addZ", "subZ", "mulZ", "ltZ", "eqZ", "andB", "orB"]

prog :: Sx -> Either String [E]
prog (L (A "prog" : ds)) = mapM def ds
  where
    def (L [A "def", _, _, b]) = expr b
    def _ = Left "malformed def"
prog _ = Left "program must start with (prog"

ev1 :: String -> Val -> Either String Val
ev1 "negZ" (VZ i) = Right (VZ (negate i))
ev1 "notB" (VB b) = Right (VB (not b))
ev1 "toInt" (VN n) = Right (VZ n)
ev1 o _ = Left ("stuck: " ++ o)

ev2 :: String -> Val -> Val -> Either String Val
ev2 "addN" (VN a) (VN b) = Right (VN (a + b))
ev2 "subN" (VN a) (VN b) = Right (VN (max 0 (a - b)))
ev2 "mulN" (VN a) (VN b) = Right (VN (a * b))
ev2 "ltN" (VN a) (VN b) = Right (VB (a < b))
ev2 "eqN" (VN a) (VN b) = Right (VB (a == b))
ev2 "addZ" (VZ a) (VZ b) = Right (VZ (a + b))
ev2 "subZ" (VZ a) (VZ b) = Right (VZ (a - b))
ev2 "mulZ" (VZ a) (VZ b) = Right (VZ (a * b))
ev2 "ltZ" (VZ a) (VZ b) = Right (VB (a < b))
ev2 "eqZ" (VZ a) (VZ b) = Right (VB (a == b))
ev2 "andB" (VB a) (VB b) = Right (VB (a && b))
ev2 "orB" (VB a) (VB b) = Right (VB (a || b))
ev2 o _ _ = Left ("stuck: " ++ o)

-- env: index 0 is the innermost binding
eval :: [E] -> Int -> [Val] -> E -> Either String Val
eval ds di env e = case e of
  Lit v -> Right v
  Var k -> if k < length env then Right (env !! k) else Left "unbound variable"
  Op1 o a -> ev a >>= ev1 o
  Op2 o a b -> do x <- ev a; y <- ev b; ev2 o x y
  Ite c a b -> ev c >>= \v -> case v of
    VB True -> ev a
    VB False -> ev b
    _ -> Left "if on non-bool"
  Let a b -> ev a >>= \v -> eval ds di (v : env) b
  Pair a b -> VP <$> ev a <*> ev b
  Fst a -> ev a >>= \v -> case v of VP x _ -> Right x; _ -> Left "fst"
  Snd a -> ev a >>= \v -> case v of VP _ y -> Right y; _ -> Left "snd"
  Inl a -> VL <$> ev a
  Inr a -> VR <$> ev a
  Case c l r -> ev c >>= \v -> case v of
    VL x -> eval ds di (x : env) l
    VR y -> eval ds di (y : env) r
    _ -> Left "case"
  Iter n z s -> ev n >>= \v -> case v of
    VN k -> ev z >>= loop 0 k
      where
        loop i m acc
          | i >= m = Right acc
          | otherwise = eval ds di (acc : VN i : env) s >>= loop (i + 1) m
    _ -> Left "iter count"
  Call j a -> do
    v <- ev a
    let c = di - 1 - j
    if c < 0 then Left "bad call" else eval ds c [v] (ds !! c)
  where
    ev = eval ds di env

main :: IO ()
main = do
  args <- getArgs
  case args of
    [pf, inf] -> do
      ptxt <- readFile pf
      itxt <- readFile inf
      let fail' m = hPutStrLn stderr ("ref: " ++ m) >> exitFailure
      ds <- either fail' pure (parseSx (tokenize ptxt) >>= prog . fst)
      let inputs = filter (not . all isSpace) (lines itxt)
      mapM_
        ( \l -> case parseSx (tokenize l) >>= val . fst of
            Left m -> fail' m
            Right v -> putStrLn (either ("error " ++) render (eval ds (length ds - 1) [v] (last ds)))
        )
        inputs
    _ -> hPutStrLn stderr "usage: ref PROGRAM.ir INPUTS" >> exitFailure
