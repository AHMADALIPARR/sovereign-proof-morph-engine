-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Certified rewrites. Each local step comes with a soundness lemma; the
-- generic bottom-up traversal lifts it to whole expressions; mapP lifts it to
-- programs; spec (function specialization) has its own program-level lemma.
-- Every rewrite has type Expr Σ Γ τ → Expr Σ Γ τ: typing is preserved by
-- construction. Semantics are the unbounded ℕ/ℤ semantics of Morph.IR.
{-# OPTIONS --safe #-}
module Morph.Rewrite where

open import Data.Nat as ℕ using (ℕ; zero; suc; _≤ᵇ_; _≡ᵇ_)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_)
import Data.Integer.Properties as ℤP
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
import Data.Bool.Properties as BP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

open import Morph.IR
open import Morph.Subst

Step : Sig → Set
Step Σ = ∀ {Γ τ} → Expr Σ Γ τ → Expr Σ Γ τ

SoundAt : FEnv Σ → Step Σ → Set
SoundAt {Σ} F st = ∀ {Γ τ} (e : Expr Σ Γ τ) (ρ : Env Γ) → ⟦ st e ⟧ F ρ ≡ ⟦ e ⟧ F ρ

------------------------------------------------------------------------
-- Generic bottom-up traversal.

bu : Step Σ → Step Σ
bu st (lit t v)     = st (lit t v)
bu st (var x)       = st (var x)
bu st (op1 o e)     = st (op1 o (bu st e))
bu st (op2 o e₁ e₂) = st (op2 o (bu st e₁) (bu st e₂))
bu st (ite c e₁ e₂) = st (ite (bu st c) (bu st e₁) (bu st e₂))
bu st (let′ e b)    = st (let′ (bu st e) (bu st b))
bu st (pair e₁ e₂)  = st (pair (bu st e₁) (bu st e₂))
bu st (fst e)       = st (fst (bu st e))
bu st (snd e)       = st (snd (bu st e))
bu st (inl e)       = st (inl (bu st e))
bu st (inr e)       = st (inr (bu st e))
bu st (case e l r)  = st (case (bu st e) (bu st l) (bu st r))
bu st (iter n z s)  = st (iter (bu st n) (bu st z) (bu st s))
bu st (call f e)    = st (call f (bu st e))

ite-cong : ∀ {A : Set} {c c′ : Bool} {x x′ y y′ : A} → c ≡ c′ → x ≡ x′ → y ≡ y′
         → (if c then x else y) ≡ (if c′ then x′ else y′)
ite-cong refl refl refl = refl

bu-sound : ∀ {st : Step Σ} (F : FEnv Σ) → SoundAt F st → SoundAt F (bu st)
bu-sound F h (lit t v) ρ = h (lit t v) ρ
bu-sound F h (var x) ρ = h (var x) ρ
bu-sound {st = st} F h (op1 o e) ρ =
  trans (h (op1 o (bu st e)) ρ) (cong (ev1 o) (bu-sound F h e ρ))
bu-sound {st = st} F h (op2 o e₁ e₂) ρ =
  trans (h _ ρ) (cong₂ (ev2 o) (bu-sound F h e₁ ρ) (bu-sound F h e₂ ρ))
bu-sound {st = st} F h (ite c e₁ e₂) ρ =
  trans (h (ite (bu st c) (bu st e₁) (bu st e₂)) ρ)
        (ite-cong (bu-sound F h c ρ) (bu-sound F h e₁ ρ) (bu-sound F h e₂ ρ))
bu-sound {st = st} F h (let′ e b) ρ =
  trans (h (let′ (bu st e) (bu st b)) ρ)
        (trans (cong (λ v → ⟦ bu st b ⟧ F (v ∷ ρ)) (bu-sound F h e ρ))
               (bu-sound F h b (⟦ e ⟧ F ρ ∷ ρ)))
bu-sound F h (pair e₁ e₂) ρ =
  trans (h _ ρ) (cong₂ _,_ (bu-sound F h e₁ ρ) (bu-sound F h e₂ ρ))
bu-sound F h (fst e) ρ = trans (h _ ρ) (cong proj₁ (bu-sound F h e ρ))
bu-sound F h (snd e) ρ = trans (h _ ρ) (cong proj₂ (bu-sound F h e ρ))
bu-sound F h (inl e) ρ = trans (h _ ρ) (cong inj₁ (bu-sound F h e ρ))
bu-sound F h (inr e) ρ = trans (h _ ρ) (cong inj₂ (bu-sound F h e ρ))
bu-sound {st = st} F h (case e l r) ρ =
  trans (h (case (bu st e) (bu st l) (bu st r)) ρ)
        (trans (cong (λ v → caseV v (λ x → ⟦ bu st l ⟧ F (x ∷ ρ)) (λ y → ⟦ bu st r ⟧ F (y ∷ ρ)))
                     (bu-sound F h e ρ))
               (caseV-cong (⟦ e ⟧ F ρ) (λ x → bu-sound F h l (x ∷ ρ)) (λ y → bu-sound F h r (y ∷ ρ))))
bu-sound {st = st} F h (iter n z s) ρ =
  trans (h (iter (bu st n) (bu st z) (bu st s)) ρ)
        (trans (cong₂ (λ k a → go 0 k a (λ i acc → ⟦ bu st s ⟧ F (acc ∷ i ∷ ρ)))
                      (bu-sound F h n ρ) (bu-sound F h z ρ))
               (go-cong 0 (⟦ n ⟧ F ρ) (⟦ z ⟧ F ρ) (λ i acc → bu-sound F h s (acc ∷ i ∷ ρ))))
bu-sound F h (call f e) ρ = trans (h _ ρ) (cong (F f) (bu-sound F h e ρ))

------------------------------------------------------------------------
-- Views.

data LitV {Σ Γ τ} : Expr Σ Γ τ → Set where
  isLit : (t : IsBase τ) (v : Val τ) → LitV (lit t v)
  other : ∀ {e} → LitV e

litV : (e : Expr Σ Γ τ) → LitV e
litV (lit t v) = isLit t v
litV e         = other

data NatIs {Σ Γ} (k : ℕ) : Expr Σ Γ nat → Set where
  isK  : ∀ {t} → NatIs k (lit t k)
  notK : ∀ {e} → NatIs k e

natIs : (k : ℕ) (e : Expr Σ Γ nat) → NatIs k e
natIs k (lit t v) with v ℕ.≟ k
... | yes refl = isK
... | no _     = notK
natIs k e = notK

data IntIs {Σ Γ} (k : ℤ) : Expr Σ Γ int → Set where
  isK  : ∀ {t} → IntIs k (lit t k)
  notK : ∀ {e} → IntIs k e

intIs : (k : ℤ) (e : Expr Σ Γ int) → IntIs k e
intIs k (lit t v) with v ℤ.≟ k
... | yes refl = isK
... | no _     = notK
intIs k e = notK

data BoolIs {Σ Γ} (k : Bool) : Expr Σ Γ bool → Set where
  isK  : ∀ {t} → BoolIs k (lit t k)
  notK : ∀ {e} → BoolIs k e

boolIs : (k : Bool) (e : Expr Σ Γ bool) → BoolIs k e
boolIs true  (lit t true)  = isK
boolIs false (lit t false) = isK
boolIs k e = notK

------------------------------------------------------------------------
-- 1. Constant folding.

cf-op1 : Op1 a b → Expr Σ Γ a → Expr Σ Γ b
cf-op1 o e with litV e
... | isLit _ x = lit (op1-base o) (ev1 o x)
... | other     = op1 o e

cf-op2 : Op2 a b c → Expr Σ Γ a → Expr Σ Γ b → Expr Σ Γ c
cf-op2 o e₁ e₂ with litV e₁ | litV e₂
... | isLit _ x | isLit _ y = lit (op2-base o) (ev2 o x y)
... | isLit _ x | other     = op2 o e₁ e₂
... | other     | _         = op2 o e₁ e₂

cf-ite : Expr Σ Γ bool → Expr Σ Γ τ → Expr Σ Γ τ → Expr Σ Γ τ
cf-ite c e₁ e₂ with litV c
... | isLit _ true  = e₁
... | isLit _ false = e₂
... | other         = ite c e₁ e₂

cf-iter : Expr Σ Γ nat → Expr Σ Γ τ → Expr Σ (τ ∷ nat ∷ Γ) τ → Expr Σ Γ τ
cf-iter n z s with natIs 0 n
... | isK  = z
... | notK = iter n z s

cf-step : Step Σ
cf-step (op1 o e)     = cf-op1 o e
cf-step (op2 o e₁ e₂) = cf-op2 o e₁ e₂
cf-step (ite c e₁ e₂) = cf-ite c e₁ e₂
cf-step (iter n z s)  = cf-iter n z s
cf-step (lit t v)     = lit t v
cf-step (var x)       = var x
cf-step (let′ e b)    = let′ e b
cf-step (pair e₁ e₂)  = pair e₁ e₂
cf-step (fst e)       = fst e
cf-step (snd e)       = snd e
cf-step (inl e)       = inl e
cf-step (inr e)       = inr e
cf-step (case e l r)  = case e l r
cf-step (call f e)    = call f e

cf-sound : (F : FEnv Σ) → SoundAt F cf-step
cf-sound F (op1 o e) ρ with litV e
... | isLit _ x = refl
... | other     = refl
cf-sound F (op2 o e₁ e₂) ρ with litV e₁ | litV e₂
... | isLit _ x | isLit _ y = refl
... | isLit _ x | other     = refl
... | other     | _         = refl
cf-sound F (ite c e₁ e₂) ρ with litV c
... | isLit _ true  = refl
... | isLit _ false = refl
... | other         = refl
cf-sound F (iter n z s) ρ with natIs 0 n
... | isK  = refl
... | notK = refl
cf-sound F (lit t v) ρ    = refl
cf-sound F (var x) ρ      = refl
cf-sound F (let′ e b) ρ   = refl
cf-sound F (pair e₁ e₂) ρ = refl
cf-sound F (fst e) ρ      = refl
cf-sound F (snd e) ρ      = refl
cf-sound F (inl e) ρ      = refl
cf-sound F (inr e) ρ      = refl
cf-sound F (case e l r) ρ = refl
cf-sound F (call f e) ρ   = refl

------------------------------------------------------------------------
-- 2. Algebraic simplification (identities and annihilators).

alg-addN : Expr Σ Γ nat → Expr Σ Γ nat → Expr Σ Γ nat
alg-addN a b with natIs 0 b | natIs 0 a
... | isK  | _    = a
... | notK | isK  = b
... | notK | notK = op2 addN a b

alg-subN : Expr Σ Γ nat → Expr Σ Γ nat → Expr Σ Γ nat
alg-subN a b with natIs 0 b | natIs 0 a
... | isK  | _    = a
... | notK | isK  = lit nat 0
... | notK | notK = op2 subN a b

alg-mulN : Expr Σ Γ nat → Expr Σ Γ nat → Expr Σ Γ nat
alg-mulN a b with natIs 1 b | natIs 1 a | natIs 0 b | natIs 0 a
... | isK  | _    | _    | _    = a
... | notK | isK  | _    | _    = b
... | notK | notK | isK  | _    = lit nat 0
... | notK | notK | notK | isK  = lit nat 0
... | notK | notK | notK | notK = op2 mulN a b

alg-addZ : Expr Σ Γ int → Expr Σ Γ int → Expr Σ Γ int
alg-addZ a b with intIs (+ 0) b | intIs (+ 0) a
... | isK  | _    = a
... | notK | isK  = b
... | notK | notK = op2 addZ a b

alg-subZ : Expr Σ Γ int → Expr Σ Γ int → Expr Σ Γ int
alg-subZ a b with intIs (+ 0) b
... | isK  = a
... | notK = op2 subZ a b

alg-mulZ : Expr Σ Γ int → Expr Σ Γ int → Expr Σ Γ int
alg-mulZ a b with intIs (+ 1) b | intIs (+ 1) a | intIs (+ 0) b | intIs (+ 0) a
... | isK  | _    | _    | _    = a
... | notK | isK  | _    | _    = b
... | notK | notK | isK  | _    = lit int (+ 0)
... | notK | notK | notK | isK  = lit int (+ 0)
... | notK | notK | notK | notK = op2 mulZ a b

alg-and : Expr Σ Γ bool → Expr Σ Γ bool → Expr Σ Γ bool
alg-and a b with boolIs true b | boolIs true a | boolIs false b | boolIs false a
... | isK  | _    | _    | _    = a
... | notK | isK  | _    | _    = b
... | notK | notK | isK  | _    = lit bool false
... | notK | notK | notK | isK  = lit bool false
... | notK | notK | notK | notK = op2 andB a b

alg-or : Expr Σ Γ bool → Expr Σ Γ bool → Expr Σ Γ bool
alg-or a b with boolIs false b | boolIs false a | boolIs true b | boolIs true a
... | isK  | _    | _    | _    = a
... | notK | isK  | _    | _    = b
... | notK | notK | isK  | _    = lit bool true
... | notK | notK | notK | isK  = lit bool true
... | notK | notK | notK | notK = op2 orB a b

data NotV {Σ Γ} : Expr Σ Γ bool → Set where
  isNot : ∀ x → NotV (op1 notB x)
  noNot : ∀ {e} → NotV e

notV : (e : Expr Σ Γ bool) → NotV e
notV (op1 notB x) = isNot x
notV e = noNot

data NegV {Σ Γ} : Expr Σ Γ int → Set where
  isNeg : ∀ x → NegV (op1 negZ x)
  noNeg : ∀ {e} → NegV e

negV : (e : Expr Σ Γ int) → NegV e
negV (op1 negZ x) = isNeg x
negV e = noNeg

alg-not : Expr Σ Γ bool → Expr Σ Γ bool
alg-not e with notV e
... | isNot x = x
... | noNot   = op1 notB e

alg-neg : Expr Σ Γ int → Expr Σ Γ int
alg-neg e with negV e
... | isNeg x = x
... | noNeg   = op1 negZ e

alg-op2 : Op2 a b c → Expr Σ Γ a → Expr Σ Γ b → Expr Σ Γ c
alg-op2 addN = alg-addN
alg-op2 subN = alg-subN
alg-op2 mulN = alg-mulN
alg-op2 addZ = alg-addZ
alg-op2 subZ = alg-subZ
alg-op2 mulZ = alg-mulZ
alg-op2 andB = alg-and
alg-op2 orB  = alg-or
alg-op2 ltN  = op2 ltN
alg-op2 eqN  = op2 eqN
alg-op2 ltZ  = op2 ltZ
alg-op2 eqZ  = op2 eqZ

alg-op1 : Op1 a b → Expr Σ Γ a → Expr Σ Γ b
alg-op1 notB  = alg-not
alg-op1 negZ  = alg-neg
alg-op1 toInt = op1 toInt

alg-step : Step Σ
alg-step (op1 o e)     = alg-op1 o e
alg-step (op2 o e₁ e₂) = alg-op2 o e₁ e₂
alg-step (lit t v)     = lit t v
alg-step (var x)       = var x
alg-step (ite c e₁ e₂) = ite c e₁ e₂
alg-step (let′ e b)    = let′ e b
alg-step (pair e₁ e₂)  = pair e₁ e₂
alg-step (fst e)       = fst e
alg-step (snd e)       = snd e
alg-step (inl e)       = inl e
alg-step (inr e)       = inr e
alg-step (case e l r)  = case e l r
alg-step (iter n z s)  = iter n z s
alg-step (call f e)    = call f e

module _ (F : FEnv Σ) {Γ : Ctx} (ρ : Env Γ) where
  ⟪_⟫ : ∀ {τ} → Expr Σ Γ τ → Val τ
  ⟪ e ⟫ = ⟦ e ⟧ F ρ

  addN-ok : (a b : Expr Σ Γ nat) → ⟪ alg-addN a b ⟫ ≡ ⟪ a ⟫ ℕ.+ ⟪ b ⟫
  addN-ok a b with natIs 0 b | natIs 0 a
  ... | isK  | _    = sym (ℕP.+-identityʳ _)
  ... | notK | isK  = refl
  ... | notK | notK = refl

  subN-ok : (a b : Expr Σ Γ nat) → ⟪ alg-subN a b ⟫ ≡ ⟪ a ⟫ ℕ.∸ ⟪ b ⟫
  subN-ok a b with natIs 0 b | natIs 0 a
  ... | isK  | _    = refl
  ... | notK | isK  = sym (ℕP.0∸n≡0 ⟪ b ⟫)
  ... | notK | notK = refl

  mulN-ok : (a b : Expr Σ Γ nat) → ⟪ alg-mulN a b ⟫ ≡ ⟪ a ⟫ ℕ.* ⟪ b ⟫
  mulN-ok a b with natIs 1 b | natIs 1 a | natIs 0 b | natIs 0 a
  ... | isK  | _    | _    | _    = sym (ℕP.*-identityʳ _)
  ... | notK | isK  | _    | _    = sym (ℕP.*-identityˡ _)
  ... | notK | notK | isK  | _    = sym (ℕP.*-zeroʳ ⟪ a ⟫)
  ... | notK | notK | notK | isK  = refl
  ... | notK | notK | notK | notK = refl

  addZ-ok : (a b : Expr Σ Γ int) → ⟪ alg-addZ a b ⟫ ≡ ⟪ a ⟫ ℤ.+ ⟪ b ⟫
  addZ-ok a b with intIs (+ 0) b | intIs (+ 0) a
  ... | isK  | _    = sym (ℤP.+-identityʳ _)
  ... | notK | isK  = sym (ℤP.+-identityˡ _)
  ... | notK | notK = refl

  subZ-ok : (a b : Expr Σ Γ int) → ⟪ alg-subZ a b ⟫ ≡ ⟪ a ⟫ ℤ.- ⟪ b ⟫
  subZ-ok a b with intIs (+ 0) b
  ... | isK  = sym (ℤP.+-identityʳ _)
  ... | notK = refl

  mulZ-ok : (a b : Expr Σ Γ int) → ⟪ alg-mulZ a b ⟫ ≡ ⟪ a ⟫ ℤ.* ⟪ b ⟫
  mulZ-ok a b with intIs (+ 1) b | intIs (+ 1) a | intIs (+ 0) b | intIs (+ 0) a
  ... | isK  | _    | _    | _    = sym (ℤP.*-identityʳ _)
  ... | notK | isK  | _    | _    = sym (ℤP.*-identityˡ _)
  ... | notK | notK | isK  | _    = sym (ℤP.*-zeroʳ ⟪ a ⟫)
  ... | notK | notK | notK | isK  = sym (ℤP.*-zeroˡ ⟪ b ⟫)
  ... | notK | notK | notK | notK = refl

  and-ok : (a b : Expr Σ Γ bool) → ⟪ alg-and a b ⟫ ≡ (⟪ a ⟫ ∧ ⟪ b ⟫)
  and-ok a b with boolIs true b | boolIs true a | boolIs false b | boolIs false a
  ... | isK  | _    | _    | _    = sym (BP.∧-identityʳ _)
  ... | notK | isK  | _    | _    = refl
  ... | notK | notK | isK  | _    = sym (BP.∧-zeroʳ _)
  ... | notK | notK | notK | isK  = refl
  ... | notK | notK | notK | notK = refl

  or-ok : (a b : Expr Σ Γ bool) → ⟪ alg-or a b ⟫ ≡ (⟪ a ⟫ ∨ ⟪ b ⟫)
  or-ok a b with boolIs false b | boolIs false a | boolIs true b | boolIs true a
  ... | isK  | _    | _    | _    = sym (BP.∨-identityʳ _)
  ... | notK | isK  | _    | _    = refl
  ... | notK | notK | isK  | _    = sym (BP.∨-zeroʳ _)
  ... | notK | notK | notK | isK  = refl
  ... | notK | notK | notK | notK = refl

  not-ok : (e : Expr Σ Γ bool) → ⟪ alg-not e ⟫ ≡ not ⟪ e ⟫
  not-ok e with notV e
  ... | isNot x = sym (BP.not-involutive _)
  ... | noNot   = refl

  neg-ok : (e : Expr Σ Γ int) → ⟪ alg-neg e ⟫ ≡ ℤ.- ⟪ e ⟫
  neg-ok e with negV e
  ... | isNeg x = sym (ℤP.neg-involutive _)
  ... | noNeg   = refl

alg-sound : (F : FEnv Σ) → SoundAt F alg-step
alg-sound F (op1 notB e) ρ  = not-ok F ρ e
alg-sound F (op1 negZ e) ρ  = neg-ok F ρ e
alg-sound F (op1 toInt e) ρ = refl
alg-sound F (op2 addN a b) ρ = addN-ok F ρ a b
alg-sound F (op2 subN a b) ρ = subN-ok F ρ a b
alg-sound F (op2 mulN a b) ρ = mulN-ok F ρ a b
alg-sound F (op2 addZ a b) ρ = addZ-ok F ρ a b
alg-sound F (op2 subZ a b) ρ = subZ-ok F ρ a b
alg-sound F (op2 mulZ a b) ρ = mulZ-ok F ρ a b
alg-sound F (op2 andB a b) ρ = and-ok F ρ a b
alg-sound F (op2 orB a b) ρ  = or-ok F ρ a b
alg-sound F (op2 ltN a b) ρ  = refl
alg-sound F (op2 eqN a b) ρ  = refl
alg-sound F (op2 ltZ a b) ρ  = refl
alg-sound F (op2 eqZ a b) ρ  = refl
alg-sound F (lit t v) ρ      = refl
alg-sound F (var x) ρ        = refl
alg-sound F (ite c e₁ e₂) ρ  = refl
alg-sound F (let′ e b) ρ     = refl
alg-sound F (pair e₁ e₂) ρ   = refl
alg-sound F (fst e) ρ        = refl
alg-sound F (snd e) ρ        = refl
alg-sound F (inl e) ρ        = refl
alg-sound F (inr e) ρ        = refl
alg-sound F (case e l r) ρ   = refl
alg-sound F (iter n z s) ρ   = refl
alg-sound F (call f e) ρ     = refl

------------------------------------------------------------------------
-- 3. Dead-code elimination: unused let bindings and dead pair components.

idx : τ ∈ Γ → ℕ
idx here      = 0
idx (there x) = suc (idx x)

occ : ℕ → Expr Σ Γ τ → Bool
occ k (lit t v)     = false
occ k (var x)       = idx x ≡ᵇ k
occ k (op1 o e)     = occ k e
occ k (op2 o e₁ e₂) = occ k e₁ ∨ occ k e₂
occ k (ite c e₁ e₂) = occ k c ∨ (occ k e₁ ∨ occ k e₂)
occ k (let′ e b)    = occ k e ∨ occ (suc k) b
occ k (pair e₁ e₂)  = occ k e₁ ∨ occ k e₂
occ k (fst e)       = occ k e
occ k (snd e)       = occ k e
occ k (inl e)       = occ k e
occ k (inr e)       = occ k e
occ k (case e l r)  = occ k e ∨ (occ (suc k) l ∨ occ (suc k) r)
occ k (iter n z s)  = occ k n ∨ (occ k z ∨ occ (suc (suc k)) s)
occ k (call f e)    = occ k e

data PairV {Σ Γ a b} : Expr Σ Γ (a ⊗ b) → Set where
  isPair : ∀ x y → PairV (pair x y)
  noPair : ∀ {e} → PairV e

pairV : (e : Expr Σ Γ (a ⊗ b)) → PairV e
pairV (pair x y) = isPair x y
pairV e = noPair

-- Removing an unused binding is the substitution b[e/0], which is sound
-- unconditionally; the occurrence test only decides when it is applied.
dce-let : Expr Σ Γ σ → Expr Σ (σ ∷ Γ) τ → Expr Σ Γ τ
dce-let e b with occ 0 b
... | false = subst (sub1 e) b
... | true  = let′ e b

dce-fst : Expr Σ Γ (a ⊗ b) → Expr Σ Γ a
dce-fst e with pairV e
... | isPair x y = x
... | noPair     = fst e

dce-snd : Expr Σ Γ (a ⊗ b) → Expr Σ Γ b
dce-snd e with pairV e
... | isPair x y = y
... | noPair     = snd e

dce-step : Step Σ
dce-step (let′ e b)    = dce-let e b
dce-step (fst e)       = dce-fst e
dce-step (snd e)       = dce-snd e
dce-step (lit t v)     = lit t v
dce-step (var x)       = var x
dce-step (op1 o e)     = op1 o e
dce-step (op2 o e₁ e₂) = op2 o e₁ e₂
dce-step (ite c e₁ e₂) = ite c e₁ e₂
dce-step (pair e₁ e₂)  = pair e₁ e₂
dce-step (inl e)       = inl e
dce-step (inr e)       = inr e
dce-step (case e l r)  = case e l r
dce-step (iter n z s)  = iter n z s
dce-step (call f e)    = call f e

dce-sound : (F : FEnv Σ) → SoundAt F dce-step
dce-sound F (let′ e b) ρ with occ 0 b
... | false = sub1-sound e b F ρ
... | true  = refl
dce-sound F (fst e) ρ with pairV e
... | isPair x y = refl
... | noPair     = refl
dce-sound F (snd e) ρ with pairV e
... | isPair x y = refl
... | noPair     = refl
dce-sound F (lit t v) ρ     = refl
dce-sound F (var x) ρ       = refl
dce-sound F (op1 o e) ρ     = refl
dce-sound F (op2 o e₁ e₂) ρ = refl
dce-sound F (ite c e₁ e₂) ρ = refl
dce-sound F (pair e₁ e₂) ρ  = refl
dce-sound F (inl e) ρ       = refl
dce-sound F (inr e) ρ       = refl
dce-sound F (case e l r) ρ  = refl
dce-sound F (iter n z s) ρ  = refl
dce-sound F (call f e) ρ    = refl

------------------------------------------------------------------------
-- 4. Partial evaluation: propagate literal / variable bindings, reduce
--    case on a known injection, unroll iteration with a known small count.

data AtomV {Σ Γ σ} : Expr Σ Γ σ → Set where
  isAtomL : ∀ t v → AtomV (lit t v)
  isAtomV : ∀ x → AtomV (var x)
  noAtom  : ∀ {e} → AtomV e

atomV : (e : Expr Σ Γ σ) → AtomV e
atomV (lit t v) = isAtomL t v
atomV (var x)   = isAtomV x
atomV e         = noAtom

data InjV {Σ Γ a b} : Expr Σ Γ (a ⊕ b) → Set where
  isInl : ∀ x → InjV (inl x)
  isInr : ∀ y → InjV (inr y)
  noInj : ∀ {e} → InjV e

injV : (e : Expr Σ Γ (a ⊕ b)) → InjV e
injV (inl x) = isInl x
injV (inr y) = isInr y
injV e       = noInj

stepSub : ℕ → Sub Σ (τ ∷ nat ∷ Γ) (τ ∷ Γ)
stepSub i here              = var here
stepSub i (there here)      = lit nat i
stepSub i (there (there x)) = var (there x)

unroll : ℕ → ℕ → Expr Σ Γ τ → Expr Σ (τ ∷ nat ∷ Γ) τ → Expr Σ Γ τ
unroll i zero    acc s = acc
unroll i (suc r) acc s = unroll (suc i) r (let′ acc (subst (stepSub i) s)) s

unroll-sound : ∀ (F : FEnv Σ) (ρ : Env Γ) i r (acc : Expr Σ Γ τ) s
  → ⟦ unroll i r acc s ⟧ F ρ ≡ go i r (⟦ acc ⟧ F ρ) (λ j x → ⟦ s ⟧ F (x ∷ j ∷ ρ))
unroll-sound F ρ i zero acc s = refl
unroll-sound F ρ i (suc r) acc s =
  trans (unroll-sound F ρ (suc i) r (let′ acc (subst (stepSub i) s)) s)
        (cong (λ v → go (suc i) r v (λ j x → ⟦ s ⟧ F (x ∷ j ∷ ρ))) step-ok)
  where
  v = ⟦ acc ⟧ F ρ
  ok : SubOK (stepSub i) F (v ∷ i ∷ ρ) (v ∷ ρ)
  ok here              = refl
  ok (there here)      = refl
  ok (there (there x)) = refl
  step-ok : ⟦ subst (stepSub i) s ⟧ F (v ∷ ρ) ≡ ⟦ s ⟧ F (v ∷ i ∷ ρ)
  step-ok = subst-sound (stepSub i) s F (v ∷ i ∷ ρ) (v ∷ ρ) ok

pe-let : Expr Σ Γ σ → Expr Σ (σ ∷ Γ) τ → Expr Σ Γ τ
pe-let e b with atomV e
... | isAtomL t v = subst (sub1 e) b
... | isAtomV x   = subst (sub1 e) b
... | noAtom      = let′ e b

pe-case : Expr Σ Γ (a ⊕ b) → Expr Σ (a ∷ Γ) τ → Expr Σ (b ∷ Γ) τ → Expr Σ Γ τ
pe-case e l r with injV e
... | isInl x = subst (sub1 x) l
... | isInr y = subst (sub1 y) r
... | noInj   = case e l r

pe-iter : ℕ → Expr Σ Γ nat → Expr Σ Γ τ → Expr Σ (τ ∷ nat ∷ Γ) τ → Expr Σ Γ τ
pe-iter k n z s with litV n
... | other     = iter n z s
... | isLit _ m with m ≤ᵇ k
...   | true  = unroll 0 m z s
...   | false = iter n z s

pe-step : ℕ → Step Σ
pe-step k (let′ e b)    = pe-let e b
pe-step k (case e l r)  = pe-case e l r
pe-step k (iter n z s)  = pe-iter k n z s
pe-step k (lit t v)     = lit t v
pe-step k (var x)       = var x
pe-step k (op1 o e)     = op1 o e
pe-step k (op2 o e₁ e₂) = op2 o e₁ e₂
pe-step k (ite c e₁ e₂) = ite c e₁ e₂
pe-step k (pair e₁ e₂)  = pair e₁ e₂
pe-step k (fst e)       = fst e
pe-step k (snd e)       = snd e
pe-step k (inl e)       = inl e
pe-step k (inr e)       = inr e
pe-step k (call f e)    = call f e

pe-sound : ∀ k (F : FEnv Σ) → SoundAt F (pe-step k)
pe-sound k F (let′ e b) ρ with atomV e
... | isAtomL t v = sub1-sound e b F ρ
... | isAtomV x   = sub1-sound e b F ρ
... | noAtom      = refl
pe-sound k F (case e l r) ρ with injV e
... | isInl x = sub1-sound x l F ρ
... | isInr y = sub1-sound y r F ρ
... | noInj   = refl
pe-sound k F (iter n z s) ρ with litV n
... | other     = refl
... | isLit _ m with m ≤ᵇ k
...   | true  = unroll-sound F ρ 0 m z s
...   | false = refl
pe-sound k F (lit t v) ρ     = refl
pe-sound k F (var x) ρ       = refl
pe-sound k F (op1 o e) ρ     = refl
pe-sound k F (op2 o e₁ e₂) ρ = refl
pe-sound k F (ite c e₁ e₂) ρ = refl
pe-sound k F (pair e₁ e₂) ρ  = refl
pe-sound k F (fst e) ρ       = refl
pe-sound k F (snd e) ρ       = refl
pe-sound k F (inl e) ρ       = refl
pe-sound k F (inr e) ρ       = refl
pe-sound k F (call f e) ρ    = refl

------------------------------------------------------------------------
-- 6. Safe expression fusion: reassociate constant chains.
--    (x + c₁) + c₂ → x + (c₁ + c₂) on ℕ and ℤ; (x * c₁) * c₂ → x * (c₁ * c₂);
--    (x + c₁) - c₂ → x + (c₁ - c₂) on ℤ only (unsound for truncated ℕ).

data OpLitV {Σ Γ τ} (o : Op2 τ τ τ) : Expr Σ Γ τ → Set where
  isOL : ∀ x t c → OpLitV o (op2 o x (lit t c))
  noOL : ∀ {e} → OpLitV o e

addNV : (e : Expr Σ Γ nat) → OpLitV addN e
addNV (op2 addN x (lit t c)) = isOL x t c
addNV e = noOL

mulNV : (e : Expr Σ Γ nat) → OpLitV mulN e
mulNV (op2 mulN x (lit t c)) = isOL x t c
mulNV e = noOL

addZV : (e : Expr Σ Γ int) → OpLitV addZ e
addZV (op2 addZ x (lit t c)) = isOL x t c
addZV e = noOL

mulZV : (e : Expr Σ Γ int) → OpLitV mulZ e
mulZV (op2 mulZ x (lit t c)) = isOL x t c
mulZV e = noOL

fuse-addN : Expr Σ Γ nat → Expr Σ Γ nat → Expr Σ Γ nat
fuse-addN a b with addNV a | litV b
... | isOL x _ c | isLit _ d = op2 addN x (lit nat (c ℕ.+ d))
... | isOL x _ c | other     = op2 addN a b
... | noOL       | _         = op2 addN a b

fuse-mulN : Expr Σ Γ nat → Expr Σ Γ nat → Expr Σ Γ nat
fuse-mulN a b with mulNV a | litV b
... | isOL x _ c | isLit _ d = op2 mulN x (lit nat (c ℕ.* d))
... | isOL x _ c | other     = op2 mulN a b
... | noOL       | _         = op2 mulN a b

fuse-addZ : Expr Σ Γ int → Expr Σ Γ int → Expr Σ Γ int
fuse-addZ a b with addZV a | litV b
... | isOL x _ c | isLit _ d = op2 addZ x (lit int (c ℤ.+ d))
... | isOL x _ c | other     = op2 addZ a b
... | noOL       | _         = op2 addZ a b

fuse-subZ : Expr Σ Γ int → Expr Σ Γ int → Expr Σ Γ int
fuse-subZ a b with addZV a | litV b
... | isOL x _ c | isLit _ d = op2 addZ x (lit int (c ℤ.- d))
... | isOL x _ c | other     = op2 subZ a b
... | noOL       | _         = op2 subZ a b

fuse-mulZ : Expr Σ Γ int → Expr Σ Γ int → Expr Σ Γ int
fuse-mulZ a b with mulZV a | litV b
... | isOL x _ c | isLit _ d = op2 mulZ x (lit int (c ℤ.* d))
... | isOL x _ c | other     = op2 mulZ a b
... | noOL       | _         = op2 mulZ a b

fuse-op2 : Op2 a b c → Expr Σ Γ a → Expr Σ Γ b → Expr Σ Γ c
fuse-op2 addN = fuse-addN
fuse-op2 mulN = fuse-mulN
fuse-op2 addZ = fuse-addZ
fuse-op2 subZ = fuse-subZ
fuse-op2 mulZ = fuse-mulZ
fuse-op2 subN = op2 subN
fuse-op2 ltN  = op2 ltN
fuse-op2 eqN  = op2 eqN
fuse-op2 ltZ  = op2 ltZ
fuse-op2 eqZ  = op2 eqZ
fuse-op2 andB = op2 andB
fuse-op2 orB  = op2 orB

fuse-step : Step Σ
fuse-step (op2 o e₁ e₂) = fuse-op2 o e₁ e₂
fuse-step (lit t v)     = lit t v
fuse-step (var x)       = var x
fuse-step (op1 o e)     = op1 o e
fuse-step (ite c e₁ e₂) = ite c e₁ e₂
fuse-step (let′ e b)    = let′ e b
fuse-step (pair e₁ e₂)  = pair e₁ e₂
fuse-step (fst e)       = fst e
fuse-step (snd e)       = snd e
fuse-step (inl e)       = inl e
fuse-step (inr e)       = inr e
fuse-step (case e l r)  = case e l r
fuse-step (iter n z s)  = iter n z s
fuse-step (call f e)    = call f e

fuse-sound : (F : FEnv Σ) → SoundAt F fuse-step
fuse-sound F (op2 addN a b) ρ with addNV a | litV b
... | isOL x _ c | isLit _ d = sym (ℕP.+-assoc (⟦ x ⟧ F ρ) c d)
... | isOL x _ c | other     = refl
... | noOL       | _         = refl
fuse-sound F (op2 mulN a b) ρ with mulNV a | litV b
... | isOL x _ c | isLit _ d = sym (ℕP.*-assoc (⟦ x ⟧ F ρ) c d)
... | isOL x _ c | other     = refl
... | noOL       | _         = refl
fuse-sound F (op2 addZ a b) ρ with addZV a | litV b
... | isOL x _ c | isLit _ d = sym (ℤP.+-assoc (⟦ x ⟧ F ρ) c d)
... | isOL x _ c | other     = refl
... | noOL       | _         = refl
fuse-sound F (op2 subZ a b) ρ with addZV a | litV b
... | isOL x _ c | isLit _ d = sym (ℤP.+-assoc (⟦ x ⟧ F ρ) c (ℤ.- d))
... | isOL x _ c | other     = refl
... | noOL       | _         = refl
fuse-sound F (op2 mulZ a b) ρ with mulZV a | litV b
... | isOL x _ c | isLit _ d = sym (ℤP.*-assoc (⟦ x ⟧ F ρ) c d)
... | isOL x _ c | other     = refl
... | noOL       | _         = refl
fuse-sound F (op2 subN a b) ρ = refl
fuse-sound F (op2 ltN a b) ρ  = refl
fuse-sound F (op2 eqN a b) ρ  = refl
fuse-sound F (op2 ltZ a b) ρ  = refl
fuse-sound F (op2 eqZ a b) ρ  = refl
fuse-sound F (op2 andB a b) ρ = refl
fuse-sound F (op2 orB a b) ρ  = refl
fuse-sound F (lit t v) ρ      = refl
fuse-sound F (var x) ρ        = refl
fuse-sound F (op1 o e) ρ      = refl
fuse-sound F (ite c e₁ e₂) ρ  = refl
fuse-sound F (let′ e b) ρ     = refl
fuse-sound F (pair e₁ e₂) ρ   = refl
fuse-sound F (fst e) ρ        = refl
fuse-sound F (snd e) ρ        = refl
fuse-sound F (inl e) ρ        = refl
fuse-sound F (inr e) ρ        = refl
fuse-sound F (case e l r) ρ   = refl
fuse-sound F (iter n z s) ρ   = refl
fuse-sound F (call f e) ρ     = refl

------------------------------------------------------------------------
-- Passes, program lifting, and chains.

data Pass : Set where
  cf alg dce fuse : Pass
  pe : ℕ → Pass

pass : Pass → Step Σ
pass cf     = bu cf-step
pass alg    = bu alg-step
pass dce    = bu dce-step
pass fuse   = bu fuse-step
pass (pe k) = bu (pe-step k)

pass-sound : ∀ p (F : FEnv Σ) → SoundAt F (pass p)
pass-sound cf F     = bu-sound F (cf-sound F)
pass-sound alg F    = bu-sound F (alg-sound F)
pass-sound dce F    = bu-sound F (dce-sound F)
pass-sound fuse F   = bu-sound F (fuse-sound F)
pass-sound (pe k) F = bu-sound F (pe-sound k F)

mapP : Pass → Prog Σ → Prog Σ
mapP p []       = []
mapP p (P ▷ b)  = mapP p P ▷ pass p b

mapP-sound : ∀ p (P : Prog Σ) → FEq ⟦ mapP p P ⟧p ⟦ P ⟧p
mapP-sound p (P ▷ b) here v =
  trans (pass-sound p ⟦ mapP p P ⟧p b (v ∷ [])) (congF (mapP-sound p P) b (v ∷ []))
mapP-sound p (P ▷ b) (there m) v = mapP-sound p P m v

runPasses : List Pass → Prog Σ → Prog Σ
runPasses []       P = P
runPasses (p ∷ ps) P = runPasses ps (mapP p P)

runPasses-sound : ∀ ps (P : Prog Σ) → FEq ⟦ runPasses ps P ⟧p ⟦ P ⟧p
runPasses-sound []       P m v = refl
runPasses-sound (p ∷ ps) P m v =
  trans (runPasses-sound ps (mapP p P) m v) (mapP-sound p P m v)

-- Observational equivalence of programs (on main), and chain composition.
infix 4 _≈_
_≈_ : ∀ {x y Σ Σ'} → Prog ((x , y) ∷ Σ) → Prog ((x , y) ∷ Σ') → Set
_≈_ {x} P Q = ∀ (u : Val x) → runMain P u ≡ runMain Q u

≈-refl : ∀ {x y Σ} {P : Prog ((x , y) ∷ Σ)} → P ≈ P
≈-refl u = refl

≈-sym : ∀ {x y Σ Σ'} {P : Prog ((x , y) ∷ Σ)} {Q : Prog ((x , y) ∷ Σ')} → P ≈ Q → Q ≈ P
≈-sym h u = sym (h u)

≈-trans : ∀ {x y Σ₁ Σ₂ Σ₃} {P : Prog ((x , y) ∷ Σ₁)} {Q : Prog ((x , y) ∷ Σ₂)}
            {R : Prog ((x , y) ∷ Σ₃)} → P ≈ Q → Q ≈ R → P ≈ R
≈-trans h k u = trans (h u) (k u)

passes-≈ : ∀ {x y Σ} ps (P : Prog ((x , y) ∷ Σ)) → runPasses ps P ≈ P
passes-≈ ps P u = runPasses-sound ps P here u

------------------------------------------------------------------------
-- 5. Function specialization on a literal second component.

data SameMem {A : Set} {xs : List A} {x : A} (m : x ∈ xs) : ∀ {y} → y ∈ xs → Set where
  same : SameMem m m

same? : ∀ {A : Set} {xs : List A} {x y : A} (m : x ∈ xs) (m′ : y ∈ xs) → Maybe (SameMem m m′)
same? here here = just same
same? (there m) (there m′) with same? m m′
... | just same = just same
... | nothing   = nothing
same? _ _ = nothing

eqVal : IsBase c → (v w : Val c) → Dec (v ≡ w)
eqVal nat  v w = v ℕ.≟ w
eqVal int  v w = v ℤ.≟ w
eqVal bool v w = v BP.≟ w

record Def (P : Prog Σ) {a b} (m : (a , b) ∈ Σ) : Set where
  field
    {Σd} : Sig
    wk   : SRen Σd Σ
    body : Expr Σd (a ∷ []) b
    ok   : ∀ v → ⟦ P ⟧p m v ≡ ⟦ body ⟧ (λ m′ → ⟦ P ⟧p (wk m′)) (v ∷ [])

lookupDef : (P : Prog Σ) {a b : Ty} (m : (a , b) ∈ Σ) → Def P m
lookupDef (P ▷ body) here = record { wk = there ; body = body ; ok = λ v → refl }
lookupDef (P ▷ _) (there m) =
  record { wk = λ m′ → there (Def.wk d m′) ; body = Def.body d ; ok = Def.ok d }
  where d = lookupDef P m

wk1 : Ren (σ ∷ []) (σ ∷ a ∷ [])
wk1 here = here

fbody : (P : Prog Σ) (m : (a ⊗ c , b) ∈ Σ) → IsBase c → Val c → Expr Σ (a ∷ []) b
fbody P m t v =
  let′ (pair (var here) (lit t v)) (rename wk1 (srename (Def.wk d) (Def.body d)))
  where d = lookupDef P m

fbody-ok : ∀ (P : Prog Σ) (m : (a ⊗ c , b) ∈ Σ) t v (u : Val a)
         → ⟦ fbody P m t v ⟧ ⟦ P ⟧p (u ∷ []) ≡ ⟦ P ⟧p m (u , v)
fbody-ok P m t v u =
  trans (rename-sound wk1 (srename (Def.wk d) (Def.body d)) ⟦ P ⟧p
           ((u , v) ∷ []) ((u , v) ∷ u ∷ []) ren-ok)
  (trans (srename-sound (Def.wk d) (Def.body d) (λ m′ → ⟦ P ⟧p (Def.wk d m′)) ⟦ P ⟧p
            ((u , v) ∷ []) (λ m′ w → refl))
         (sym (Def.ok d (u , v))))
  where
  d = lookupDef P m
  ren-ok : RenOK wk1 ((u , v) ∷ []) ((u , v) ∷ u ∷ [])
  ren-ok here = refl

data CallV {Σ Γ a b c} (m : (a ⊗ c , b) ∈ Σ) : ∀ {τ} → Expr ((a , b) ∷ Σ) Γ τ → Set where
  hit  : ∀ (e : Expr ((a , b) ∷ Σ) Γ a) (t : IsBase c) (w : Val c)
       → CallV m (call (there m) (pair e (lit t w)))
  miss : ∀ {τ} {e : Expr ((a , b) ∷ Σ) Γ τ} → CallV m e

callV : ∀ {Σ Γ a b c τ} (m : (a ⊗ c , b) ∈ Σ) (e : Expr ((a , b) ∷ Σ) Γ τ) → CallV m e
callV m (call (there m′) (pair e (lit t w))) with same? m m′
... | just same = hit e t w
... | nothing   = miss
callV m e = miss

respec : (m : (a ⊗ c , b) ∈ Σ) → Val c → Step ((a , b) ∷ Σ)
respec m v e with callV m e
... | miss = e
... | hit e′ t w with eqVal t v w
...   | yes _ = call here e′
...   | no _  = e

respec-sound : ∀ (m : (a ⊗ c , b) ∈ Σ) v (F : FEnv ((a , b) ∷ Σ))
             → (∀ u → F here u ≡ F (there m) (u , v)) → SoundAt F (respec m v)
respec-sound m v F h e ρ with callV m e
... | miss = refl
... | hit e′ t w with eqVal t v w
...   | yes refl = h (⟦ e′ ⟧ F ρ)
...   | no _     = refl

spec : ∀ {x y} (P : Prog Σ) (main : Expr Σ (x ∷ []) y) (m : (a ⊗ c , b) ∈ Σ)
     → IsBase c → Val c → Prog ((x , y) ∷ (a , b) ∷ Σ)
spec P main m t v = (P ▷ fbody P m t v) ▷ bu (respec m v) (srename there main)

spec-≈ : ∀ {x y} (P : Prog Σ) (main : Expr Σ (x ∷ []) y) (m : (a ⊗ c , b) ∈ Σ)
         (t : IsBase c) (v : Val c) → spec P main m t v ≈ (P ▷ main)
spec-≈ P main m t v u =
  trans (bu-sound F1 (respec-sound m v F1 (fbody-ok P m t v)) (srename there main) (u ∷ []))
        (srename-sound there main ⟦ P ⟧p F1 (u ∷ []) (λ m′ w → refl))
  where F1 = ⟦ P ▷ fbody P m t v ⟧p

-- Specialization phrased on whole programs, so that rewrite scripts compose
-- by ordinary function application.
specP : ∀ {x y} → Prog ((x , y) ∷ Σ) → (m : (a ⊗ c , b) ∈ Σ) → IsBase c → Val c
      → Prog ((x , y) ∷ (a , b) ∷ Σ)
specP (P ▷ main) m t v = spec P main m t v

specP-≈ : ∀ {x y} (Q : Prog ((x , y) ∷ Σ)) (m : (a ⊗ c , b) ∈ Σ) (t : IsBase c) (v : Val c)
        → specP Q m t v ≈ Q
specP-≈ (P ▷ main) m t v = spec-≈ P main m t v
