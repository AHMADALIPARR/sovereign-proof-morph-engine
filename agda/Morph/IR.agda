-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Certified fragment of the Morph IR: intrinsically typed syntax, so every
-- function  Expr Σ Γ τ → Expr Σ Γ τ  preserves typing by construction.
-- Denotational semantics over unbounded ℕ / ℤ / Bool / × / ⊎.
{-# OPTIONS --safe --without-K #-}
module Morph.IR where

open import Data.Nat as ℕ using (ℕ; zero; suc; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Integer as ℤ using (ℤ)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

infixr 6 _⊗_
infixr 5 _⊕_
data Ty : Set where
  nat int bool : Ty
  _⊗_ _⊕_      : Ty → Ty → Ty

Val : Ty → Set
Val nat     = ℕ
Val int     = ℤ
Val bool    = Bool
Val (a ⊗ b) = Val a × Val b
Val (a ⊕ b) = Val a ⊎ Val b


data IsBase : Ty → Set where
  nat  : IsBase nat
  int  : IsBase int
  bool : IsBase bool

data Op1 : Ty → Ty → Set where
  negZ  : Op1 int int
  notB  : Op1 bool bool
  toInt : Op1 nat int

data Op2 : Ty → Ty → Ty → Set where
  addN subN mulN : Op2 nat nat nat
  ltN eqN        : Op2 nat nat bool
  addZ subZ mulZ : Op2 int int int
  ltZ eqZ        : Op2 int int bool
  andB orB       : Op2 bool bool bool

op2-base : ∀ {a b c} → Op2 a b c → IsBase c
op2-base addN = nat
op2-base subN = nat
op2-base mulN = nat
op2-base ltN  = bool
op2-base eqN  = bool
op2-base addZ = int
op2-base subZ = int
op2-base mulZ = int
op2-base ltZ  = bool
op2-base eqZ  = bool
op2-base andB = bool
op2-base orB  = bool

op1-base : ∀ {a b} → Op1 a b → IsBase b
op1-base negZ  = int
op1-base notB  = bool
op1-base toInt = int

ev1 : ∀ {a b} → Op1 a b → Val a → Val b
ev1 negZ  x = ℤ.- x
ev1 notB  x = not x
ev1 toInt x = ℤ.+ x

ev2 : ∀ {a b c} → Op2 a b c → Val a → Val b → Val c
ev2 addN x y = x ℕ.+ y
ev2 subN x y = x ∸ y
ev2 mulN x y = x ℕ.* y
ev2 ltN  x y = x <ᵇ y
ev2 eqN  x y = x ≡ᵇ y
ev2 addZ x y = x ℤ.+ y
ev2 subZ x y = x ℤ.- y
ev2 mulZ x y = x ℤ.* y
ev2 ltZ  x y = does (x ℤ.<? y)
ev2 eqZ  x y = does (x ℤ.≟ y)
ev2 andB x y = x ∧ y
ev2 orB  x y = x ∨ y

infix 4 _∈_
data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {x xs} → x ∈ x ∷ xs
  there : ∀ {x y xs} → x ∈ xs → x ∈ y ∷ xs

Ctx = List Ty
Sig = List (Ty × Ty)

variable
  Σ Σ' : Sig
  Γ Δ  : Ctx
  a b c σ τ : Ty

data Expr (Σ : Sig) (Γ : Ctx) : Ty → Set where
  lit  : IsBase τ → Val τ → Expr Σ Γ τ
  var  : τ ∈ Γ → Expr Σ Γ τ
  op1  : Op1 a b → Expr Σ Γ a → Expr Σ Γ b
  op2  : Op2 a b c → Expr Σ Γ a → Expr Σ Γ b → Expr Σ Γ c
  ite  : Expr Σ Γ bool → Expr Σ Γ τ → Expr Σ Γ τ → Expr Σ Γ τ
  let′ : Expr Σ Γ σ → Expr Σ (σ ∷ Γ) τ → Expr Σ Γ τ
  pair : Expr Σ Γ a → Expr Σ Γ b → Expr Σ Γ (a ⊗ b)
  fst  : Expr Σ Γ (a ⊗ b) → Expr Σ Γ a
  snd  : Expr Σ Γ (a ⊗ b) → Expr Σ Γ b
  inl  : Expr Σ Γ a → Expr Σ Γ (a ⊕ b)
  inr  : Expr Σ Γ b → Expr Σ Γ (a ⊕ b)
  case : Expr Σ Γ (a ⊕ b) → Expr Σ (a ∷ Γ) τ → Expr Σ (b ∷ Γ) τ → Expr Σ Γ τ
  -- iter n z s : acc₀ = z, acc_{i+1} = s[acc := acc_i , i := i], result acc_n
  iter : Expr Σ Γ nat → Expr Σ Γ τ → Expr Σ (τ ∷ nat ∷ Γ) τ → Expr Σ Γ τ
  call : (a , b) ∈ Σ → Expr Σ Γ a → Expr Σ Γ b

data Env : Ctx → Set where
  []  : Env []
  _∷_ : Val τ → Env Γ → Env (τ ∷ Γ)

lookup : Env Γ → τ ∈ Γ → Val τ
lookup (v ∷ ρ) here      = v
lookup (v ∷ ρ) (there x) = lookup ρ x

FEnv : Sig → Set
FEnv Σ = ∀ {a b} → (a , b) ∈ Σ → Val a → Val b

go : ℕ → ℕ → Val τ → (ℕ → Val τ → Val τ) → Val τ
go i zero    acc s = acc
go i (suc r) acc s = go (suc i) r (s i acc) s

caseV : Val (a ⊕ b) → (Val a → Val τ) → (Val b → Val τ) → Val τ
caseV (inj₁ x) f g = f x
caseV (inj₂ y) f g = g y

⟦_⟧ : Expr Σ Γ τ → FEnv Σ → Env Γ → Val τ
⟦ lit _ v ⟧      F ρ = v
⟦ var x ⟧        F ρ = lookup ρ x
⟦ op1 o e ⟧      F ρ = ev1 o (⟦ e ⟧ F ρ)
⟦ op2 o e₁ e₂ ⟧  F ρ = ev2 o (⟦ e₁ ⟧ F ρ) (⟦ e₂ ⟧ F ρ)
⟦ ite c e₁ e₂ ⟧  F ρ = if ⟦ c ⟧ F ρ then ⟦ e₁ ⟧ F ρ else ⟦ e₂ ⟧ F ρ
⟦ let′ e b ⟧     F ρ = ⟦ b ⟧ F (⟦ e ⟧ F ρ ∷ ρ)
⟦ pair e₁ e₂ ⟧   F ρ = ⟦ e₁ ⟧ F ρ , ⟦ e₂ ⟧ F ρ
⟦ fst e ⟧        F ρ = proj₁ (⟦ e ⟧ F ρ)
⟦ snd e ⟧        F ρ = proj₂ (⟦ e ⟧ F ρ)
⟦ inl e ⟧        F ρ = inj₁ (⟦ e ⟧ F ρ)
⟦ inr e ⟧        F ρ = inj₂ (⟦ e ⟧ F ρ)
⟦ case e l r ⟧   F ρ = caseV (⟦ e ⟧ F ρ) (λ x → ⟦ l ⟧ F (x ∷ ρ)) (λ y → ⟦ r ⟧ F (y ∷ ρ))
⟦ iter n z s ⟧   F ρ = go 0 (⟦ n ⟧ F ρ) (⟦ z ⟧ F ρ) (λ i acc → ⟦ s ⟧ F (acc ∷ i ∷ ρ))
⟦ call f e ⟧     F ρ = F f (⟦ e ⟧ F ρ)

-- Programs: a telescope of first-order, non-recursive unary functions.
-- Each body may call only earlier definitions; the head is `main`.
infixl 4 _▷_
data Prog : Sig → Set where
  []  : Prog []
  _▷_ : Prog Σ → Expr Σ (a ∷ []) b → Prog ((a , b) ∷ Σ)

⟦_⟧p : Prog Σ → FEnv Σ
⟦ P ▷ body ⟧p here      v = ⟦ body ⟧ ⟦ P ⟧p (v ∷ [])
⟦ P ▷ body ⟧p (there m) v = ⟦ P ⟧p m v

runMain : Prog ((a , b) ∷ Σ) → Val a → Val b
runMain P = ⟦ P ⟧p here

------------------------------------------------------------------------
-- Congruence lemmas (pointwise; no function extensionality is used).

go-cong : ∀ {τ} i r (acc : Val τ) {s s′ : ℕ → Val τ → Val τ}
        → (∀ j x → s j x ≡ s′ j x) → go i r acc s ≡ go i r acc s′
go-cong i zero    acc h = refl
go-cong i (suc r) acc {s} {s′} h rewrite h i acc = go-cong (suc i) r (s′ i acc) h

caseV-cong : ∀ (v : Val (a ⊕ b)) {f f′ : Val a → Val τ} {g g′ : Val b → Val τ}
           → (∀ x → f x ≡ f′ x) → (∀ y → g y ≡ g′ y) → caseV v f g ≡ caseV v f′ g′
caseV-cong (inj₁ x) hf hg = hf x
caseV-cong (inj₂ y) hf hg = hg y

FEq : FEnv Σ → FEnv Σ → Set
FEq F G = ∀ {a b} (m : (a , b) ∈ _) v → F m v ≡ G m v

congF : ∀ {F G : FEnv Σ} → FEq F G → (e : Expr Σ Γ τ) (ρ : Env Γ) → ⟦ e ⟧ F ρ ≡ ⟦ e ⟧ G ρ
congF h (lit _ v) ρ     = refl
congF h (var x) ρ       = refl
congF h (op1 o e) ρ     = cong (ev1 o) (congF h e ρ)
congF h (op2 o e₁ e₂) ρ = cong₂ (ev2 o) (congF h e₁ ρ) (congF h e₂ ρ)
congF {F = F} {G} h (ite c e₁ e₂) ρ
  rewrite congF h c ρ | congF h e₁ ρ | congF h e₂ ρ = refl
congF {F = F} {G} h (let′ e b) ρ
  rewrite congF h e ρ = congF h b (⟦ e ⟧ G ρ ∷ ρ)
congF h (pair e₁ e₂) ρ  = cong₂ _,_ (congF h e₁ ρ) (congF h e₂ ρ)
congF h (fst e) ρ       = cong proj₁ (congF h e ρ)
congF h (snd e) ρ       = cong proj₂ (congF h e ρ)
congF h (inl e) ρ       = cong inj₁ (congF h e ρ)
congF h (inr e) ρ       = cong inj₂ (congF h e ρ)
congF {F = F} {G} h (case e l r) ρ rewrite congF h e ρ =
  caseV-cong (⟦ e ⟧ G ρ) (λ x → congF h l (x ∷ ρ)) (λ y → congF h r (y ∷ ρ))
congF {F = F} {G} h (iter n z s) ρ rewrite congF h n ρ | congF h z ρ =
  go-cong 0 (⟦ n ⟧ G ρ) (⟦ z ⟧ G ρ) (λ i acc → congF h s (acc ∷ i ∷ ρ))
congF {F = F} {G} h (call f e) ρ rewrite congF h e ρ = h f (⟦ e ⟧ G ρ)
