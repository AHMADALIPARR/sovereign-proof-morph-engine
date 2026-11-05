-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Renaming, substitution and signature renaming, each with a semantic
-- soundness lemma stated against pointwise environment relations.
{-# OPTIONS --safe --without-K #-}
module Morph.Subst where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)
open import Morph.IR

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {τ} → τ ∈ Γ → τ ∈ Δ

ext : Ren Γ Δ → Ren (σ ∷ Γ) (σ ∷ Δ)
ext r here      = here
ext r (there x) = there (r x)

rename : Ren Γ Δ → Expr Σ Γ τ → Expr Σ Δ τ
rename r (lit t v)     = lit t v
rename r (var x)       = var (r x)
rename r (op1 o e)     = op1 o (rename r e)
rename r (op2 o e₁ e₂) = op2 o (rename r e₁) (rename r e₂)
rename r (ite c e₁ e₂) = ite (rename r c) (rename r e₁) (rename r e₂)
rename r (let′ e b)    = let′ (rename r e) (rename (ext r) b)
rename r (pair e₁ e₂)  = pair (rename r e₁) (rename r e₂)
rename r (fst e)       = fst (rename r e)
rename r (snd e)       = snd (rename r e)
rename r (inl e)       = inl (rename r e)
rename r (inr e)       = inr (rename r e)
rename r (case e l k)  = case (rename r e) (rename (ext r) l) (rename (ext r) k)
rename r (iter n z s)  = iter (rename r n) (rename r z) (rename (ext (ext r)) s)
rename r (call f e)    = call f (rename r e)

RenOK : Ren Γ Δ → Env Γ → Env Δ → Set
RenOK {Γ} r γ δ = ∀ {τ} (x : τ ∈ Γ) → lookup δ (r x) ≡ lookup γ x

ext-ok : ∀ {r : Ren Γ Δ} {γ δ} → RenOK r γ δ → (v : Val σ) → RenOK (ext r) (v ∷ γ) (v ∷ δ)
ext-ok h v here      = refl
ext-ok h v (there x) = h x

rename-sound : ∀ (r : Ren Γ Δ) (e : Expr Σ Γ τ) (F : FEnv Σ) γ δ → RenOK r γ δ
             → ⟦ rename r e ⟧ F δ ≡ ⟦ e ⟧ F γ
rename-sound r (lit t v) F γ δ h     = refl
rename-sound r (var x) F γ δ h       = h x
rename-sound r (op1 o e) F γ δ h     = cong (ev1 o) (rename-sound r e F γ δ h)
rename-sound r (op2 o e₁ e₂) F γ δ h =
  cong₂ (ev2 o) (rename-sound r e₁ F γ δ h) (rename-sound r e₂ F γ δ h)
rename-sound r (ite c e₁ e₂) F γ δ h
  rewrite rename-sound r c F γ δ h | rename-sound r e₁ F γ δ h
        | rename-sound r e₂ F γ δ h = refl
rename-sound r (let′ e b) F γ δ h rewrite rename-sound r e F γ δ h =
  rename-sound (ext r) b F _ _ (ext-ok h (⟦ e ⟧ F γ))
rename-sound r (pair e₁ e₂) F γ δ h =
  cong₂ _,_ (rename-sound r e₁ F γ δ h) (rename-sound r e₂ F γ δ h)
rename-sound r (fst e) F γ δ h = cong proj₁ (rename-sound r e F γ δ h)
rename-sound r (snd e) F γ δ h = cong proj₂ (rename-sound r e F γ δ h)
rename-sound r (inl e) F γ δ h = cong inj₁ (rename-sound r e F γ δ h)
rename-sound r (inr e) F γ δ h = cong inj₂ (rename-sound r e F γ δ h)
rename-sound r (case e l k) F γ δ h rewrite rename-sound r e F γ δ h =
  caseV-cong (⟦ e ⟧ F γ) (λ x → rename-sound (ext r) l F _ _ (ext-ok h x))
                         (λ y → rename-sound (ext r) k F _ _ (ext-ok h y))
rename-sound r (iter n z s) F γ δ h
  rewrite rename-sound r n F γ δ h | rename-sound r z F γ δ h =
  go-cong 0 (⟦ n ⟧ F γ) (⟦ z ⟧ F γ)
    (λ i acc → rename-sound (ext (ext r)) s F _ _ (ext-ok (ext-ok h i) acc))
rename-sound r (call f e) F γ δ h = cong (F f) (rename-sound r e F γ δ h)

------------------------------------------------------------------------
Sub : Sig → Ctx → Ctx → Set
Sub Σ Γ Δ = ∀ {τ} → τ ∈ Γ → Expr Σ Δ τ

exts : Sub Σ Γ Δ → Sub Σ (σ ∷ Γ) (σ ∷ Δ)
exts s here      = var here
exts s (there x) = rename there (s x)

subst : Sub Σ Γ Δ → Expr Σ Γ τ → Expr Σ Δ τ
subst s (lit t v)     = lit t v
subst s (var x)       = s x
subst s (op1 o e)     = op1 o (subst s e)
subst s (op2 o e₁ e₂) = op2 o (subst s e₁) (subst s e₂)
subst s (ite c e₁ e₂) = ite (subst s c) (subst s e₁) (subst s e₂)
subst s (let′ e b)    = let′ (subst s e) (subst (exts s) b)
subst s (pair e₁ e₂)  = pair (subst s e₁) (subst s e₂)
subst s (fst e)       = fst (subst s e)
subst s (snd e)       = snd (subst s e)
subst s (inl e)       = inl (subst s e)
subst s (inr e)       = inr (subst s e)
subst s (case e l k)  = case (subst s e) (subst (exts s) l) (subst (exts s) k)
subst s (iter n z t)  = iter (subst s n) (subst s z) (subst (exts (exts s)) t)
subst s (call f e)    = call f (subst s e)

SubOK : Sub Σ Γ Δ → FEnv Σ → Env Γ → Env Δ → Set
SubOK {Γ = Γ} s F γ δ = ∀ {τ} (x : τ ∈ Γ) → ⟦ s x ⟧ F δ ≡ lookup γ x

exts-ok : ∀ {s : Sub Σ Γ Δ} {F : FEnv Σ} {γ δ} → SubOK s F γ δ → (v : Val σ)
        → SubOK (exts s) F (v ∷ γ) (v ∷ δ)
exts-ok h v here = refl
exts-ok {s = s} {F} {γ} {δ} h v (there x) =
  trans (rename-sound there (s x) F δ (v ∷ δ) (λ y → refl)) (h x)

subst-sound : ∀ (s : Sub Σ Γ Δ) (e : Expr Σ Γ τ) (F : FEnv Σ) γ δ → SubOK s F γ δ
            → ⟦ subst s e ⟧ F δ ≡ ⟦ e ⟧ F γ
subst-sound s (lit t v) F γ δ h     = refl
subst-sound s (var x) F γ δ h       = h x
subst-sound s (op1 o e) F γ δ h     = cong (ev1 o) (subst-sound s e F γ δ h)
subst-sound s (op2 o e₁ e₂) F γ δ h =
  cong₂ (ev2 o) (subst-sound s e₁ F γ δ h) (subst-sound s e₂ F γ δ h)
subst-sound s (ite c e₁ e₂) F γ δ h
  rewrite subst-sound s c F γ δ h | subst-sound s e₁ F γ δ h
        | subst-sound s e₂ F γ δ h = refl
subst-sound s (let′ e b) F γ δ h rewrite subst-sound s e F γ δ h =
  subst-sound (exts s) b F _ _ (exts-ok h (⟦ e ⟧ F γ))
subst-sound s (pair e₁ e₂) F γ δ h =
  cong₂ _,_ (subst-sound s e₁ F γ δ h) (subst-sound s e₂ F γ δ h)
subst-sound s (fst e) F γ δ h = cong proj₁ (subst-sound s e F γ δ h)
subst-sound s (snd e) F γ δ h = cong proj₂ (subst-sound s e F γ δ h)
subst-sound s (inl e) F γ δ h = cong inj₁ (subst-sound s e F γ δ h)
subst-sound s (inr e) F γ δ h = cong inj₂ (subst-sound s e F γ δ h)
subst-sound s (case e l k) F γ δ h rewrite subst-sound s e F γ δ h =
  caseV-cong (⟦ e ⟧ F γ) (λ x → subst-sound (exts s) l F _ _ (exts-ok h x))
                         (λ y → subst-sound (exts s) k F _ _ (exts-ok h y))
subst-sound s (iter n z t) F γ δ h
  rewrite subst-sound s n F γ δ h | subst-sound s z F γ δ h =
  go-cong 0 (⟦ n ⟧ F γ) (⟦ z ⟧ F γ)
    (λ i acc → subst-sound (exts (exts s)) t F _ _ (exts-ok (exts-ok h i) acc))
subst-sound s (call f e) F γ δ h = cong (F f) (subst-sound s e F γ δ h)

-- Single substitution  b[e/0].
sub1 : Expr Σ Γ σ → Sub Σ (σ ∷ Γ) Γ
sub1 e here      = e
sub1 e (there x) = var x

sub1-sound : ∀ (e : Expr Σ Γ σ) (b : Expr Σ (σ ∷ Γ) τ) (F : FEnv Σ) ρ
           → ⟦ subst (sub1 e) b ⟧ F ρ ≡ ⟦ b ⟧ F (⟦ e ⟧ F ρ ∷ ρ)
sub1-sound e b F ρ = subst-sound (sub1 e) b F (⟦ e ⟧ F ρ ∷ ρ) ρ ok
  where
  ok : SubOK (sub1 e) F (⟦ e ⟧ F ρ ∷ ρ) ρ
  ok here      = refl
  ok (there x) = refl

------------------------------------------------------------------------
-- Signature renaming (used by function specialization).
SRen : Sig → Sig → Set
SRen Σ Σ' = ∀ {a b} → (a , b) ∈ Σ → (a , b) ∈ Σ'

srename : SRen Σ Σ' → Expr Σ Γ τ → Expr Σ' Γ τ
srename r (lit t v)     = lit t v
srename r (var x)       = var x
srename r (op1 o e)     = op1 o (srename r e)
srename r (op2 o e₁ e₂) = op2 o (srename r e₁) (srename r e₂)
srename r (ite c e₁ e₂) = ite (srename r c) (srename r e₁) (srename r e₂)
srename r (let′ e b)    = let′ (srename r e) (srename r b)
srename r (pair e₁ e₂)  = pair (srename r e₁) (srename r e₂)
srename r (fst e)       = fst (srename r e)
srename r (snd e)       = snd (srename r e)
srename r (inl e)       = inl (srename r e)
srename r (inr e)       = inr (srename r e)
srename r (case e l k)  = case (srename r e) (srename r l) (srename r k)
srename r (iter n z s)  = iter (srename r n) (srename r z) (srename r s)
srename r (call f e)    = call (r f) (srename r e)

srename-sound : ∀ (r : SRen Σ Σ') (e : Expr Σ Γ τ) (F : FEnv Σ) (G : FEnv Σ') ρ
              → (∀ {a b} (m : (a , b) ∈ Σ) v → G (r m) v ≡ F m v)
              → ⟦ srename r e ⟧ G ρ ≡ ⟦ e ⟧ F ρ
srename-sound r (lit t v) F G ρ h     = refl
srename-sound r (var x) F G ρ h       = refl
srename-sound r (op1 o e) F G ρ h     = cong (ev1 o) (srename-sound r e F G ρ h)
srename-sound r (op2 o e₁ e₂) F G ρ h =
  cong₂ (ev2 o) (srename-sound r e₁ F G ρ h) (srename-sound r e₂ F G ρ h)
srename-sound r (ite c e₁ e₂) F G ρ h
  rewrite srename-sound r c F G ρ h | srename-sound r e₁ F G ρ h
        | srename-sound r e₂ F G ρ h = refl
srename-sound r (let′ e b) F G ρ h rewrite srename-sound r e F G ρ h =
  srename-sound r b F G _ h
srename-sound r (pair e₁ e₂) F G ρ h =
  cong₂ _,_ (srename-sound r e₁ F G ρ h) (srename-sound r e₂ F G ρ h)
srename-sound r (fst e) F G ρ h = cong proj₁ (srename-sound r e F G ρ h)
srename-sound r (snd e) F G ρ h = cong proj₂ (srename-sound r e F G ρ h)
srename-sound r (inl e) F G ρ h = cong inj₁ (srename-sound r e F G ρ h)
srename-sound r (inr e) F G ρ h = cong inj₂ (srename-sound r e F G ρ h)
srename-sound r (case e l k) F G ρ h rewrite srename-sound r e F G ρ h =
  caseV-cong (⟦ e ⟧ F ρ) (λ x → srename-sound r l F G _ h)
                         (λ y → srename-sound r k F G _ h)
srename-sound r (iter n z s) F G ρ h
  rewrite srename-sound r n F G ρ h | srename-sound r z F G ρ h =
  go-cong 0 (⟦ n ⟧ F ρ) (⟦ z ⟧ F ρ) (λ i acc → srename-sound r s F G _ h)
srename-sound r (call f e) F G ρ h rewrite srename-sound r e F G ρ h = h f (⟦ e ⟧ F ρ)
