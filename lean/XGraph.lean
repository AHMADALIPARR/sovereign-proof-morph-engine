-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Discrete model of the twin X-graph sweep (bqn/checked). Zero sorry, zero
-- user axioms. States are (token, phase); the step is deterministic and the
-- state space finite, so every trace is eventually periodic, every period of
-- the phase component is a multiple of 2462, two traces that meet once stay
-- merged, and the midpoint of two distinct rows is an exact snap tie.
import Mathlib.Tactic

namespace XGraph

/-- (1) Eventual periodicity of any self-map of a finite type. -/
theorem eventually_periodic {S : Type} [Fintype S] (f : S → S) (x : S) :
    ∃ μ per, 0 < per ∧ f^[μ + per] x = f^[μ] x := by
  have hcard : Fintype.card S < Fintype.card (Fin (Fintype.card S + 1)) := by simp
  obtain ⟨i, j, hne, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card S + 1) => f^[k.val] x) hcard
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hij | hij
  · exact ⟨i.val, j.val - i.val, by omega, by rw [Nat.add_sub_cancel' hij.le]; exact h.symm⟩
  · exact ⟨j.val, i.val - j.val, by omega, by rw [Nat.add_sub_cancel' hij.le]; exact h⟩

/-- The (token, phase) step: the token update reads the phase, the phase
    advances by 89 on Z_2462. -/
def step {V : ℕ} (K : Fin V → Fin 2462 → Fin V) (s : Fin V × Fin 2462) :
    Fin V × Fin 2462 :=
  (K s.1 s.2, ⟨(s.2.val + 89) % 2462, Nat.mod_lt _ (by norm_num)⟩)

theorem step_iter_phase {V : ℕ} (K : Fin V → Fin 2462 → Fin V) (s : Fin V × Fin 2462) (n : ℕ) :
    ((step K)^[n] s).2.val = (s.2.val + 89 * n) % 2462 := by
  induction n generalizing s with
  | zero => simp [Nat.mod_eq_of_lt s.2.isLt]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [step]
    omega

/-- (2) Every period of the (token, phase) system is a multiple of 2462. -/
theorem period_multiple {V : ℕ} (K : Fin V → Fin 2462 → Fin V) (s : Fin V × Fin 2462)
    (μ per : ℕ) (h : (step K)^[μ + per] s = (step K)^[μ] s) : 2462 ∣ per := by
  have h2 := congrArg (fun x => x.2.val) h
  simp only [step_iter_phase] at h2
  have h3 : 2462 ∣ 89 * per := by omega
  exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 2462 89) h3

/-- A time-indexed trace: run step init 0 = init, then step n. -/
def run {E : Type} (stepN : ℕ → E → E) (init : E) : ℕ → E
  | 0 => init
  | n + 1 => stepN n (run stepN init n)

/-- (3) Merge: two traces from different initial states that agree at step k
    agree at every later step. -/
theorem merge {E : Type} (stepN : ℕ → E → E) (a b : E) (k : ℕ)
    (h : run stepN a k = run stepN b k) : ∀ n, k ≤ n → run stepN a n = run stepN b n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => simp [run, ih]

/-- (4) The midpoint of two embeddings is exactly equidistant from both, so
    the snap of a midpoint between distinct rows is decided by tie-breaking. -/
theorem midpoint_tie {D : ℕ} (a b : Fin D → ℝ) :
    (∑ k, ((a k + b k) / 2 - a k) ^ 2) = (∑ k, ((a k + b k) / 2 - b k) ^ 2) := by
  apply Finset.sum_congr rfl
  intro k _
  ring

end XGraph

#print axioms XGraph.eventually_periodic
#print axioms XGraph.period_multiple
#print axioms XGraph.merge
#print axioms XGraph.midpoint_tie
