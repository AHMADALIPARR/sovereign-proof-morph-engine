-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Checked replacement for SnapUnique.lean (kept unmodified). Zero sorry and
-- zero user axioms. The snap is defined as the lowest-index minimizer (what
-- BQN `⊑⍋` returns, since grade is stable), which is always exactly one token.
-- Strict uniqueness of the minimizer holds only under an explicit injectivity
-- hypothesis, and the midpoint lemma shows exact ties occur by construction.
import Mathlib.Tactic

namespace SnapUnique_Checked

open Classical

abbrev TokenSpace (N : ℕ) := Fin N

variable {N : ℕ} [NeZero N]

/-- (a) A minimizer exists over a nonempty finite vocabulary. -/
theorem exists_min_dist (sq_dist : TokenSpace N → ℝ) :
    ∃ min_tok : TokenSpace N, ∀ tok, sq_dist min_tok ≤ sq_dist tok := by
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ sq_dist Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- The set of minimizers. -/
noncomputable def minimizers (sq_dist : TokenSpace N → ℝ) : Finset (TokenSpace N) :=
  Finset.univ.filter (fun i => ∀ j, sq_dist i ≤ sq_dist j)

theorem minimizers_nonempty (sq_dist : TokenSpace N → ℝ) : (minimizers sq_dist).Nonempty := by
  obtain ⟨i, hi⟩ := exists_min_dist sq_dist
  exact ⟨i, by simp [minimizers, hi]⟩

/-- (b) The snap: the lowest-index minimizer. -/
noncomputable def snap (sq_dist : TokenSpace N → ℝ) : TokenSpace N :=
  (minimizers sq_dist).min' (minimizers_nonempty sq_dist)

theorem snap_is_min (sq_dist : TokenSpace N → ℝ) : ∀ tok, sq_dist (snap sq_dist) ≤ sq_dist tok := by
  have h := Finset.min'_mem (minimizers sq_dist) (minimizers_nonempty sq_dist)
  simp only [minimizers, Finset.mem_filter] at h
  exact h.2

theorem snap_lowest (sq_dist : TokenSpace N → ℝ) (i : TokenSpace N)
    (hi : ∀ tok, sq_dist i ≤ sq_dist tok) : snap sq_dist ≤ i :=
  Finset.min'_le _ _ (by simp [minimizers, hi])

/-- (b) snap is the unique minimizer that is ≤ every other minimizer. -/
theorem snap_unique (sq_dist : TokenSpace N → ℝ) :
    ∃! s : TokenSpace N, (∀ tok, sq_dist s ≤ sq_dist tok) ∧
      (∀ i, (∀ tok, sq_dist i ≤ sq_dist tok) → s ≤ i) := by
  refine ⟨snap sq_dist, ⟨snap_is_min sq_dist, snap_lowest sq_dist⟩, ?_⟩
  rintro s ⟨hs_min, hs_low⟩
  exact le_antisymm (hs_low _ (snap_is_min sq_dist)) (snap_lowest sq_dist s hs_min)

/-- (c) Strict uniqueness, only under an explicit injectivity hypothesis. -/
theorem snap_kernel_unique (sq_dist : TokenSpace N → ℝ) (h : Function.Injective sq_dist) :
    ∃! snap_tok : TokenSpace N, ∀ tok, tok ≠ snap_tok → sq_dist snap_tok < sq_dist tok := by
  obtain ⟨m, hm⟩ := exists_min_dist sq_dist
  refine ⟨m, fun tok hne => lt_of_le_of_ne (hm tok) (fun heq => hne (h heq).symm), ?_⟩
  intro y hy
  by_contra hne
  have := hy m (Ne.symm hne)
  linarith [hm y]

/-- (d) The midpoint of two embeddings is exactly equidistant from both. -/
theorem midpoint_tie {D : ℕ} (a b : Fin D → ℝ) :
    (∑ k, ((a k + b k) / 2 - a k) ^ 2) = (∑ k, ((a k + b k) / 2 - b k) ^ 2) := by
  apply Finset.sum_congr rfl
  intro k _
  ring

end SnapUnique_Checked

#print axioms SnapUnique_Checked.exists_min_dist
#print axioms SnapUnique_Checked.snap_unique
#print axioms SnapUnique_Checked.snap_kernel_unique
#print axioms SnapUnique_Checked.midpoint_tie
