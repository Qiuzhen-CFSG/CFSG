/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeZeroFibers

/-!
# DodecadMaskKernel

The polar mask map for a nonzero hexacode word has kernel consisting of zero and that
word. The four-letter polar calculation and the minimum-weight constraint determine the
kernel coordinate by coordinate.

Source: `Atlas/Codes/DodecadMaskKernel.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

/-- The actual polar mask change, on the nonzero positions of the fixed word. -/
def dodecadMaskMap (i : HexIndex) (h : hexZeroCoordinate i) :
    hexZeroCoordinate i →ₗ[Bit] ({k : HexIndex // h.val.val k ≠ 0} → Bit) where
  toFun t k := polar (h.val.val k) (t.val.val k)
  map_add' t u := by funext k; exact map_add (polar (h.val.val k)) _ _
  map_smul' r t := by funext k; exact map_smul (polar (h.val.val k)) r _

theorem polar_zero_letter : ∀ x y : K, x ≠ 0 →
    (polar x y = 0 ↔ y = 0 ∨ y = x) := by decide

theorem hexZero_self_add (i : HexIndex) (h : hexZeroCoordinate i) : h + h = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact Prod.ext (bit_self_add _) (bit_self_add _)

theorem dodecadMaskMap_kernel (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0)
    (t : hexZeroCoordinate i) : dodecadMaskMap i h t = 0 ↔ t = 0 ∨ t = h := by
  classical
  constructor
  · intro ht
    by_contra hn
    push Not at hn
    have hth : t + h ≠ 0 := by
      intro he
      apply hn.2
      exact add_right_cancel (he.trans (hexZero_self_add i h).symm)
    have wt := hexZeroCoordinate_nonzero_weight i t hn.1
    have wth := hexZeroCoordinate_nonzero_weight i (t + h) hth
    obtain ⟨j, ⟨hji, hj⟩, hjuniq⟩ := hexZeroCoordinate_unique_other_zero i h hh
    have bound (k : HexIndex) :
        (if t.val.val k = 0 then 0 else 1 : ℕ) +
        (if t.val.val k + h.val.val k = 0 then 0 else 1 : ℕ) ≤
        if k = i then 0 else if k = j then 2 else 1 := by
      by_cases hki : k = i
      · subst k
        have ti : t.val.val i = 0 := t.prop
        have hi : h.val.val i = 0 := h.prop
        simp [ti, hi]
      by_cases hkj : k = j
      · subst k
        simp only [hji, hj, add_zero, ite_false, ite_true]
        split_ifs <;> omega
      have hk : h.val.val k ≠ 0 := by
        intro hz
        exact hkj (hjuniq k ⟨hki, hz⟩)
      have hp : polar (h.val.val k) (t.val.val k) = 0 := congrFun ht ⟨k, hk⟩
      rcases (polar_zero_letter _ _ hk).mp hp with hz | hz
      · simp [hz, hk, hki, hkj]
      · have hs : h.val.val k + h.val.val k = 0 := Prod.ext (bit_self_add _) (bit_self_add _)
        simp [hz, hs, hk, hki, hkj]
    have hb := Finset.sum_le_sum (s := Finset.univ) (fun k _ => bound k)
    have total : (∑ k : HexIndex, if k = i then 0 else if k = j then 2 else 1 : ℕ) = 6 := by
      have he : ∀ k : HexIndex,
          (if k = i then 0 else if k = j then 2 else 1 : ℕ) + (if k = i then 1 else 0) =
          1 + (if k = j then 1 else 0) := by
        intro k
        by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
      have hs := congrArg (fun f : HexIndex → ℕ => ∑ k, f k) (funext he)
      simp only [Finset.sum_add_distrib] at hs
      norm_num [HexIndex] at hs
      omega
    rw [total, Finset.sum_add_distrib, ← hammingNorm_eq_sum, ← hammingNorm_eq_sum] at hb
    change hammingNorm t.val.val + hammingNorm (t + h).val.val ≤ 6 at hb
    omega
  · rintro (rfl | rfl)
    · exact map_zero _
    · funext k
      change polar (t.val.val k) (t.val.val k) = 0
      have he : ∀ x : K, polar x x = 0 := by decide
      exact he _

end Atlas.Codes
