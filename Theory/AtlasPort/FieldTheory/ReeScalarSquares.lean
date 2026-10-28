module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Sources: Atlas/FieldTheory/ReeScalarSquares.lean and
Atlas/LinearGroups/Symplectic/PerfectLarge.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.FieldTheory.ReeTitsAutomorphism
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
set_option warningAsError false

/-!
Scalar facts used to generate the Ree group by commutators. A field with more
than three elements has a scalar outside `{0, 1, -1}`. For the Ree field sizes,
which are three modulo four, the quadratic character shows that every unit is
a square or the negative of a square. These arguments use only finite-field
arithmetic, independently of symplectic group generation.
-/

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

omit [CharP F 3] in
/-- A nonexceptional field contains a nonzero scalar whose square is not one. -/
theorem exists_scalar_square_ne_one (hq : 3 < Nat.card F) :
    ∃ c : F, c ≠ 0 ∧ c^2 ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  have hcard : ({0,1,-1} : Finset F).card < (Finset.univ : Finset F).card := by
    have h := Finset.card_le_three (a := (0 : F)) (b := 1) (c := -1)
    simpa only [Finset.card_univ,← Nat.card_eq_fintype_card] using lt_of_le_of_lt h hq
  obtain ⟨c,_,hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hc
  exact ⟨c,hc.1,fun h => (sq_eq_one_iff.mp h).elim hc.2.1 hc.2.2⟩

theorem scalar_square_or_negative_square (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (a : F) :
    IsSquare a ∨ IsSquare (-a) := by
  classical
  letI := Fintype.ofFinite F
  have hn : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hcard]
    norm_num [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
  by_cases ha : IsSquare a
  · exact Or.inl ha
  right
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0,by simp⟩
  apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr ha0)).mp
  rw [show -a = (-1)*a by ring,map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr hn,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha]
  norm_num

theorem unit_eq_square_or_negative_square (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (l : Fˣ) :
    (∃ k : Fˣ, l = k^2) ∨ (∃ k : Fˣ, l = -(k^2)) := by
  rcases scalar_square_or_negative_square m hcard (l : F) with ⟨x,hx⟩ | ⟨x,hx⟩
  · left
    have hn : x ≠ 0 := by intro h; apply Units.ne_zero l; simpa [h] using hx
    refine ⟨Units.mk0 x hn, Units.ext ?_⟩
    simpa [pow_two] using hx
  · right
    have hn : x ≠ 0 := by
      intro h
      have hz : -(l : F) = 0 := by simpa [h] using hx
      exact Units.ne_zero l (neg_eq_zero.mp hz)
    refine ⟨Units.mk0 x hn, Units.ext ?_⟩
    simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mk0, pow_two, Units.val_mul]
    linear_combination -hx

end Atlas.ReeG2
