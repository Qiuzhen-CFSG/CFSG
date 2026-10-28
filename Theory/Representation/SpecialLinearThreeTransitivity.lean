module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FinCases

/-!
# Transitivity of the natural SL₃ action

Complete any nonzero first column to a determinant-one matrix. Comparing two
such completions gives transitivity on nonzero vectors over any field, and
hence after restriction to its prime field. This is the elementary natural
module geometry used in the G.9.3(8) exclusion on printed p.1149 of
Aschbacher--Smith.
-/

public section
open Matrix
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {F : Type*} [Field F]

private theorem exists_first_column_three (v : Fin 3 → F) (hv : v ≠ 0) :
    ∃ g : SL(3, F), g • (![1, 0, 0] : Fin 3 → F) = v := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        ext i
        fin_cases i <;> simp_all
      refine ⟨⟨!![0, 0, -(v 2)⁻¹; 0, 1, 0; v 2, 0, 0], ?_⟩, ?_⟩
      · simp [det_fin_three, h2]
      · change (!![0, 0, -(v 2)⁻¹; 0, 1, 0; v 2, 0, 0] *ᵥ ![1, 0, 0]) = v
        ext i
        fin_cases i <;> simp [mulVec, dotProduct,
          Fin.sum_univ_three, h0, h1]
    · refine ⟨⟨!![0, -(v 1)⁻¹, 0; v 1, 0, 0; v 2, 0, 1], ?_⟩, ?_⟩
      · simp [det_fin_three, h1]
      · change (!![0, -(v 1)⁻¹, 0; v 1, 0, 0; v 2, 0, 1] *ᵥ ![1, 0, 0]) = v
        ext i
        fin_cases i <;> simp [mulVec, dotProduct,
          Fin.sum_univ_three, h0]
  · refine ⟨⟨!![v 0, 0, 0; v 1, (v 0)⁻¹, 0; v 2, 0, 1], ?_⟩, ?_⟩
    · simp [det_fin_three, h0]
    · change (!![v 0, 0, 0; v 1, (v 0)⁻¹, 0; v 2, 0, 1] *ᵥ ![1, 0, 0]) = v
      ext i
      fin_cases i <;> simp [mulVec, dotProduct,
        Fin.sum_univ_three]

/-- The actual special linear matrix group sends any nonzero column to any
other, without passing to a projective quotient. -/
theorem exists_mulVec_eq_three (v w : Fin 3 → F) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SL(3, F), g.val *ᵥ v = w := by
  obtain ⟨a, ha⟩ := exists_first_column_three v hv
  obtain ⟨b, hb⟩ := exists_first_column_three w hw
  refine ⟨b * a⁻¹, ?_⟩
  change (b * a⁻¹) • v = w
  rw [← ha, mul_smul, inv_smul_smul, hb]

end Matrix.SpecialLinearGroup
