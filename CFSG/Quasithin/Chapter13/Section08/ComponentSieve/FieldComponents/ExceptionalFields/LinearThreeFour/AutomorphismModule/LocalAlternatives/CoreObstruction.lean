module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.BorelTransport

/-!
# A retained two-element in the graph-field Borel centralizer

Coordinate reversal followed by inverse transpose and any coefficient
field automorphism fixes the binary highest-root matrix I + E₁₃. This
matrix belongs to the Borel but is not scalar. Consequently the full
Borel centralizer cannot be replaced by the scalar center. This model
calculation diagnoses the literal centralizer equality on printed p.955;
it does not refute the full standing configuration, which is itself
being excluded. A sufficient route must use two-perfect source factors
or the two-residual of the relevant fixed subgroup.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
open Subgroup Representation.SL3FourNaturalDual Matrix
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions

private theorem root_mem_borel : root 1 ∈ borelSL F := by
  rw [mem_borelSL_iff]
  simp [root]

private theorem root_not_central : root 1 ∉ center SL := by
  intro h
  obtain ⟨r, hr, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have hx := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 2) he
  simp [root, Matrix.scalar_apply, Matrix.diagonal_apply_ne] at hx

private theorem opposition_field_fixes_root (σ : F ≃+* F) :
    (linearConjSL F (reversalGL F) * Atlas.fieldEquivSL 3 σ * graphSL F) (root 1) = root 1 := by
  have hg : graphSL F (root 1) = SpecialLinearGroup.transpose (root 1) := by
    have he : graphSL F (root 1) = SpecialLinearGroup.inverseTranspose (root 1) := by
      apply Subtype.ext
      exact (Matrix.adjugate_transpose (root 1).val).symm
    rw [he]
    change (root 1)⁻¹.transpose = _
    rw [root_inv]
  rw [MulAut.mul_apply, MulAut.mul_apply, hg]
  have hf : Atlas.fieldEquivSL 3 σ (SpecialLinearGroup.transpose (root 1)) =
      SpecialLinearGroup.transpose (root 1) := by
    apply Subtype.ext
    funext i j
    change σ ((root 1).val j i) = (root 1).val j i
    fin_cases i <;> fin_cases j <;> simp [root]
  rw [hf]
  apply Subtype.ext
  funext i j
  rw [reversal_conj_val]
  change (root 1).val j.rev i.rev = (root 1).val i j
  fin_cases i <;> fin_cases j <;> simp [root]

/-- The full graph-field fixed subgroup of the Borel retains a noncentral two-element. -/
theorem opposition_field_fixed_borel_ne_center (σ : F ≃+* F) :
    borelSL F ⊓
      (linearConjSL F (reversalGL F) * Atlas.fieldEquivSL 3 σ * graphSL F).fixedSubgroup ≠
        center SL := by
  intro he
  apply root_not_central
  rw [← he]
  exact ⟨root_mem_borel, (MulAut.mem_fixedSubgroup _ _).mpr (opposition_field_fixes_root σ)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
