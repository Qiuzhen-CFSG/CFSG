module

public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Theory.GroupTheory.PResidual.Defs

/-!
# The two marked factors of the binary determinant action

The factors below are the literal images of SL₂(4) × 1 and 1 × SL₂(4)
under the faithful matrix action. Interchange means that conjugation by
the specified binary linear automorphism sends each image to the other.
These definitions impose no normalizer classification or moved-rank claim.

They provide the common interface for the factor-preserving and swapping
involution calculations used in Aschbacher–Smith 14.4.9, printed p.1010.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual
open Subgroup

abbrev SL := Matrix.SpecialLinearGroup (Fin 2) F

/-- The actual first special linear factor in GL₈(2). -/
def leftFactor : Subgroup (V ≃ₗ[ZMod 2] V) :=
  (linearAction.comp (MonoidHom.inl SL SL)).range

/-- The actual second special linear factor in GL₈(2). -/
def rightFactor : Subgroup (V ≃ₗ[ZMod 2] V) :=
  (linearAction.comp (MonoidHom.inr SL SL)).range

/-- Interchange of the two marked factors by the specified operator. -/
def SwapsFactors (t : V ≃ₗ[ZMod 2] V) : Prop :=
  leftFactor.map (MulAut.conj t).toMonoidHom = rightFactor ∧
    rightFactor.map (MulAut.conj t).toMonoidHom = leftFactor

theorem leftFactor_le : leftFactor ≤ linearAction.range := by
  rintro _ ⟨g,rfl⟩
  exact ⟨(g,1),rfl⟩

theorem rightFactor_le : rightFactor ≤ linearAction.range := by
  rintro _ ⟨g,rfl⟩
  exact ⟨(1,g),rfl⟩

/-- The two marked factors generate the original matrix action image. -/
theorem factors_sup : leftFactor ⊔ rightFactor = linearAction.range := by
  apply le_antisymm (sup_le leftFactor_le rightFactor_le)
  rintro _ ⟨⟨g,h⟩,rfl⟩
  have he : (g,h) = (g,1) * (1,h) := by simp
  rw [he,map_mul]
  exact (leftFactor ⊔ rightFactor).mul_mem
    (mem_sup_left ⟨g,rfl⟩) (mem_sup_right ⟨h,rfl⟩)

end ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual
