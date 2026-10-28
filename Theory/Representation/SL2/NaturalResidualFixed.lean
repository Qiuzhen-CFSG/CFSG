module
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.Representation.QuadraticFourGroup.TensorClassification.NaturalAction
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Fixed vectors of a two-residual on a natural plane

A surjection to SL₂ in characteristic two maps the actual two-residual
onto the model two-residual. The latter contains an explicit element of
order three, which fixes no nonzero natural vector. Thus a natural quotient
has no residual-fixed vectors, including over the field of order two.

This identifies the denominator used in DGS, Groups and Graphs (1985),
(8.5) and the central-intersection argument in (12.3), printed pp.139,180.
The literal source application is CommutingThreeProfile.LinearResidualLayer.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SL2
open Representation.QuadraticFourGroup.TensorClassification
variable {H F : Type*} [Group H] [Finite H] [Field F] [CharP F 2]

/-- A vector fixed by the original two-residual is zero under a surjective natural action. -/
theorem natural_residual_fixed_eq_zero (q : H →* SL(2,F))
    (hq : Function.Surjective q) (v : Fin 2 → F)
    (hv : ∀ a ∈ pResidual 2 H, Matrix.mulVec (q a).val v = v) : v = 0 := by
  have hc : cubicMatrix F ∈ pResidual 2 SL(2,F) :=
    mem_pResidual_of_orderOf_coprime (by rw [cubicMatrix_order]; decide)
  rw [← map_pResidual_of_surjective 2 q hq] at hc
  obtain ⟨a,ha,he⟩ := hc
  apply cubic_fixed_eq_zero (cubicMatrix F) (cubicMatrix_order F)
  rw [← he]
  exact hv a ha
end Matrix.SL2
