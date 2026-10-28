module
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.ModelChecked
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.CentralKernel

/-!
# Faithfulness of the literal thirteen-relator HS presentation

The ATLAS centralizer route is completed on the canonical marked surjection.
A checked 5,775-coset cover and two-point separation in the actual degree-100
carrier force kernel elements to centralize the first generator. Normality,
perfectness, the proved multiplier bound and the concrete double-cover square
obstruction then kill the kernel. No abstract finiteness, cardinal bound or
model equivalence is assumed.

The final application supplies the presentation input for the degree-1408
matrix descent, using the existing checked matrix relations.
Source: ATLAS HSG1-P1.M, retained in `../source/` with its attribution.
-/

namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact

private theorem faithful_of_cover {ι : Type*}
    (C : Subgroup.GeneratorCosetCover centralizer generator ι)
    (hsep : ∀ i, Commute (toCarrier (C.repr i)) generatorAElement → C.repr i = 1) :
    Function.Injective toCarrier := by
  apply toCarrier_injective_of_kernel_centralizes_a
  intro k hk
  obtain ⟨h, i, he⟩ := C.covers Faithfulness.canonical_generates k
  have hh : Commute h.val (generator false) :=
    (Subgroup.mem_centralizer_iff.mp h.property _ (Set.mem_singleton _)).symm
  have hhm : Commute (toCarrier h.val) generatorAElement := by
    simpa only [toCarrier_generator_false] using hh.map toCarrier
  have hm : toCarrier (C.repr i) = (toCarrier h.val)⁻¹ := by
    have hc : toCarrier h.val * toCarrier (C.repr i) = 1 := by
      rw [← map_mul, ← he]
      exact hk
    exact eq_inv_of_mul_eq_one_right hc
  have hr := hsep i (by rw [hm]; exact hhm.inv_left)
  simpa only [he, hr, mul_one] using hh.eq

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact

namespace Sporadic.LeechRelated.HS.AtlasPresentation

/-- The canonical map from the exact ATLAS presentation to the literal HS
carrier is faithful, with both marked generator images unchanged. -/
public theorem toCarrier_injective : Function.Injective toCarrier :=
  Exact.faithful_of_cover Exact.Cover.cover (fun i hi => Exact.representative_eq_one i hi)

end Sporadic.LeechRelated.HS.AtlasPresentation

namespace Representation.HigmanSims.LargeModels.Restricted1408
open Sporadic.LeechRelated.HS

/-- The marked degree-1408 matrices descend to the literal HS carrier. -/
public theorem matrixDescentExists : MatrixDescentExists :=
  matrixDescentExists_of_presentation (fun _ => AtlasPresentation.toCarrier_injective) matrixRelations

end Representation.HigmanSims.LargeModels.Restricted1408
