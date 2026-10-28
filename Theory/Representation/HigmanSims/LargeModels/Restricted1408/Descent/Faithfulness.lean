module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aCover
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder

/-!
# Faithfulness reduced to the order of the literal source subgroup

The checked 100-coset cover gives an upper bound for Universal from a finite
bound for M₁ₐ. A bound of 443,520 then matches the proved order 44,352,000 of
the literal permutation carrier. The canonical surjection is therefore
injective, with its original marked generator images. Applying that exact map
to the degree-1408 descent discharges its presentation-faithfulness premise.

The finite subgroup bound remains an explicit mathematical obligation here;
this module does not yet assert unconditional presentation faithfulness.
Source: ATLAS HSG1-P1.M, the subgroup M1a and its index-100 hint.
-/

namespace Sporadic.LeechRelated.HS.AtlasPresentation

/-- The certified coset bound and the subgroup order bound force the actual
marked presentation map to be faithful. No simplicity assumption is needed. -/
public theorem toCarrier_injective_of_m1a_bound
    (hfinite : Finite Faithfulness.M1a)
    (hcard : Nat.card Faithfulness.M1a ≤ 443520) : Function.Injective toCarrier := by
  let : Finite Faithfulness.M1a := hfinite
  obtain ⟨hU, hUcard⟩ := Faithfulness.finite_card_le_of_m1a
  let : Finite Universal := hU
  apply toCarrier_injective_of_card_le
  rw [NormalizerIndex.card_carrier]
  exact hUcard.trans (Nat.mul_le_mul_right 100 hcard)

end Sporadic.LeechRelated.HS.AtlasPresentation

namespace Representation.HigmanSims.LargeModels.Restricted1408
open Sporadic.LeechRelated.HS

/-- Consumer application: the literal subgroup bound discharges presentation
faithfulness in the existing marked matrix-descent theorem. Matrix relations
remain with their independent producer. -/
public theorem matrixDescentExists_of_m1a_bound
    (hfinite : Finite AtlasPresentation.Faithfulness.M1a)
    (hcard : Nat.card AtlasPresentation.Faithfulness.M1a ≤ 443520)
    (hmatrices : MatrixRelations) : MatrixDescentExists :=
  matrixDescentExists_of_presentation
    (fun _ => AtlasPresentation.toCarrier_injective_of_m1a_bound hfinite hcard) hmatrices

end Representation.HigmanSims.LargeModels.Restricted1408
