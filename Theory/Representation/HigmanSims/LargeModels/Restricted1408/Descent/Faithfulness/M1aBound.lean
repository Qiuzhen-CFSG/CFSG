module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.Presentation

/-!
# The remaining M₁ₐ bound as a concrete finite-presentation calculation

All 1,300 local relations are now proved in the abstract HS presentation.
The checked marked homomorphism transfers a finite order bound for the local
presentation to the literal subgroup M₁ₐ. Its numerical bound is still an
explicit premise; unconditional finiteness and order are not asserted here.

Source: ATLAS HSG1-P1.M, via the Schreier presentation documented under
`M1aBound/source/README.md`.
-/

namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness

/-- The remaining local cardinal certificate discharges exactly the M₁ₐ premise
of the existing marked HS faithfulness assembly. -/
public theorem m1a_finite_card_le_of_schreier_bound
    (h : Finite M1aBound.Schreier.Carrier ∧ Nat.card M1aBound.Schreier.Carrier ≤ 443520) :
    Finite M1a ∧ Nat.card M1a ≤ 443520 :=
  M1aBound.Schreier.m1a_finite_card_of_bound h

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness
