module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound

/-!
# Applying the local relation certificate to the reduced order bound

The checked local cover removes the order-20,160 premise from the existing
consumer, leaving the four explicit local word identities and the independent
outer cover. Both concern the literal reduced presentation. Source and final
discharge obligations are recorded in `source/README.md`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced
open Subgroup.CosetWordCertificate

theorem finite_card_of_outer_cover_and_local_relations
    (C : Subgroup.GeneratorCosetCover Bound.localSubgroup generator (Fin 22))
    (hr : ∀ r : Fin 4,
      eval Bound.subgroupGenerator (Bound.LocalFinite.extraRelatorWord r) = 1) :
    Finite Carrier ∧ Nat.card Carrier ≤ 443520 :=
  finite_card_of_local_bound C (Bound.local_finite_card_of_extra hr)

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced
