module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.Calculus

/-! Kernel checks for the finite Schreier table. Transition identities are
checked in the free group, and the thirteen source words close at each of the
100 vertices. These checks give actual equations in Universal through the
structural telescoping proof in `Calculus`. -/

namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier
open Subgroup.CosetWordCertificate

private theorem checks :
    (∀ i a, EdgeCheck i a) ∧ (∀ i r, terminal i (sourceWord r) = i) := by
  decide +kernel

public theorem transition_checked (i : Fin 100) (a : Letter Bool) : EdgeCheck i a :=
  checks.1 i a

public theorem source_loop (i : Fin 100) (r : Fin 13) : terminal i (sourceWord r) = i :=
  checks.2 i r

/-- All defining relations of the local presentation hold in Universal itself. -/
public theorem relator_valid (i : Fin 100) (r : Fin 13) :
    eval edgeGenerator (relatorWord i r) = 1 :=
  relator_valid_of_checks transition_checked source_loop i r

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier
