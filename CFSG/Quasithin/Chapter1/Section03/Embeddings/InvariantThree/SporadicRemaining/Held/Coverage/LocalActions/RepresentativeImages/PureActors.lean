module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions.Reductions

/-!
# Non-diagonal lower witnesses for the pure Held representative images

The model actors normalize the fixed Held permutation carrier and preserve
both literal candidate subgroups. Here their checked marked-basis formulas
are expressed using the chapter's actual `planeAction`: a quarter-turn for
false and its inverse for true. No action-realization or inner-image premise
is needed. Full-image assembly remains in RepresentativeImages.

Source context: GLS3 Table 5.3p and quasithin printed pp.509–511. These
witnesses support the retained Held branch, not the blanket Held exclusion.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs.LocalActions
namespace RepresentativeImages

open Held.LocalPairs.PairCoverage.LocalActions
open Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages

/-- The coordinate formula for the genuine pure-pair actor. -/
theorem pure_actor_planeAction (i : Bool) :
    planeAction (candidateTwo i 0) (candidateOdd i 0) (candidateOddEquiv i 0)
      (PureActors.actor i) = PureActors.coordinateAction i :=
  PureActors.actor_coordinates i

theorem pure_actor_false_planeAction :
    planeAction (candidateTwo false 0) (candidateOdd false 0) (candidateOddEquiv false 0)
      (PureActors.actor false) = rotation :=
  pure_actor_planeAction false

theorem pure_actor_true_planeAction :
    planeAction (candidateTwo true 0) (candidateOdd true 0) (candidateOddEquiv true 0)
      (PureActors.actor true) = rotation⁻¹ :=
  pure_actor_planeAction true

theorem pure_actor_planeAction_not_mem_diagonal (i : Bool) :
    planeAction (candidateTwo i 0) (candidateOdd i 0) (candidateOddEquiv i 0)
      (PureActors.actor i) ∉ diagonal := by
  rw [pure_actor_planeAction]
  exact PureActors.coordinateAction_not_mem_diagonal i

/-- Unconditional witnesses for the separate full-image assembly. -/
theorem exists_pure_nondiagonal_actor (i : Bool) :
    ∃ a : Held.LocalPairs.permutationPairStabilizer (candidateTwo i 0) (candidateOdd i 0),
      planeAction (candidateTwo i 0) (candidateOdd i 0) (candidateOddEquiv i 0) a ∉ diagonal :=
  ⟨PureActors.actor i, pure_actor_planeAction_not_mem_diagonal i⟩

end RepresentativeImages
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs.LocalActions
