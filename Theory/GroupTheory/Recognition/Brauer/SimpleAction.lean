module
public import Theory.GroupTheory.Recognition.Brauer.OddActionKernel
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The Brauer action for a simple group

For a finite simple group satisfying Brauer's seed postulates, the actual
point-and-line collineation representation is injective. This is the
simple-group reduction of Brauer, *On finite Desarguesian planes I*,
(4B)-(4D), article page 123, used by the ABG recognition adapter.

Simplicity makes the normal kernel either trivial or the whole group.
The latter is impossible: its order is odd by (4C), whereas it would contain
the distinguished involution of order two. The trivial-kernel criterion
then gives injectivity, and the usual image equivalence can identify the
source group with its actual collineation image. No coordinate recognition,
nonabelian hypothesis, or faithful-action instance is assumed.
-/

namespace Theory.GroupTheory.BrauerPlaneSeed

public theorem collineationRepresentation_injective
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (S : BrauerPlaneSeed G) :
    Function.Injective S.collineationRepresentation := by
  apply S.collineationRepresentation.ker_eq_bot_iff.mp
  rcases (inferInstance : S.collineationRepresentation.ker.Normal).eq_bot_or_eq_top with hK | hK
  · exact hK
  · have hjK : S.j ∈ S.collineationRepresentation.ker := by simp only [hK, Subgroup.mem_top]
    have ho := S.odd_card_collineationRepresentation_ker.of_dvd_nat
      (S.collineationRepresentation.ker.orderOf_dvd_natCard hjK)
    rw [S.j_order] at ho
    obtain ⟨k, hk⟩ := ho
    omega

end Theory.GroupTheory.BrauerPlaneSeed
