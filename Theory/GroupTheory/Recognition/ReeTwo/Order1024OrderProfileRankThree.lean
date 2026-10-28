module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileRankThreeCoordinates
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileRankThreeKernel
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileRankThreeCounts

/-!
# Assembly of the five rank-three residual order-profile models

The concrete quotient homomorphisms, surjectivity and seven-bit fiber
parametrizations are proved in `Order1024OrderProfileRankThreeCoordinates`.
The independently proved Frattini-kernel and exact order-count certificates
complete the five models through `OrderProfileModel.of_counts`. They refer to
those concrete maps and original representatives, so no realization is inferred
from the abstract color tables.

The ordered quotient bases use the Shinoda (1975), (2.3), pp. 81–82 convention
recorded in the coordinate module.
-/

namespace ReeTwo.SylowModel

/-- Assemble the rank-three models from their concrete kernel and count certificates. -/
public theorem orderProfileModel_rankThree_of_coordinates
    (hker : ∀ j : Fin 5, (rankThreeProjection j).ker =
      frattini (residualCandidate (rankThreeIndex j)))
    (hc : ∀ (j : Fin 5) (v : OrderProfileQuotient 3),
      (Subgroup.fiberProfile (rankThreeProjection j) orderOf v 1,
        Subgroup.fiberProfile (rankThreeProjection j) orderOf v 2,
        Subgroup.fiberProfile (rankThreeProjection j) orderOf v 4) = rankThreeCounts j v) :
    ∀ i : Fin 15, i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 8 → OrderProfileModel i := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact OrderProfileModel.of_counts 2 (rankThreeProjection 0)
      (rankThreeProjection_surjective 0) (hker 0) (hc 0)
  · exact OrderProfileModel.of_counts 3 (rankThreeProjection 1)
      (rankThreeProjection_surjective 1) (hker 1) (hc 1)
  · exact OrderProfileModel.of_counts 4 (rankThreeProjection 2)
      (rankThreeProjection_surjective 2) (hker 2) (hc 2)
  · exact OrderProfileModel.of_counts 6 (rankThreeProjection 3)
      (rankThreeProjection_surjective 3) (hker 3) (hc 3)
  · exact OrderProfileModel.of_counts 8 (rankThreeProjection 4)
      (rankThreeProjection_surjective 4) (hker 4) (hc 4)

/-- The five rank-three residual representatives realize their Frattini order profiles. -/
public theorem orderProfileModel_rankThree :
    ∀ i : Fin 15, i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 8 → OrderProfileModel i :=
  orderProfileModel_rankThree_of_coordinates
    rankThreeProjection_ker_eq_frattini rankThreeProjection_orderCounts

end ReeTwo.SylowModel
