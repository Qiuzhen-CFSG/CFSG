module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RankTwoCoordinates
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RankTwoFrattini
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RankTwoOrderCounts

/-!
# Assembly of the rank-two residual order profiles

The surjective coordinate maps and their fibers are constructed in
`Order1024RankTwoCoordinates`. The square-word kernel identifications in
`Order1024RankTwoFrattini` and exact element-order counts in
`Order1024RankTwoOrderCounts` complete the models at indices 10, 11 and 14.
The assembly compares these actual fiber counts with the prescribed tables.

Source: the root convention of Shinoda (1975), (2.3), pp. 81–82, and the
ordered bases and order-profile tables in `Order1024OrderProfileData`.
-/

namespace ReeTwo.SylowModel

/-- The two concrete coordinate obligations imply all three required models. -/
public theorem orderProfileModel_rankTwo_of_coordinates
    (hker : ∀ c, (rankTwoProjection c).ker = frattini (residualCandidate (rankTwoIndex c)))
    (hc : ∀ c v, (Subgroup.fiberProfile (rankTwoProjection c) orderOf v 1,
      Subgroup.fiberProfile (rankTwoProjection c) orderOf v 2,
      Subgroup.fiberProfile (rankTwoProjection c) orderOf v 4) = rankTwoProfileCounts c v) :
    ∀ i : Fin 15, i = 10 ∨ i = 11 ∨ i = 14 → OrderProfileModel i := by
  rintro i (rfl | rfl | rfl)
  · apply OrderProfileModel.of_counts 10 (rankTwoProjection 0)
      (rankTwoProjection_surjective 0) (hker 0)
    intro v
    have htable : ∀ v : OrderProfileQuotient 2,
        rankTwoProfileCounts 0 v = orderProfileCounts 10 v := by
      unfold rankTwoProfileCounts orderProfileCounts orderProfileColor orderProfileRank
      decide +kernel
    exact (hc 0 v).trans (htable v)
  · apply OrderProfileModel.of_counts 11 (rankTwoProjection 1)
      (rankTwoProjection_surjective 1) (hker 1)
    intro v
    have htable : ∀ v : OrderProfileQuotient 2,
        rankTwoProfileCounts 1 v = orderProfileCounts 11 v := by
      unfold rankTwoProfileCounts orderProfileCounts orderProfileColor orderProfileRank
      decide +kernel
    exact (hc 1 v).trans (htable v)
  · apply OrderProfileModel.of_counts 14 (rankTwoProjection 2)
      (rankTwoProjection_surjective 2) (hker 2)
    intro v
    have htable : ∀ v : OrderProfileQuotient 2,
        rankTwoProfileCounts 2 v = orderProfileCounts 14 v := by
      unfold rankTwoProfileCounts orderProfileCounts orderProfileColor orderProfileRank
      decide +kernel
    exact (hc 2 v).trans (htable v)

/-- The three rank-two residual candidates realize their prescribed Frattini
quotients and element-order fiber profiles. -/
public theorem orderProfileModel_rankTwo :
    ∀ i : Fin 15, i = 10 ∨ i = 11 ∨ i = 14 → OrderProfileModel i :=
  orderProfileModel_rankTwo_of_coordinates
    rankTwoProjection_ker_eq_frattini rankTwoProjection_order_counts

end ReeTwo.SylowModel
