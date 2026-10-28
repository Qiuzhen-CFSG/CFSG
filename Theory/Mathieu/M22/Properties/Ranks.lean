module
public import Theory.Mathieu.M22.Properties.MultiplierCovers
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
namespace Sporadic.Mathieu
noncomputable section
public structure M22ElementLiftData where
  coverLabel : String
  baseOrder : Nat
  liftedOrder : Nat
  fusionDescription : String
@[expose] public def m22TwoElementLiftData : M22ElementLiftData :=
  { coverLabel := "2M22", baseOrder := 2, liftedOrder := 4,
    fusionDescription := "central involution times a 2A lift" }
@[expose] public def m22ThreeElementLiftData : M22ElementLiftData :=
  { coverLabel := "3M22", baseOrder := 3, liftedOrder := 3,
    fusionDescription := "3-central lift interface" }
@[expose] public def m22FourElementLiftData : M22ElementLiftData :=
  { coverLabel := "4M22", baseOrder := 2, liftedOrder := 4,
    fusionDescription := "two central lifts, fused by the outer involution" }
public structure M22RankData where
  groupLabel : String
  prime : Nat
  rank : Nat
  witnessDescription : String
  upperBoundDescription : String
@[expose] public def m22TwoRankData : M22RankData :=
  { groupLabel := "M22", prime := 2, rank := 4,
    witnessDescription := "E16 natural-action certificate",
    upperBoundDescription := "2-part of the order and fixed-point count" }
@[expose] public def m22TwoCoverRankData : M22RankData :=
  { groupLabel := "2M22", prime := 2, rank := 5,
    witnessDescription := "central C2 times E16",
    upperBoundDescription := "cover-model rank interface" }
@[expose] public def m22FourCoverRankData : M22RankData :=
  { groupLabel := "4M22", prime := 2, rank := 4,
    witnessDescription := "4-cover lift/fusion certificate",
    upperBoundDescription := "cover-model rank interface" }
@[expose] public def m22ThreeRankData : M22RankData :=
  { groupLabel := "M22", prime := 3, rank := 2,
    witnessDescription := "E9 natural-action certificate",
    upperBoundDescription := "3-part of the order" }
public theorem m22Rank_values :
    (m22TwoRankData.rank, m22TwoCoverRankData.rank,
      m22FourCoverRankData.rank, m22ThreeRankData.rank) =
      (4, 5, 4, 2) := by
  rfl
public theorem m22ElementLift_values :
    (m22TwoElementLiftData.baseOrder, m22TwoElementLiftData.liftedOrder,
      m22ThreeElementLiftData.baseOrder, m22FourElementLiftData.liftedOrder) =
      (2, 4, 3, 4) := by
  rfl
end
end Sporadic.Mathieu
