module

public import Theory.GroupTheory.CubicCoreQuotientNormalizer
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.SpecificGroups.PSL2.TwentyFiveThirteen
public import GorensteinWalter.PSL2Center

/-!
# A cubic Cartan actor in a PSL₂(25) overcomponent

The actual quotient J/O₂(J) is PSL₂(25). Its outer group is a two-group,
and its order7800 is not divisible by nine. Thus a three-group actor has
image of order at most three. Its specified cubic subgroup inside a
perfect K ≤ J realizes this image, so the whole actor normalizes K once
O₂(J) normalizes K.

This proves the PSL₂(25) row in the rank-one-container reduction of
Aschbacher–Smith9.3.1, printed p.732. No arbitrary quotient action is
substituted for the actual conjugation map.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.PSL2.TwentyFive
variable {G : Type*} [_root_.Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F]

/-- The actual three-group action on a PSL₂(25) core quotient normalizes
its perfect subgroup containing the marked diagonal cubic. -/
theorem cartan_normalizes_perfect_subgroup
    (K J A B : Subgroup G) [Group.IsPerfect K]
    (hKJ : K ≤ J) (hAJ : A ≤ normalizer (J : Set G))
    (hBA : B ≤ A) (hBK : B ≤ K)
    (hQK : J.pCoreIn 2 ≤ normalizer (K : Set G))
    (hA : IsPGroup 3 A) (hB : Nat.card B = 3)
    (hF : Nat.card F = 25)
    (e : (J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :
    A ≤ normalizer (K : Set G) := by
  have hz : center (J ⧸ pCore 2 J) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hez : e z ∈ center (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :=
      (centerCongr e ⟨z,hz⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hez
    exact e.injective (hez.trans e.map_one.symm)
  have ho : IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J)) :=
    (OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      (by decide : Nat.Prime 5) (by decide : Odd 5) (by decide : 2 ≤ 2)
      (show Nat.card F = 5 ^ 2 from hF)).of_equiv (MulAut.outerCongr e).symm
  apply CubicCoreQuotientNormalizer.normalizes_of_small_image K J A B hKJ hAJ hBA hBK hQK hB hz
  apply CubicCoreQuotientNormalizer.cubic_action_image_card_le_three _ hA hz ho
  rw [Nat.card_congr e.toEquiv,card hF]
  decide
end Theory.PSL2.TwentyFive
