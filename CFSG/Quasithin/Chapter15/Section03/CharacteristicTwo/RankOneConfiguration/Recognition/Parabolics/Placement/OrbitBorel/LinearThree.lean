module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree.OrbitCoordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree.ProductCalculation

/-!
# Excluding the nonnormal linear-three component orbit

The earlier orbit reduction constructs Y₊ inside the S-span. Restricting
Y₊ to that span and then taking an image with two-group kernel preserves
its Sylow three-order, exactly three. The two actual conjugate components
give product coordinates modulo the two-core, with PSL₃(2) factors. The
Sylow intersection acts as the product of the coordinate Sylow subgroups,
and a moving element of S exchanges the factors while preserving Y₊'s image.

The concrete PSL₃(2) Sylow subgroups are self-normalizing, so the intrinsic
product calculation makes the three-part of this image a square, contradicting
its Sylow three-order. Thus the explicit PSL₃(2) branch is impossible under
relative nonnormality. The universal earlier orbit results remain explicit;
model selection and the other branch belong to the enclosing assembly.

Source: Aschbacher–Smith, proof of 15.3.27, printed p.1130 (PDF p.1147,
combined manuscript of 1 March 2004).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- Every quotient of the actual orbit span with two-group kernel retains
Sylow three-subgroups of order three in the image of Y₊. -/
theorem yplus_image_sylow_three_card {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (h : RankOneFacts d I)
    (hr : primeRank 3 d.Yplus = 1)
    {J : Type v} [Group J] (q : localSpan c.L d.S →* J)
    (hq : IsPGroup 2 q.ker)
    (P : Sylow 3 ((d.Yplus.subgroupOf (localSpan c.L d.S)).map q)) : Nat.card P = 3 := by
  obtain ⟨hY, _, _, hthree⟩ := yplus_invariant_three_subgroup earlier hG d hI c hn hS h hr
  exact sylow_three_card_image q hq _
    (sylow_three_card_subgroupOf _ _ hY hthree) P

/-- The nonnormal orbit cannot have intrinsic component quotient PSL₃(2).
The product coordinates and the invariant image of the actual Y₊ are
constructed from the source hypotheses, with no additional model certificate. -/
theorem excluded {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (h : RankOneFacts d I)
    (hr : primeRank 3 d.Yplus = 1)
    (hm : ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 3 2) : False := by
  obtain ⟨a⟩ := OrbitCoordinates.nonempty_productCoordinates
    earlier hG d hI hf c hn hS h hr hm
  exact ProductCalculation.not_sylow_three_card_eq_three a.firstSylow a.secondSylow
    (model_sylow_self_normalizing a.firstModel a.firstSylow)
    (model_sylow_self_normalizing a.secondModel a.secondSylow)
    _ a.sylow_invariant a.exchange a.exchange_first a.exchange_second a.exchange_invariant
    (yplus_image_sylow_three_card earlier hG d hI c hn hS h hr a.quotient a.kernel_two)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree
