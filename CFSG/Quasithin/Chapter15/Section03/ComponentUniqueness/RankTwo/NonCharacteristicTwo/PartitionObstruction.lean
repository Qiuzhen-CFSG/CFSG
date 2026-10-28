module

public import Theory.GroupTheory.GeneralizedFitting.OddNormalObstruction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.Partitions

/-!
# The normal three-group in the (4,3)-partition stabilizer

Use the existing faithful seven-point block action, rather than a new abstract
partition label. The three-cycles of its three-point block form a normal
subgroup of order three. Every subgroup containing those cycles therefore
fails F* = O₂. The final theorem transports this obstruction through an actual
isomorphism of the local subgroup, including its marked three-group.

Placement of the source M_I in this stabilizer remains a separate obligation;
no A₇ exclusion or maximal-subgroup recognition is asserted here.
Source: Aschbacher--Smith, combined manuscript, 15.3.42, printed p.1138.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.PartitionObstruction
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
/-- The alternating group on the three-point block, fixing the other block. -/
def threeFactor : Subgroup FourThree := (⊥ : Subgroup (Equiv.Perm (Fin 4))).prod
  (alternatingGroup (Fin 3))

instance threeFactor_normal : threeFactor.Normal := inferInstanceAs
  ((⊥ : Subgroup (Equiv.Perm (Fin 4))).prod (alternatingGroup (Fin 3))).Normal

/-- The explicit block subgroup has order three. -/
theorem card_threeFactor : Nat.card threeFactor = 3 := by
  rw [threeFactor, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  rw [Subgroup.card_bot, nat_card_alternatingGroup]
  norm_num

/-- The three-cycles on the block of size three are an actual normal subgroup. -/
noncomputable def threeCycles : Subgroup fourThreeStabilizer := threeFactor.map fourThreeEquiv.toMonoidHom

instance threeCycles_normal : threeCycles.Normal :=
  Subgroup.Normal.map threeFactor_normal _ fourThreeEquiv.surjective

/-- The same cardinality in the actual seven-point stabilizer. -/
theorem card_threeCycles : Nat.card threeCycles = 3 := by
  rw [threeCycles, Subgroup.card_map_of_injective (f := fourThreeEquiv.toMonoidHom) fourThreeEquiv.injective, card_threeFactor]

/-- This also applies to the alternating partition stabilizer. -/
theorem not_characteristicTwo_of_contains_threeCycles
    (J : Subgroup fourThreeStabilizer) (hJ : threeCycles ≤ J) :
    generalizedFitting J ≠ pCore 2 J := by
  apply not_characteristicTwo_of_normal_three (threeCycles.subgroupOf J)
  exact (Nat.card_congr (subgroupOfEquivOfLe hJ).toEquiv).trans card_threeCycles

/-- Transport the explicit normal three-group through the actual subgroup equivalence. -/
theorem not_characteristicTwo_of_equiv
    {H : Type*} [Group H] [Finite H]
    (J : Subgroup fourThreeStabilizer) (hJ : threeCycles ≤ J) (e : H ≃* J) :
    generalizedFitting H ≠ pCore 2 H := by
  let N := (threeCycles.subgroupOf J).map e.symm.toMonoidHom
  have : N.Normal := Subgroup.Normal.map inferInstance _ e.symm.surjective
  apply not_characteristicTwo_of_normal_three N
  rw [Subgroup.card_map_of_injective e.symm.injective]
  exact (Nat.card_congr (subgroupOfEquivOfLe hJ).toEquiv).trans card_threeCycles
end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.PartitionObstruction
