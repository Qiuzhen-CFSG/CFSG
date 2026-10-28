module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.Cardinality
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ElementarySixteenFusion

/-!
# The Hall–Janko exclusion in the deleted-five normal branch

The actual alternating-five block normalizes its characteristic elementary
sixteen. Its quotient has order sixty, so that normalizer has order divisible
by five. The native J₂ fusion calculation excludes this possibility.

Source: Aschbacher–Smith 13.5.15, printed p.921.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
open ChapterC
variable {G : Type*} [Group G]

theorem no_alternatingFive_of_j2_equiv
    (e : G ≃* Sporadic.LeechRelated.J2.Carrier) (A : Subgroup G)
    (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) : False := by
  let U := (blockU A).map A.subtype
  let : IsElementaryAbelian 2 (blockU A) := hA.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map A.subtype
  let W := U.map e.toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  have hcW : Nat.card W = 16 := (card_map_of_injective e.injective).trans hc
  apply Sporadic.LeechRelated.J2.ElementarySixteenFusion.five_not_dvd_card_normalizer W hcW
  have hAN : A ≤ normalizer (U : Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (blockU A))
  have hquot : 60 ∣ Nat.card A := by
    rw [← alternatingFive_quotient_card A hA]
    exact (pCore 2 A).card_quotient_dvd_card
  have hfive : 5 ∣ Nat.card (normalizer (U : Set G)) :=
    (dvd_trans (by decide : 5 ∣ 60) hquot).trans (card_dvd_of_le hAN)
  have hcardN : Nat.card (normalizer (W : Set Sporadic.LeechRelated.J2.Carrier)) =
      Nat.card (normalizer (U : Set G)) := by
    rw [← map_equiv_normalizer_eq U e, card_map_of_injective e.injective]
  rwa [hcardN]

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
