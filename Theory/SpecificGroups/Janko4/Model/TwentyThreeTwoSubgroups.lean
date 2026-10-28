module
public import Theory.SpecificGroups.Janko4.Model.SylowOvergroups.PrimeTwentyThree
public import Theory.SpecificGroups.Janko4.Model.Cardinality
/-!
# Two-subgroups normalized by a prime-23 actor in J₄

Neither native involution centralizer has order divisible by 23. Therefore
an element of order 23 fixes no nonidentity element of a normalized
two-subgroup U: any nontrivial fixed two-group would contain an involution.
Orbit counting gives |U| congruent to 1 modulo 23. The native group order
bounds the exponent of |U| by 21, leaving only orders 1 and 2048.

Consequently a nontrivial elementary subgroup and any containing two-group,
when both are normalized by the same prime-23 actor, coincide. The actual
Mathieu pushing-up application uses the image of its original component
intersection and its original chosen module in the central quotient.

Source: Aschbacher--Smith 4.2.13, printed p.612. The native orders and
involution-centralizer certificates retain the imported ATLAS provenance.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Janko4
attribute [local irreducible] modelGroup matrixA matrixB

/-- A two-subgroup normalized by an actor containing an element of order 23
has order at most 2048, with no Sylow-placement or commutativity premise. -/
theorem twentyThree_normalized_twoGroup_card_le_2048
    (B U : Subgroup Model) (h23 : 23 ∣ Nat.card B) (hU : IsPGroup 2 U)
    (hn : B ≤ normalizer (U : Set Model)) : Nat.card U ≤ 2048 := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 23 h23
  let X := zpowers (b : Model)
  have hX : IsPGroup 23 X := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,hb,pow_one])
  have hXU : X ≤ normalizer (U : Set Model) := zpowers_le.mpr (hn b.property)
  have hc : U ⊓ centralizer (X : Set Model) = ⊥ := by
    by_contra hne
    have hd : 2 ∣ Nat.card (U ⊓ centralizer (X : Set Model) : Subgroup Model) :=
      (hU.to_le inf_le_left).card_eq_or_dvd.resolve_left (fun hh => hne (card_eq_one.mp hh))
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2 hd
    have hz' : orderOf (z : Model) = 2 := (orderOf_coe z).trans hz
    have hbC : (b : Model) ∈ centralizer ({(z : Model)} : Set Model) :=
      mem_centralizer_singleton_iff.mpr (z.property.2 b (mem_zpowers (b : Model)))
    apply SylowOvergroups.involution_centralizer_not_dvd_twentyThree z hz'
    have ho : orderOf (⟨b,hbC⟩ : centralizer ({(z : Model)} : Set Model)) = 23 :=
      (orderOf_coe _).symm.trans ((orderOf_coe b).trans hb)
    exact ho ▸ orderOf_dvd_natCard (⟨b,hbC⟩ : centralizer ({(z : Model)} : Set Model))
  have hm := card_modEq_card_inf_centralizer X U hX hXU
  rw [hc,card_bot] at hm
  obtain ⟨n,hnc⟩ := hU.exists_card_eq
  have hd := card_subgroup_dvd_card U
  rw [hnc] at hm hd ⊢
  have hbnd : n ≤ 21 := by
    by_contra hh
    have h22 : 2^22 ∣ Nat.card Model := (pow_dvd_pow 2 (by omega : 22 ≤ n)).trans hd
    rw [Cardinality.model_card] at h22
    norm_num at h22
  interval_cases n <;> norm_num [Nat.ModEq] at hm
  all_goals norm_num

/-- The prime-23 action identifies the whole normalized two-subgroup with
its nontrivial normalized elementary subgroup. -/
theorem twentyThree_elementary_eq_normalized_twoGroup
    (B U V : Subgroup Model) (h23 : 23 ∣ Nat.card B)
    (hU : IsPGroup 2 U) [IsElementaryAbelian 2 V]
    (hne : V ≠ ⊥) (hVU : V ≤ U)
    (hnU : B ≤ normalizer (U : Set Model))
    (hnV : B ≤ normalizer (V : Set Model)) : V = U := by
  let N := normalizer (V : Set Model)
  let E := V.subgroupOf N
  let : E.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf V.le_normalizer
  have hE : E ≠ ⊥ := by
    intro he
    have hh := congrArg (map N.subtype) he
    rw [map_subgroupOf_eq_of_le V.le_normalizer,Subgroup.map_bot] at hh
    exact hne hh
  have hb := SylowOvergroups.normal_elementary_card_ge_of_twentyThree N
    (h23.trans (card_dvd_of_le hnV)) E hE
  rw [Nat.card_congr (subgroupOfEquivOfLe V.le_normalizer).toEquiv] at hb
  exact eq_of_le_of_card_ge hVU
    ((twentyThree_normalized_twoGroup_card_le_2048 B U h23 hU hnU).trans hb)
end Janko4
