module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.Characteristic
public import Theory.GroupTheory.PCorePrimeToIndex

/-!
# Relative normal closure and intrinsic cores in the Hall--Janko normalizer

The normal closure defining `l₂` is taken in `p₂`. Its image is normal there;
the characteristic radical places `s` and hence `q₂` inside that image.
The order of `q₂` identifies it with the intrinsic core of `l₂` once the
second-parabolic core-cardinality calculation is supplied.

If the full normalizer has order 1152, the subgroup `s` has odd index nine.
Consequently the intrinsic cores of `l₂` and `p₂` have the same ambient image.
This proves the core bridge without duplicating the intrinsic `l₂` calculation.
The normalizer order is an explicit remaining finite computation, not an
assumed consequence of the source's extension notation.
Source: GLS3 Table 5.3g and Aschbacher--Smith, printed p.511 (PDF p.528).
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
open Seed Subgroup

@[instance] theorem q₂_normal_in_p₂ : (q₂.subgroupOf p₂).Normal :=
  normal_subgroupOf_of_le_normalizer le_rfl

theorem l₂_le_p₂ : l₂ ≤ p₂ := map_subtype_le _

theorem l₂_subgroupOf_p₂ : l₂.subgroupOf p₂ = normalClosure (s.subgroupOf p₂ : Set p₂) := by
  change ((normalClosure (s.subgroupOf p₂ : Set p₂)).map p₂.subtype).comap p₂.subtype = _
  exact comap_map_eq_self (by simp)

@[instance] theorem l₂_normal_in_p₂ : (l₂.subgroupOf p₂).Normal := by
  rw [l₂_subgroupOf_p₂]
  infer_instance

theorem s_le_p₂_of_characteristic (hc : (q₂.subgroupOf s).Characteristic) : s ≤ p₂ := by
  let := hc
  exact (normal_subgroupOf_iff_le_normalizer q₂_le_s).mp inferInstance

theorem s_le_l₂_of_le_p₂ (hsp : s ≤ p₂) : s ≤ l₂ := by
  intro x hx
  exact ⟨⟨x, hsp hx⟩, subset_normalClosure hx, rfl⟩

theorem s_le_p₂ : s ≤ p₂ := s_le_p₂_of_characteristic q₂_characteristic

theorem s_le_l₂ : s ≤ l₂ := s_le_l₂_of_le_p₂ s_le_p₂

theorem q₂_le_l₂ : q₂ ≤ l₂ := q₂_le_s.trans s_le_l₂

@[instance] theorem q₂_normal_in_l₂ : (q₂.subgroupOf l₂).Normal :=
  normal_subgroupOf_of_le_normalizer l₂_le_p₂

private theorem core_relative_map :
    ((pCore 2 (l₂.subgroupOf p₂)).map (l₂.subgroupOf p₂).subtype).map p₂.subtype =
      (pCore 2 l₂).map l₂.subtype := by
  let e : l₂.subgroupOf p₂ ≃* l₂ := subgroupOfEquivOfLe l₂_le_p₂
  rw [← pCore_map_iso 2 e, map_map, map_map]
  rfl

theorem mapped_l₂_core_le_p₂_core :
    (pCore 2 l₂).map l₂.subtype ≤ (pCore 2 p₂).map p₂.subtype := by
  let L := l₂.subgroupOf p₂
  let : L.Normal := l₂_normal_in_p₂
  have hle : (pCore 2 L).map L.subtype ≤ pCore 2 p₂ :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, pCore_isPGroup.map L.subtype⟩
  rw [← core_relative_map]
  exact map_mono hle

theorem s_relIndex_p₂_of_card (hsp : s ≤ p₂) (hP : Nat.card p₂ = 1152) :
    s.relIndex p₂ = 9 := by
  have hc : Nat.card (s.subgroupOf p₂) = 128 :=
    (Nat.card_congr (subgroupOfEquivOfLe hsp).toEquiv).trans card_s
  have h := (s.subgroupOf p₂).card_mul_index
  rw [hc, hP] at h
  change (s.subgroupOf p₂).index = 9
  omega

theorem mapped_p₂_core_eq_l₂_core_of_card (hsp : s ≤ p₂) (hP : Nat.card p₂ = 1152) :
    (pCore 2 p₂).map p₂.subtype = (pCore 2 l₂).map l₂.subtype := by
  have hLodd : ¬ 2 ∣ (l₂.subgroupOf p₂).index := by
    have hd := relIndex_dvd_of_le_left p₂ (s_le_l₂_of_le_p₂ hsp)
    rw [s_relIndex_p₂_of_card hsp hP] at hd
    exact fun h => (by decide : ¬ 2 ∣ 9) (h.trans hd)
  apply le_antisymm _ mapped_l₂_core_le_p₂_core
  rw [← core_relative_map]
  exact map_mono (pCore_le_map_pCore_of_prime_not_dvd_index (l₂.subgroupOf p₂) hLodd)

theorem l₂_core_eq_q₂_of_card (hqL : q₂ ≤ l₂) (hLcore : Nat.card (pCore 2 l₂) = 64) :
    pCore 2 l₂ = q₂.subgroupOf l₂ := by
  have hn := q₂_normal_in_l₂
  have hp : IsPGroup 2 (q₂.subgroupOf l₂) :=
    q₂_isPGroup.of_equiv (subgroupOfEquivOfLe hqL).symm
  have hle : q₂.subgroupOf l₂ ≤ pCore 2 l₂ := le_sSup ⟨hn, hp⟩
  apply (eq_of_le_of_card_ge hle _).symm
  rw [hLcore]
  exact le_of_eq ((Nat.card_congr (subgroupOfEquivOfLe hqL).toEquiv).trans card_q₂).symm

theorem p₂_core_eq_q₂_of_card (hsp : s ≤ p₂) (hP : Nat.card p₂ = 1152)
    (hLcore : Nat.card (pCore 2 l₂) = 64) : pCore 2 p₂ = q₂.subgroupOf p₂ := by
  have hqL := q₂_le_s.trans (s_le_l₂_of_le_p₂ hsp)
  apply map_injective p₂.subtype_injective
  rw [mapped_p₂_core_eq_l₂_core_of_card hsp hP, l₂_core_eq_q₂_of_card hqL hLcore,
    map_subgroupOf_eq_of_le hqL, map_subgroupOf_eq_of_le (show q₂ ≤ p₂ from q₂.le_normalizer)]

theorem p₂_core_card_of_card (hP : Nat.card p₂ = 1152)
    (hLcore : Nat.card (pCore 2 l₂) = 64) : Nat.card (pCore 2 p₂) = 64 := by
  rw [p₂_core_eq_q₂_of_card s_le_p₂ hP hLcore]
  exact (Nat.card_congr
    (subgroupOfEquivOfLe (show q₂ ≤ p₂ from q₂.le_normalizer)).toEquiv).trans card_q₂

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
