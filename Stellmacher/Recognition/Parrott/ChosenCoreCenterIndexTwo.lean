module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterLocalBounds
public import Theory.GroupTheory.IndexTwoCentralizerFixedCard

/-!
# The lower bound for the chosen center in the index-two branch

Put C = K ∩ S and A = C_E(C). The central binary commutator pairing
gives |A| |C| = 512, since C_E(a) has order sixteen and E is
self-centralizing. If S covers only an order-two subgroup modulo K,
then |C| = 64 and |A| = 8. The group S normalizes A and C acts
trivially on it, so the involution fixed-point bound excludes a
two-element derived center.

Only the original local hypotheses and the supplied witnesses are used.
Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the parenthetical lower bound on p.676.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem card_subgroupOf_inf (U V : Subgroup G) :
    Nat.card (U.subgroupOf V) = Nat.card (U ⊓ V : Subgroup G) := by
  rw [← subgroupOf_map_subtype]
  exact (card_map_of_injective V.subtype_injective).symm

/-- The annihilator in E of the actual core intersection has complementary
order 512. This formula applies in both quotient-index branches. -/
public theorem chosen_core_derived_centralizer_card_mul
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let C := K ⊓ S
    Nat.card (E ⊓ centralizer (C : Set G) : Subgroup G) * Nat.card C = 512 := by
  intro H J K E S C
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ, _, _, _, hupper, helem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := helem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hcomm : ⁅E, C⁆ ≤ zpowers z := by
    apply commutator_le.mpr
    rintro e ⟨b, hb, rfl⟩ c hc
    obtain ⟨cH, hcJ, rfl⟩ := hc.1
    have hbc : ⁅b, (⟨cH, hcJ⟩ : J)⁆ ∈ center J := by
      have hbU : b ∈ Subgroup.upperCentralSeries J 2 := hupper ▸ hb
      simpa only [Subgroup.upperCentralSeries_one] using
        (Subgroup.mem_upperCentralSeries_succ_iff.mp hbU (⟨cH, hcJ⟩ : J))
    rw [← hZ]
    exact mem_map_of_mem (H.subtype.comp J.subtype) hbc
  have hZcomm : ⁅zpowers z, C⁆ ≤ ⊥ := by
    rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
    intro c hc u hu
    obtain ⟨n, rfl⟩ := hu
    exact (Commute.zpow_right
      (mem_centralizer_singleton_iff.mp hc.2.1 : Commute c z) n).symm.eq
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hEC : E ⊓ C = E ⊓ d.F := by
    have hEK : E ≤ K := by
      rintro x ⟨j, _, rfl⟩
      exact mem_map_of_mem H.subtype j.property
    have hEH : E ≤ H := hEK.trans (map_subtype_le _)
    change E ⊓ (K ⊓ (H ⊓ centralizer ({(d.a : G)} : Set G))) = E ⊓ d.F
    rw [← inf_assoc, inf_eq_left.mpr hEK, ← inf_assoc,
      inf_eq_left.mpr hEH, d.inf_eq]
  have hh := card_mul_card_centralizer_restrict_of_central_binary_pairing
    E C (zpowers z) (zpowers_le.mpr d.z_mem_inf.1) hcomm hZcomm
    ((Nat.card_zpowers z).trans h.involution)
  rw [parrott_derived_centralizer z h, card_subgroupOf_inf,
    card_subgroupOf_inf, hEC, d.inf_card, hEcard, inf_comm (centralizer (C : Set G)) E] at hh
  nlinarith only [hh]

/-- In the quotient-index-two branch, the derived part of the chosen
center has at least four elements. -/
public theorem chosen_center_derived_card_ge_four_of_core_relIndex_two
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    K.relIndex S = 2 → 4 ≤ Nat.card (E ⊓ Z : Subgroup G) := by
  intro H J K E S Z hi
  let C := K ⊓ S
  let A := E ⊓ centralizer (C : Set G)
  have hCcard : Nat.card C = 64 := (d.chosen_card_of_core_relIndex_two h hi).1
  have hAcard : Nat.card A = 8 := by
    have hh := d.chosen_core_derived_centralizer_card_mul h
    change Nat.card A * Nat.card C = 512 at hh
    rw [hCcard] at hh
    omega
  have hnorm (R : Subgroup H) [R.Normal] : H ≤ normalizer (R.map H.subtype : Set G) := by
    have hh := R.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hHK : H ≤ normalizer (K : Set G) := hnorm J
  have hHE : H ≤ normalizer (E : Set G) := by
    have hh := hnorm ((commutator J).map J.subtype)
    simpa only [map_map] using hh
  have hSC : S ≤ normalizer (C : Set G) :=
    (le_inf (inf_le_left.trans hHK) S.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hScentral : S ≤ normalizer (centralizer (C : Set G) : Set G) :=
    hSC.trans (le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer (C : Set G)))
  have hSA : S ≤ normalizer (A : Set G) :=
    (le_inf (inf_le_left.trans hHE) hScentral).trans inf_normalizer_le_normalizer_inf
  have hAS : A ≤ S := by
    intro a ha
    have hEH : E ≤ H := by
      rintro x ⟨j, _, rfl⟩
      exact j.val.property
    refine ⟨hEH ha.1, mem_centralizer_singleton_iff.mpr ?_⟩
    have haC : (d.a : G) ∈ C :=
      ⟨mem_map_of_mem H.subtype d.a_mem_core,
        d.a.property, mem_centralizer_singleton_iff.mpr rfl⟩
    exact (ha.2 (d.a : G) haC).symm
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 (commutator J) := (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  let : IsElementaryAbelian 2 A := {
    toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
      (setLike_mul_comm (s := E) a.property.1 b.property.1)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) a a.property.1)) }
  have hbound := card_le_centralizer_card_sq_of_relIndex_two A C S hSA inf_le_right
    (show C.relIndex S = 2 by rw [inf_relIndex_right]; exact hi)
  have hle : centralizer (S : Set G) ⊓ A ≤ E ⊓ Z := by
    intro a ha
    refine ⟨ha.2.1, ?_⟩
    refine ⟨⟨a, hAS ha.2⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro s
    exact Subtype.ext (ha.1 s s.property)
  have hcard := card_le_of_le hle
  rw [card_subgroupOf_inf, hAcard] at hbound
  have hcases := d.chosen_center_derived_card_cases h
  change Nat.card (E ⊓ Z : Subgroup G) = 2 ∨
    Nat.card (E ⊓ Z : Subgroup G) = 4 ∨ Nat.card (E ⊓ Z : Subgroup G) = 8 at hcases
  rcases hcases with hc | hc | hc
  · rw [hc] at hcard
    nlinarith
  · omega
  · omega

end Stellmacher.Recognition.ParrottSecondElementaryData
