module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterGeometry
public import Stellmacher.Recognition.Parrott.CoreCentralizerCounts
public import Stellmacher.Recognition.Parrott.OuterFourFixedSpace

/-!
# Local size constraints for the chosen core centralizer

Retain the supplied involution `a`, Sylow subgroup `T`, and fixed join `F`.
Write `K` for the ambient two-core and `S = C_G(z) ∩ C_G(a)`. The core
centralizer bound gives `|K ∩ S| ≤ 64`, whereas `|S| ≥ 128`. Since `T/K`
has order four, the image of `S` has order two or four and `|S| ≤ 256`.

The part of `Z(S)` in the derived core has order two, four, or eight.
The outer fixed-space bound shows that an intersection of order
at least eight forces the image of `S` modulo the core to have order two.
These bounds use only the original local hypotheses, before any fusion
or normalizer-growth argument.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, properties (a)–(d), and p.676, “We claim that Z(S)”.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The actual core intersection is bounded by the core element-centralizer theorem. -/
public theorem chosen_core_intersection_card_le (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    Nat.card (K ⊓ S : Subgroup G) ≤ 64 := by
  intro H K S
  have hKH : K ≤ H := map_subtype_le _
  have haE : (d.a : G) ∉ (commutator (pCore 2 H)).map
      (H.subtype.comp (pCore 2 H).subtype) := by
    rintro ⟨a, ha, heq⟩
    exact d.a_not_mem_derived ⟨a, ha, H.subtype_injective heq⟩
  have hbound := parrott_core_element_centralizer_card_le_sixty_four z h
    (d.a : G) (mem_map_of_mem H.subtype d.a_mem_core) haE
  let C := (centralizer ({(d.a : G)} : Set G)).subgroupOf K
  let i : (K ⊓ S : Subgroup G) → C := fun x => ⟨⟨x, x.property.1⟩, x.property.2.2⟩
  have hi : Function.Bijective i := by
    constructor
    · intro x y hxy
      exact Subtype.ext (congrArg (fun c : C => ((c : K) : G)) hxy)
    · intro c
      exact ⟨⟨c, (c : K).property, hKH (c : K).property, c.property⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective i hi)).le.trans hbound

/-- The supplied Sylow has index four over the actual core. -/
public theorem core_relIndex_sylow (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    ((pCore 2 H).map H.subtype).relIndex (d.sylow : Subgroup G) = 4 := by
  intro H
  let J := pCore 2 H
  let K := J.map H.subtype
  have hKT : K ≤ (d.sylow : Subgroup G) := by
    rw [d.sylow_map]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal d.localSylow)
  have hKcard : Nat.card K = 512 :=
    (card_map_of_injective H.subtype_injective).trans h.core_card
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) K (d.sylow : Subgroup G)
    bot_le hKT
  rw [relIndex_bot_left, relIndex_bot_left, hKcard, d.sylow_card h] at hc
  change K.relIndex (d.sylow : Subgroup G) = 4
  omega

/-- The chosen centralizer covers at least the order-two subgroup modulo the core. -/
public theorem chosen_core_relIndex_bounds (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    2 ≤ K.relIndex S ∧ K.relIndex S ≤ 4 := by
  intro H K S
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ S) S bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right] at hc
  have hcore := d.chosen_core_intersection_card_le h
  have hlarge := d.chosen_centralizer_card_ge h
  change Nat.card (K ⊓ S : Subgroup G) ≤ 64 at hcore
  change 128 ≤ Nat.card S at hlarge
  refine ⟨?_, ?_⟩
  · by_contra hlt
    have hi : K.relIndex S ≤ 1 := by omega
    nlinarith
  · have hindex := d.core_relIndex_sylow h
    exact (relIndex_le_of_le_right (d.chosen_centralizer_le_sylow h)
      (show K.relIndex (d.sylow : Subgroup G) ≠ 0 by rw [hindex]; decide)).trans_eq hindex

/-- There are exactly two possibilities for the image of S modulo the core. -/
public theorem chosen_core_relIndex_cases (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    K.relIndex S = 2 ∨ K.relIndex S = 4 := by
  intro H K S
  obtain ⟨hl, hu⟩ := d.chosen_core_relIndex_bounds h
  change 2 ≤ K.relIndex S at hl
  change K.relIndex S ≤ 4 at hu
  have hd : K.relIndex S ∣ 2048 := by
    have hs := card_dvd_of_le (d.chosen_centralizer_le_sylow h)
    rw [d.sylow_card h] at hs
    exact (relIndex_dvd_card K S).trans hs
  interval_cases hi : K.relIndex S <;> simp_all

/-- The actual centralizer has order between 128 and 256. -/
public theorem chosen_centralizer_card_bounds (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    128 ≤ Nat.card S ∧ Nat.card S ≤ 256 := by
  intro S
  let K := (pCore 2 (centralizer ({z} : Set G))).map
    (centralizer ({z} : Set G)).subtype
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ S) S bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right] at hc
  have hcore := d.chosen_core_intersection_card_le h
  have hindex := (d.chosen_core_relIndex_bounds h).2
  change Nat.card (K ⊓ S : Subgroup G) ≤ 64 at hcore
  change K.relIndex S ≤ 4 at hindex
  exact ⟨d.chosen_centralizer_card_ge h, by nlinarith⟩

/-- Even without fusion, the fixed join cannot be the entire center:
its self-centralization would make S have order 32. -/
public theorem chosen_center_ne_fixed_join_local (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    (center S).map S.subtype ≠ d.F := by
  intro S heq
  have hc := d.chosen_centralizer_center.2.2.2
  change centralizer (((center S).map S.subtype : Subgroup G) : Set G) = S at hc
  rw [heq, d.centralizer_eq] at hc
  have hh := d.chosen_centralizer_card_ge h
  change 128 ≤ Nat.card S at hh
  rw [← hc, d.card] at hh
  omega

/-- Before the local action calculation, the derived part of the center has
one of three possible orders; this statement does not use fusion. -/
public theorem chosen_center_derived_card_cases (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    Nat.card (E ⊓ Z : Subgroup G) = 2 ∨ Nat.card (E ⊓ Z : Subgroup G) = 4 ∨
      Nat.card (E ⊓ Z : Subgroup G) = 8 := by
  intro H E S Z
  have hUF : E ⊓ Z ≤ E ⊓ d.F := inf_le_inf_left _ d.chosen_centralizer_center.2.2.1
  have hd : Nat.card (E ⊓ Z : Subgroup G) ∣ 16 := d.inf_card ▸ card_dvd_of_le hUF
  have hz : zpowers z ≤ E ⊓ Z := zpowers_le.mpr
    ⟨d.z_mem_inf.1, d.chosen_centralizer_center.1⟩
  have hl : 2 ≤ Nat.card (E ⊓ Z : Subgroup G) := by
    have hh := card_le_of_le hz
    rwa [Nat.card_zpowers, h.involution] at hh
  have hc := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  rw [show (16 : ℕ).divisors = {1, 2, 4, 8, 16} by decide] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  have hne : Nat.card (E ⊓ Z : Subgroup G) ≠ 16 := by
    intro h16
    have hZcard := d.chosen_center_derived_index.2
    change Nat.card Z = 2 * Nat.card (E ⊓ Z : Subgroup G) at hZcard
    rw [h16] at hZcard
    apply d.chosen_center_ne_fixed_join_local h
    exact eq_of_le_of_card_ge d.chosen_centralizer_center.2.2.1 (by
      change Nat.card d.F ≤ Nat.card Z
      rw [d.card, hZcard])
  omega

/-- A large derived part of the center forces precisely index two over the core. -/
public theorem chosen_core_relIndex_eq_two_of_center_derived_card_ge_eight
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    8 ≤ Nat.card (E ⊓ Z : Subgroup G) → K.relIndex S = 2 := by
  intro H K E S Z hcard
  have hcentral : S ≤ centralizer ((E ⊓ Z : Subgroup G) : Set G) := by
    intro s hs c hc
    obtain ⟨cS, hcS, heq⟩ := hc.2
    rw [← heq]
    exact (congrArg S.subtype (mem_center_iff.mp hcS ⟨s, hs⟩)).symm
  have hu := parrott_two_subgroup_centralizer_relIndex_le_two z h S (E ⊓ Z)
    inf_le_left (d.chosen_centralizer_isPGroup h) inf_le_left hcard hcentral
  exact Nat.le_antisymm hu (d.chosen_core_relIndex_bounds h).1

/-- In the index-two branch both centralizer orders are forced. -/
public theorem chosen_card_of_core_relIndex_two (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    K.relIndex S = 2 → Nat.card (K ⊓ S : Subgroup G) = 64 ∧ Nat.card S = 128 := by
  intro H K S hi
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ S) S bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right, hi] at hc
  have hcore := d.chosen_core_intersection_card_le h
  have hlarge := d.chosen_centralizer_card_ge h
  change Nat.card (K ⊓ S : Subgroup G) ≤ 64 at hcore
  change 128 ≤ Nat.card S at hlarge
  omega

/-- In the covering branch the only outstanding possibility, besides order
four, is a derived center consisting just of the distinguished involution. -/
public theorem chosen_center_derived_card_le_four_of_core_relIndex_four
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    K.relIndex S = 4 → Nat.card (E ⊓ Z : Subgroup G) ≤ 4 := by
  intro H K E S Z hi
  by_contra hgt
  have hcases := d.chosen_center_derived_card_cases h
  change Nat.card (E ⊓ Z : Subgroup G) = 2 ∨
    Nat.card (E ⊓ Z : Subgroup G) = 4 ∨ Nat.card (E ⊓ Z : Subgroup G) = 8 at hcases
  have h8 : 8 ≤ Nat.card (E ⊓ Z : Subgroup G) := by omega
  have hh := d.chosen_core_relIndex_eq_two_of_center_derived_card_ge_eight h h8
  change K.relIndex S = 2 at hh
  omega

end Stellmacher.Recognition.ParrottSecondElementaryData
