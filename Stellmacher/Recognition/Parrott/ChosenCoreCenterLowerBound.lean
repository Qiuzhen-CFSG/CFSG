module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterIndexTwo
public import Stellmacher.Recognition.Parrott.ChosenCoreCoveringFixed
public import Stellmacher.Recognition.Parrott.ChosenCoreCoveringLift
public import Stellmacher.Recognition.Parrott.ChosenCoreCoveringCompatibleLift
public import Stellmacher.Recognition.Parrott.OuterFourEighthPower
public import Theory.GroupTheory.FourthPowerCentralizerCard

/-!
# Reduction of the chosen-center lower bound to the covering action

The index-two branch is already settled by the central commutator pairing.
In the covering branch, choose an element of S of order four modulo the
core. If its fourth power centralizes E and its E-fixed subgroup lies in
Z(S), the fourth-power fixed-point count excludes |E ∩ Z(S)|=2.

The fixed-subgroup containment is established in `ChosenCoreCoveringFixed`.
The outstanding input is a single actor in S satisfying both the quotient
order and fourth-power conditions. `ChosenCoreCoveringLift` supplies a
controlled actor in the Sylow subgroup, but does not establish that it
centralizes the supplied a. The reductions below keep this compatibility
condition explicit; quotient order alone does not control a lift's order.

The final counterexample reduction below records the actual obstruction:
failure supplies an actor of actual order eight in S, with just two fixed
elements in E, whose fourth power is a or az. Conversely, excluding just
these actors suffices for the lower bound. This is weaker than controlling
all lifts of quotient order four in H.
Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the parenthetical lower bound on p.676.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The covering branch supplies an element of the actual centralizer
whose image has order four. No order assertion about the lift is made. -/
public theorem chosen_centralizer_exists_quotient_order_four
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    (J.map H.subtype).relIndex S = 4 →
      ∃ y : H, (y : G) ∈ S ∧ orderOf (QuotientGroup.mk' J y) = 4 := by
  intro H J S hi
  have hSH : S ≤ H := inf_le_left
  let L := S.subgroupOf H
  let q := QuotientGroup.mk' J
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let f := e.toMonoidHom.comp q
  let A := L.map f
  have hp : IsPGroup 2 S := d.chosen_centralizer_isPGroup h
  have hLtwo : IsPGroup 2 L := hp.of_injective
    (subgroupOfEquivOfLe hSH).toMonoidHom (subgroupOfEquivOfLe hSH).injective
  let : IsCyclic A :=
    (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ A (hLtwo.map f)).1
  have hrel : (J.map H.subtype).relIndex S = Nat.card A := by
    calc
      _ = (J.map H.subtype).relIndex (L.map H.subtype) := by
        rw [map_subgroupOf_eq_of_le hSH]
      _ = J.relIndex L := relIndex_map_map_of_injective J L H.subtype_injective
      _ = Nat.card (L.map q) := by
        have hh := relIndex_ker L q
        rw [QuotientGroup.ker_mk'] at hh
        exact hh
      _ = Nat.card A := by
        have hh := card_map_of_injective (K := L.map q) (f := e.toMonoidHom) e.injective
        rw [map_map] at hh
        exact hh.symm
  have hA : Nat.card A = 4 := hrel.symm.trans hi
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic A)
  rw [hA] at ha
  obtain ⟨y, hy, hya⟩ := a.property
  refine ⟨y, hy, ?_⟩
  have hf : orderOf (f y) = 4 := by
    rw [hya]
    exact (orderOf_injective A.subtype A.subtype_injective a).trans ha
  simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.orderOf_eq] using hf

/-- A fixed subgroup lying in the chosen center gives the lower bound
as soon as the fourth power of its actor centralizes the derived core. -/
public theorem chosen_center_derived_card_ge_four_of_fixed_subgroup
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    ∀ y : H, (y : G) ^ 4 ∈ centralizer (E : Set G) →
      E ⊓ centralizer ({(y : G)} : Set G) ≤ Z →
        4 ≤ Nat.card (E ⊓ Z : Subgroup G) := by
  intro H J E S Z y hy4 hfixed
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, _, _, _, _, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := commutator J)
      (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hHE : H ≤ normalizer (E : Set G) := by
    have hh := ((commutator J).map J.subtype).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype,
      map_map] using hh
  have hl := two_lt_centralizer_card_of_card_thirty_two_of_fourth_power
    E hEcard (y : G) (hHE y.property) hy4
  have hc := card_le_of_le (le_inf inf_le_left hfixed)
  have hcases := d.chosen_center_derived_card_cases h
  change Nat.card (E ⊓ Z : Subgroup G) = 2 ∨
    Nat.card (E ⊓ Z : Subgroup G) = 4 ∨ Nat.card (E ⊓ Z : Subgroup G) = 8 at hcases
  omega

/-- Assembly using the remaining covering-branch action input. The
unconditional lower bound is obtained once that input is established from
the original local hypotheses. -/
public theorem chosen_center_derived_card_ge_four_of_covering_action
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    ((J.map H.subtype).relIndex S = 4 → ∃ y : H,
      (y : G) ^ 4 ∈ centralizer (E : Set G) ∧
      E ⊓ centralizer ({(y : G)} : Set G) ≤ Z) →
        4 ≤ Nat.card (E ⊓ Z : Subgroup G) := by
  intro H J E S Z hcover
  rcases d.chosen_core_relIndex_cases h with hi | hi
  · exact d.chosen_center_derived_card_ge_four_of_core_relIndex_two h hi
  · obtain ⟨y, hy4, hyfixed⟩ := hcover hi
    exact d.chosen_center_derived_card_ge_four_of_fixed_subgroup h y hy4 hyfixed

/-- An actor in the chosen centralizer satisfying both action conditions
excludes a two-element derived center. All conditions concern the same actor. -/
public theorem chosen_center_derived_card_ge_four_of_centralizing_lift
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    ∀ y : H, (y : G) ∈ S → orderOf (QuotientGroup.mk' J y) = 4 →
      (y : G) ^ 4 ∈ centralizer (E : Set G) →
        4 ≤ Nat.card (E ⊓ Z : Subgroup G) := by
  intro H J E S Z y hyS hyOrder hyPower
  exact d.chosen_center_derived_card_ge_four_of_fixed_subgroup h y hyPower
    (d.chosen_covering_fixed_le_center h y hyS hyOrder)

/-- Final reduction to compatibility of the covering lift with the supplied
involution. A lift merely in the Sylow subgroup does not discharge this premise. -/
public theorem chosen_center_derived_card_ge_four_of_compatible_covering_lift
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    ((J.map H.subtype).relIndex S = 4 → ∃ y : H,
      (y : G) ∈ S ∧ orderOf (QuotientGroup.mk' J y) = 4 ∧
      (y : G) ^ 4 ∈ centralizer (E : Set G)) →
        4 ≤ Nat.card (E ⊓ Z : Subgroup G) := by
  intro H J E S Z hcover
  rcases d.chosen_core_relIndex_cases h with hi | hi
  · exact d.chosen_center_derived_card_ge_four_of_core_relIndex_two h hi
  · obtain ⟨y, hyS, hyOrder, hyPower⟩ := hcover hi
    exact d.chosen_center_derived_card_ge_four_of_centralizing_lift h y hyS hyOrder hyPower

/-- A failure of the lower bound produces an actual order-eight actor in
the supplied centralizer, fixing precisely two derived elements. Its fourth
power is one of the two specified involutions; all assertions concern the
same actor. -/
public theorem chosen_center_small_exists_order_eight_root
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    Nat.card (E ⊓ Z : Subgroup G) < 4 →
      (J.map H.subtype).relIndex S = 4 ∧
      ∃ y : H, (y : G) ∈ S ∧ orderOf (QuotientGroup.mk' J y) = 4 ∧
        orderOf y = 8 ∧
        Nat.card (E ⊓ centralizer ({(y : G)} : Set G) : Subgroup G) = 2 ∧
        ((y : G) ^ 4 = (d.a : G) ∨ (y : G) ^ 4 = (d.a : G) * z) := by
  intro H J E S Z hsmall
  have hi : (J.map H.subtype).relIndex S = 4 := by
    rcases d.chosen_core_relIndex_cases h with hi | hi
    · have hh := d.chosen_center_derived_card_ge_four_of_core_relIndex_two h hi
      change 4 ≤ Nat.card (E ⊓ Z : Subgroup G) at hh
      omega
    · exact hi
  obtain ⟨y, hyS, hyOrder, hyEight⟩ :=
    d.chosen_covering_exists_lift_eighth_power_eq_one h hi
  let C := E ⊓ centralizer ({(y : G)} : Set G)
  have hCZ : C ≤ E ⊓ Z :=
    le_inf inf_le_left (d.chosen_covering_fixed_le_center h y hyS hyOrder)
  have hcases := d.chosen_center_derived_card_cases h
  change Nat.card (E ⊓ Z : Subgroup G) = 2 ∨
    Nat.card (E ⊓ Z : Subgroup G) = 4 ∨
    Nat.card (E ⊓ Z : Subgroup G) = 8 at hcases
  have hCupper : Nat.card C ≤ 2 := by
    have hh := card_le_of_le hCZ
    omega
  have hzC : zpowers z ≤ C := by
    apply zpowers_le.mpr
    exact ⟨d.z_mem_inf.1, mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp y.property).symm⟩
  have hClower : 2 ≤ Nat.card C := by
    have hh := card_le_of_le hzC
    rwa [Nat.card_zpowers, h.involution] at hh
  have hroot := d.chosen_centralizer_small_fixed_fourth_power h y hyS hCupper
  have haE : (d.a : G) ∉ E := by
    rintro ⟨a, ha, heq⟩
    exact d.a_not_mem_derived ⟨a, ha, H.subtype_injective heq⟩
  have hyFour : y ^ 4 ∉ (commutator J).map J.subtype := by
    intro hmem
    have hmemE := mem_map_of_mem H.subtype hmem
    rw [map_map] at hmemE
    change (y : G) ^ 4 ∈ E at hmemE
    rcases hroot with heq | heq
    · exact haE (heq ▸ hmemE)
    · exact haE ((E.mul_mem_cancel_right d.z_mem_inf.1).mp (heq ▸ hmemE))
  have hyActual :=
    (parrott_outer_four_bad_eighth_power_data z h y hyOrder hyEight hyFour).1
  exact ⟨hi, y, hyS, hyOrder, hyActual, Nat.le_antisymm hCupper hClower, hroot⟩

/-- Final assembly needs only exclude order-eight roots in the original
chosen centralizer with the smallest possible derived fixed subgroup.
No conclusion about other lifts is required. -/
public theorem chosen_center_derived_card_ge_four_of_no_order_eight_roots
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    (∀ y : H, (y : G) ∈ S → orderOf (QuotientGroup.mk' J y) = 4 →
      orderOf y = 8 →
      Nat.card (E ⊓ centralizer ({(y : G)} : Set G) : Subgroup G) = 2 →
      (y : G) ^ 4 ≠ (d.a : G) ∧ (y : G) ^ 4 ≠ (d.a : G) * z) →
      4 ≤ Nat.card (E ⊓ Z : Subgroup G) := by
  intro H J E S Z hroots
  by_contra hsmall
  obtain ⟨_, y, hyS, hyOrder, hyActual, hyFixed, hroot⟩ :=
    d.chosen_center_small_exists_order_eight_root h (Nat.not_le.mp hsmall)
  rcases hroot with heq | heq
  · exact (hroots y hyS hyOrder hyActual hyFixed).1 heq
  · exact (hroots y hyS hyOrder hyActual hyFixed).2 heq

end Stellmacher.Recognition.ParrottSecondElementaryData
