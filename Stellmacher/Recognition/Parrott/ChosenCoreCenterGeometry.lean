module

public import Stellmacher.Recognition.Parrott.ChosenCoreCentralizer

/-!
# Center geometry for the chosen core centralizer

For the supplied involution `a`, put `S = C_G(z) ∩ C_G(a)` and let `Z` be
its ambient center. The inclusion `Z ≤ F` makes the center elementary
abelian. Its two independent elements `z` and `a` give the lower bound
four; its intersection with the derived core has index two. If `F` is
self-normalized by the supplied Sylow, fusion excludes
`Z = F`. Thus its possible orders are four, eight, and sixteen.

Conjugation on `Z` has kernel exactly `S`, giving a faithful realization
of `N_G(S)/S` as an automorphism subgroup. The image of `E` has order two
and its displacement subgroup is exactly `⟨z⟩`. Derived weak closure
forces the normalizer to move `E ∩ Z`. These are the counting and action
interfaces for the local center calculation in Parrott,
*A characterization of the Tits' simple group* (1972), printed p.676,
the paragraph beginning “We claim that Z(S)”.
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] {z : G}

/-- The chosen center is elementary abelian, with the same supplied `F`. -/
public theorem chosen_center_elementary (d : ParrottSecondElementaryData z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    IsElementaryAbelian 2 (center S) := by
  let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
  let : IsElementaryAbelian 2 d.F := d.elementary
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro c
  apply Subtype.ext
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.F) (c : S)
    (d.chosen_centralizer_center.2.2.1 (mem_map_of_mem S.subtype c.property))

/-- Fusion and self-normalization exclude an entire fixed join as the center. -/
public theorem chosen_center_ne_fixed_join [Finite G] (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hconj : IsConj z (d.a : G)) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    (center S).map S.subtype ≠ d.F := by
  intro S heq
  apply d.chosen_centralizer_normalizer_not_le_fixed_join_normalizer h hself hconj
  rw [← heq, d.chosen_centralizer_center_normalizer]

/-- Initial cardinality restrictions, before the exact local center calculation. -/
public theorem chosen_center_card_cases [Finite G] (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hconj : IsConj z (d.a : G)) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    Nat.card (center S) = 4 ∨ Nat.card (center S) = 8 ∨ Nat.card (center S) = 16 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let S := H ⊓ centralizer ({(d.a : G)} : Set G)
  let Z := (center S).map S.subtype
  have hZcard : Nat.card Z = Nat.card (center S) :=
    card_map_of_injective S.subtype_injective
  obtain ⟨hzZ, haZ, hZF, _⟩ := d.chosen_centralizer_center
  have hdiv : Nat.card Z ∣ 32 := d.card ▸ card_dvd_of_le hZF
  have htwo : 2 ≤ Nat.card Z := by
    have hle : zpowers z ≤ Z := zpowers_le.mpr hzZ
    have hc : Nat.card (zpowers z) = 2 := (Nat.card_zpowers z).trans h.involution
    exact hc ▸ card_le_of_le hle
  have hnotTwo : Nat.card Z ≠ 2 := by
    intro hc
    have hZZ : zpowers z = Z := eq_of_le_of_card_ge (zpowers_le.mpr hzZ) (by
      rw [Nat.card_zpowers, h.involution, hc])
    have haE : (d.a : G) ∈ E :=
      (zpowers_le.mpr d.z_mem_inf.1) (hZZ.symm ▸ haZ)
    obtain ⟨a, ha, heq⟩ := haE
    exact d.a_not_mem_derived ⟨a, ha, H.subtype_injective heq⟩
  have hnot32 : Nat.card Z ≠ 32 := by
    intro hc
    exact d.chosen_center_ne_fixed_join h hself hconj
      (eq_of_le_of_card_ge hZF (by rw [hc, d.card]))
  have hcases := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
  rw [show (32 : ℕ).divisors = {1, 2, 4, 8, 16, 32} by decide] at hcases
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcases
  change Nat.card (center S) = 4 ∨ Nat.card (center S) = 8 ∨ Nat.card (center S) = 16
  omega

/-- The part of the chosen center in the derived core is a hyperplane. -/
public theorem chosen_center_derived_index [Finite G] (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    E.relIndex Z = 2 ∧ Nat.card Z = 2 * Nat.card (E ⊓ Z : Subgroup G) := by
  intro H E S Z
  have hFindex : E.relIndex d.F = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (E ⊓ d.F) d.F bot_le inf_le_right
    rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right, d.inf_card, d.card] at hh
    omega
  have hle : E.relIndex Z ≤ 2 := by
    have hh := relIndex_le_of_le_right d.chosen_centralizer_center.2.2.1
      (show E.relIndex d.F ≠ 0 by rw [hFindex]; decide)
    exact hh.trans_eq hFindex
  have hne : E.relIndex Z ≠ 1 := by
    intro heq
    have haE := relIndex_eq_one.mp heq d.chosen_centralizer_center.2.1
    obtain ⟨a, ha, heq⟩ := haE
    exact d.a_not_mem_derived ⟨a, ha, H.subtype_injective heq⟩
  have hpos : E.relIndex Z ≠ 0 := by
    change Nat.card (Z ⧸ E.subgroupOf Z) ≠ 0
    exact Nat.card_pos.ne'
  have hindex : E.relIndex Z = 2 := by omega
  refine ⟨hindex, ?_⟩
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (E ⊓ Z) Z bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right, hindex] at hh
  exact hh.symm.trans (Nat.mul_comm _ _)

/-- The derived core centralizes exactly its fixed-join hyperplane in the
chosen center action. -/
public theorem chosen_center_derived_centralizer (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    E ⊓ centralizer (Z : Set G) = E ⊓ d.F := by
  intro H E S Z
  have hEH : E ≤ H := by
    rintro x ⟨b, _, rfl⟩
    exact b.val.property
  rw [d.chosen_centralizer_center.2.2.2]
  change E ⊓ (H ⊓ centralizer ({(d.a : G)} : Set G)) = E ⊓ d.F
  rw [← inf_assoc, inf_eq_left.mpr hEH, d.inf_eq]

/-- The nontrivial derived-core action on the chosen center has precisely
`⟨z⟩` as its displacement subgroup. -/
public theorem chosen_center_derived_commutator [Finite G]
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    ⁅E, Z⁆ = zpowers z := by
  intro H E S Z
  let J := pCore 2 H
  obtain ⟨hZ, _, _, _, hupper, _, _, _⟩ := parrott_centralizer_structure z h
  have hle : ⁅E, Z⁆ ≤ zpowers z := by
    apply commutator_le.mpr
    rintro e ⟨b, hb, rfl⟩ c hc
    obtain ⟨cH, hcJ, rfl⟩ := d.le_core (d.chosen_centralizer_center.2.2.1 hc)
    have hbc : ⁅b, (⟨cH, hcJ⟩ : J)⁆ ∈ center J := by
      have hbU : b ∈ Subgroup.upperCentralSeries J 2 := hupper ▸ hb
      simpa only [Subgroup.upperCentralSeries_one] using
        (Subgroup.mem_upperCentralSeries_succ_iff.mp hbU (⟨cH, hcJ⟩ : J))
    rw [← hZ]
    exact mem_map_of_mem (H.subtype.comp J.subtype) hbc
  have hne : ⁅E, Z⁆ ≠ ⊥ := by
    intro heq
    have hcentral : Z ≤ centralizer (E : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp heq)
    rw [parrott_derived_centralizer z h] at hcentral
    obtain ⟨a, ha, heq⟩ := hcentral d.chosen_centralizer_center.2.1
    exact d.a_not_mem_derived ⟨a, ha, H.subtype_injective heq⟩
  apply eq_of_le_of_card_ge hle
  rw [Nat.card_zpowers, h.involution]
  exact (one_lt_card_iff_ne_bot _).mpr hne

/-- Weak closure forces the normalizer to move the derived hyperplane of
its center, as well as to move the distinguished involution. -/
public theorem chosen_center_derived_not_normalized [Finite G]
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hconj : IsConj z (d.a : G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    ¬ normalizer (S : Set G) ≤ normalizer ((E ⊓ Z : Subgroup G) : Set G) := by
  intro H E S Z hle
  apply d.chosen_centralizer_normalizer_not_le h hconj
  intro g hg
  have hz : z ∈ E ⊓ Z := ⟨d.z_mem_inf.1, d.chosen_centralizer_center.1⟩
  have hgz : g * z * g⁻¹ ∈ E ⊓ Z := (hle hg z).mp hz
  have heq := hderived _ hgz.1 (isConj_iff.mpr ⟨g, rfl⟩)
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq)

/-- The actual conjugation action on the ambient center, including its kernel
and the resulting faithful realization of the normalizer quotient. -/
public theorem chosen_center_action (d : ParrottSecondElementaryData z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    let N := normalizer (S : Set G)
    ∃ f : N →* MulAut Z,
      (∀ (g : N) (c : Z), (f g c : G) = (g : G) * (c : G) * (g : G)⁻¹) ∧
      f.ker = S.subgroupOf N ∧
      Nonempty ((N ⧸ S.subgroupOf N) ≃* f.range) := by
  intro S Z N
  have hN : N ≤ normalizer (Z : Set G) :=
    le_of_eq d.chosen_centralizer_center_normalizer.symm
  let f : N →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hN)
  have hker : f.ker = S.subgroupOf N := by
    ext g
    change Z.normalizerMonoidHom (inclusion hN g) = 1 ↔ (g : G) ∈ S
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    change (g : G) ∈ centralizer (Z : Set G) ↔ (g : G) ∈ S
    rw [d.chosen_centralizer_center.2.2.2]
  refine ⟨f, fun _ _ => rfl, hker, ?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange f)⟩

/-- The derived core has image of order two in the faithful center action. -/
public theorem chosen_center_derived_action_card [Finite G]
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    let N := normalizer (S : Set G)
    ∀ f : N →* MulAut Z, f.ker = S.subgroupOf N →
      Nat.card ((E.subgroupOf N).map f) = 2 := by
  intro H E S Z N f hker
  have hEN : E ≤ N := d.derived_le_chosen_centralizer_normalizer h
  have hEcard : Nat.card E = 32 := by
    exact (card_map_of_injective (K := commutator (pCore 2 H))
      (f := H.subtype.comp (pCore 2 H).subtype)
      (H.subtype_injective.comp (pCore 2 H).subtype_injective)).trans
        (parrott_centralizer_structure z h).2.2.2.2.2.2.1
  have hES : E ⊓ S = E ⊓ d.F := by
    have hcentral : centralizer (Z : Set G) = S := d.chosen_centralizer_center.2.2.2
    rw [← hcentral]
    exact d.chosen_center_derived_centralizer
  have hindex : S.relIndex E = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (E ⊓ S) E bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, hES, d.inf_card, hEcard] at hh
    omega
  rw [← relIndex_ker, hker, relIndex_subgroupOf hEN, hindex]

end Stellmacher.Recognition.ParrottSecondElementaryData
