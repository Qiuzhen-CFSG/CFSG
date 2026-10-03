module

public import Stellmacher.Recognition.Parrott.SecondElementary
public import Stellmacher.Recognition.Parrott.CoreCentralizerCounts

/-!
# The join of Parrott's two elementary subgroups

For the supplied second elementary subgroup F and the ambient derived core E,
put A=E∨F. The fixed-join description identifies A with ⟨a,E⟩. Its order is
64 and its derived subgroup is ⟨z⟩. Moreover C_G(E∩F)=A: an element fixing
the hyperplane E∩F has square in E, hence lies in the core by the outer
fixed-space bound; the central commutator pairing then gives order 64.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the final paragraph of p.676.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem core_derived_image (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    E ⊔ d.F = E ⊔ zpowers (d.a : G) := by
  intro H J E
  rw [d.fixed_join, sup_comm (zpowers _), ← sup_assoc,
    sup_eq_left.mpr (show E ⊓ centralizer ({(d.a : G)} : Set G) ≤ E from inf_le_left)]

omit [Finite G] in
private theorem core_derived_normalized :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    H ≤ normalizer (E : Set G) := by
  intro H J E
  let DH := (commutator J).map J.subtype
  have hh := le_normalizer_map (H := DH) H.subtype
  rw [normalizer_eq_top] at hh
  simpa only [← MonoidHom.range_eq_map, range_subtype, DH, map_map] using hh

/-- The join A=E∨F has order 64. -/
public theorem elementary_join_card (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    Nat.card (E ⊔ d.F : Subgroup G) = 64 := by
  intro H J E
  have haE : (d.a : G) ∉ E := by
    rintro ⟨b, hb, heq⟩
    exact d.a_not_mem_derived ⟨b, hb, H.subtype_injective heq⟩
  have ha2 : (d.a : G) ^ 2 = 1 := by
    have ho : orderOf (d.a : G) = 2 := (Subgroup.orderOf_coe d.a).trans d.a_order
    exact ho ▸ pow_orderOf_eq_one (d.a : G)
  have hc : Nat.card E = 32 := by
    exact (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans
        (parrott_centralizer_structure z h).2.2.2.2.2.2.1
  rw [d.core_derived_image, card_sup_zpowers_of_normalizing_involution E (d.a : G)
    ha2 haE (core_derived_normalized d.a.property), hc]

/-- The actual ambient image of A′ is the original involution line. -/
public theorem elementary_join_commutator (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let A := E ⊔ d.F
    (commutator A).map A.subtype = zpowers z := by
  intro H J E A
  let embed := H.subtype.comp J.subtype
  let D := commutator J
  let a : J := ⟨d.a, d.a_mem_core⟩
  let A₀ := D ⊔ zpowers a
  have hmap : A₀.map embed = A := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    exact (d.core_derived_image).symm
  obtain ⟨hcenter, _, _, _, hUpper, _, _, _⟩ := parrott_centralizer_structure z h
  let q := QuotientGroup.mk' (center J)
  have hDcentral : D.map q ≤ center (J ⧸ center J) := by
    rintro x ⟨b, hb, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (center J) y
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hcomm : ⁅D, ⊤⁆ ≤ center J := by
      rw [show D = Subgroup.upperCentralSeries J 2 from hUpper]
      simpa only [Subgroup.upperCentralSeries_one] using
        commutator_upperCentralSeries_top_le J 1
    exact hcomm (commutator_mem_commutator hb (mem_top c))
  have hqcomm : ⁅A₀.map q, A₀.map q⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [show A₀.map q = D.map q ⊔ zpowers (q a) by
      rw [show A₀ = D ⊔ zpowers a from rfl, Subgroup.map_sup, MonoidHom.map_zpowers]]
    apply sup_le
    · exact hDcentral.trans (center_le_centralizer _)
    · apply le_centralizer_iff.mpr
      exact sup_le (hDcentral.trans (center_le_centralizer _)) (le_centralizer _)
  have hbound₀ : ⁅A₀, A₀⁆ ≤ center J := by
    have hh : (⁅A₀, A₀⁆).map q = ⊥ := (map_commutator _ _ _).trans hqcomm
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hh
  have hbound : ⁅A, A⁆ ≤ zpowers z := by
    have hm := map_mono (f := embed) hbound₀
    rwa [map_commutator, hmap, hcenter] at hm
  have hne : ⁅A, A⁆ ≠ ⊥ := by
    intro heq
    have hAA := commutator_eq_bot_iff_le_centralizer.mp heq
    have haE : (d.a : G) ∈ E := by
      have hCE : centralizer (E : Set G) = E := parrott_derived_centralizer z h
      rw [← hCE]
      exact centralizer_le (show E ≤ A from le_sup_left)
        (hAA ((le_sup_right : d.F ≤ A) (by
          rw [d.fixed_join]
          exact Subgroup.mem_sup_left (mem_zpowers (d.a : G)))))
    obtain ⟨b, hb, heq⟩ := haE
    exact d.a_not_mem_derived ⟨b, hb, H.subtype_injective heq⟩
  rw [map_subtype_commutator]
  apply eq_of_le_of_card_ge hbound
  have hc : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, h.involution]
  rw [hc]
  exact Nat.succ_le_of_lt ((one_lt_card_iff_ne_bot _).mpr hne)

/-- The fixed hyperplane E∩F has centralizer exactly A=E∨F. -/
public theorem elementary_inf_centralizer (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    centralizer (E ⊓ d.F : Set G) = E ⊔ d.F := by
  intro H J E
  let K := J.map H.subtype
  let Z := E ⊓ d.F
  let C := centralizer (Z : Set G)
  let A := E ⊔ d.F
  obtain ⟨_, _, _, _, _, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hEJ : E ≤ K := by
    rw [show E = ((commutator J).map J.subtype).map H.subtype from (map_map _ _ _).symm]
    exact map_mono (map_subtype_le _)
  have hCH : C ≤ H := by
    intro c hc
    exact mem_centralizer_singleton_iff.mpr (hc z d.z_mem_inf).symm
  have hHN : H ≤ normalizer (E : Set G) := core_derived_normalized
  have hCE : centralizer (E : Set G) = E := parrott_derived_centralizer z h
  have hZcard : Nat.card (Z.subgroupOf E) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show Z ≤ E from inf_le_left)).toEquiv).trans d.inf_card
  have hZindex : (Z.subgroupOf E).index = 2 := by
    have hh := (Z.subgroupOf E).index_mul_card
    rw [hZcard, hEcard] at hh
    omega
  have hCK : C ≤ K := by
    intro c hc
    let cH : H := ⟨c, hCH hc⟩
    let cN : normalizer (E : Set G) := ⟨c, hHN (hCH hc)⟩
    let b : MulAut E := E.normalizerMonoidHom cN
    have hZfixed : Z.subgroupOf E ≤ FixedPoints.subgroup (zpowers b) E := by
      intro e he mover
      have hb : b e = e := by
        apply Subtype.ext
        change c * (e : G) * c⁻¹ = (e : G)
        exact mul_inv_eq_iff_eq_mul.mpr (hc (e : G) he).symm
      exact smul_eq_self_of_mem_zpowers mover.property hb
    have hb2 : b ^ 2 = 1 := MulAut.square_eq_one_of_fixed_index_dvd_two b
      ((index_dvd_of_le hZfixed).trans (by rw [hZindex]))
    have hc2E : c ^ 2 ∈ E := by
      have hh : cN ^ 2 ∈ E.normalizerMonoidHom.ker := by
        change E.normalizerMonoidHom (cN ^ 2) = 1
        rw [map_pow]
        exact hb2
      rw [normalizerMonoidHom_ker] at hh
      exact hCE ▸ hh
    have hc2J : cH ^ 2 ∈ J := by
      obtain ⟨x, hx, hxc⟩ := hEJ hc2E
      exact (show x = cH ^ 2 from Subtype.ext hxc) ▸ hx
    by_contra hcK
    have hcJ : cH ∉ J := fun hh => hcK (mem_map_of_mem H.subtype hh)
    have hbound := parrott_outer_square_mem_core_fixed_card_le z h cH hc2J hcJ
    have hZC : Z.subgroupOf E ≤ (centralizer ({c} : Set G)).subgroupOf E := by
      intro e he
      exact mem_centralizer_singleton_iff.mpr (hc (e : G) he)
    have hh := card_le_of_le hZC
    rw [hZcard] at hh
    change Nat.card ((centralizer ({c} : Set G)).subgroupOf E) ≤ 8 at hbound
    omega
  have hCcard : Nat.card C = 64 := by
    have hh := parrott_core_subgroup_centralizer_card z h Z
      (zpowers_le.mpr d.z_mem_inf) inf_le_left
    have heq : Nat.card (C.subgroupOf K) = Nat.card C :=
      Nat.card_congr (subgroupOfEquivOfLe hCK).toEquiv
    change Nat.card Z * Nat.card (C.subgroupOf K) = 1024 at hh
    rw [show Nat.card Z = 16 from d.inf_card, heq] at hh
    omega
  have hAC : A ≤ C := sup_le
    ((le_centralizer E).trans (centralizer_le inf_le_left))
    ((le_centralizer d.F).trans (centralizer_le inf_le_right))
  exact (eq_of_le_of_card_ge hAC (by rw [hCcard, d.elementary_join_card h])).symm

/-- Every element of A of square one belongs to one of the two elementary
subgroups. In the outer coset, squaring forces its E-component to fix a. -/
public theorem elementary_join_involution (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ x ∈ E ⊔ d.F, x ^ 2 = 1 → x ∈ E ∨ x ∈ d.F := by
  classical
  intro H J E x hx hx2
  obtain ⟨_, _, _, _, _, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have ha2 : orderOf (d.a : G) = 2 := (Subgroup.orderOf_coe d.a).trans d.a_order
  have haN : zpowers (d.a : G) ≤ normalizer (E : Set G) :=
    zpowers_le.mpr (core_derived_normalized d.a.property)
  rw [d.core_derived_image] at hx
  have hprod : x ∈ (E : Set G) * (zpowers (d.a : G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left E (zpowers (d.a : G)) haN]
    exact hx
  obtain ⟨e, he, b, hb, rfl⟩ := hprod
  change b ∈ zpowers (d.a : G) at hb
  rw [mem_zpowers_iff_mem_range_orderOf, ha2] at hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · exact Or.inl (by simpa using he)
  · simp only [pow_one] at hx2 ⊢
    right
    have he2 : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian e he
    have haPow : (d.a : G) ^ 2 = 1 := ha2 ▸ pow_orderOf_eq_one (d.a : G)
    have hcomm : e * (d.a : G) = (d.a : G) * e := by
      have hh := inv_eq_of_mul_eq_one_right (show (e * (d.a : G)) * (e * (d.a : G)) = 1 by
        simpa only [pow_two] using hx2)
      rw [mul_inv_rev,
        inv_eq_of_mul_eq_one_right (show (d.a : G) * (d.a : G) = 1 by
          simpa only [pow_two] using haPow),
        inv_eq_of_mul_eq_one_right (show e * e = 1 by simpa only [pow_two] using he2)] at hh
      exact hh.symm
    rw [d.fixed_join]
    exact mul_mem (Subgroup.mem_sup_right ⟨he, mem_centralizer_singleton_iff.mpr hcomm⟩)
      (Subgroup.mem_sup_left (mem_zpowers (d.a : G)))

end Stellmacher.Recognition.ParrottSecondElementaryData
