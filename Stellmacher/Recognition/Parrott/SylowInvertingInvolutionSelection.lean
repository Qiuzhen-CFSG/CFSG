module

public import Stellmacher.Recognition.Parrott.SylowCoreSelectionData
public import Stellmacher.Recognition.Parrott.SecondCentralizerOriginalCoreCount

/-!
# An original-core involution giving Parrott's equation (3)

Select an involution in the supplied Sylow T outside the normalizer omega
subgroup that inverts the supplied three-subgroup Q. The outside-omega
criterion puts it in the original core J, and its centralization of v puts
it outside K = C_T(t). It normalizes C_K(Q) = ⟨b⟩. Its centralizer in J is
an elementary fixed join, so it cannot centralize the order-four element b;
therefore it inverts b. Finally J′ = Z₂(J) and Z(J) = ⟨z⟩ turn its
noncentralization of t into [d,t] = z.

All witnesses z,t,v,F,T,Q,b are retained. No action frame is needed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.678, paragraph leading to equation (3).
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

private theorem core_derived_pc (h : ParrottCentralizerHypotheses z)
    {g k : G} (hg : g ∈ J) (hk : k ∈ E) :
    Tits.parrottCommutator g k ∈ zpowers z := by
  let K := pCore 2 H
  let embed := (H).subtype.comp K.subtype
  obtain ⟨gH, hgK, rfl⟩ := hg
  obtain ⟨kK, hkK, rfl⟩ := hk
  obtain ⟨hZ, _, _, _, hUpper, _, _, _⟩ := parrott_centralizer_structure z h
  have hcomm : ⁅commutator K, (⊤ : Subgroup K)⁆ ≤ center K := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      commutator_upperCentralSeries_top_le K 1
  have hh := mem_map_of_mem embed (hcomm (commutator_mem_commutator
    ((commutator K).inv_mem hkK) (show (⟨gH, hgK⟩ : K)⁻¹ ∈ ⊤ from mem_top _)))
  rw [hZ] at hh
  have heq : embed ⁅kK⁻¹, (⟨gH, hgK⟩ : K)⁻¹⁆ =
      (Tits.parrottCommutator (gH : G) (embed kK))⁻¹ := by
    simp only [commutatorElement_def,
      Tits.parrottCommutator, mul_inv_rev, inv_inv, map_mul, map_inv]
    change (embed kK)⁻¹ * (gH : G)⁻¹ * embed kK * (gH : G) = _
    group
  rw [heq] at hh
  simpa only [inv_inv, embed, K, Subgroup.coe_subtype] using (zpowers z).inv_mem hh


/-- The supplied three-centralizer generator admits an original-core
involution satisfying both commutator identities in equation (3). -/
public theorem ParrottNormalizerFusionData.exists_three_generator_involution
    [IsSimpleGroup G] (_hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z)
    (n : ParrottNormalizerFusionData e) :
    ∃ d : G, d ∈ J ∧ d ^ 2 = 1 ∧
      Tits.parrottCommutator d n.b = n.v ∧
      Tits.parrottCommutator d n.t = z := by
  classical
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let X := K.map N.subtype
  let A := (n.Q : Subgroup N).map N.subtype
  obtain ⟨d, hdP, hd2, hdW, hinv⟩ :=
    e.exists_normalizer_fixed_outer_involution_inverting_three h hN
      n.sylow_lt_normalizer n.Q n.v n.v_order n.elementary_fixed
  have hdJ : d ∈ J := by
    by_contra hout
    exact hdW (e.sylow_outer_involution_mem_normalizer_omega h hN
      n.sylow_lt_normalizer d hdP.1 hd2 hout)
  have hdX : d ∉ X := by
    intro hdX
    exact hdW ((e.normalizer_core_fixed_involution_centralizer h hN
      n.sylow_lt_normalizer n.Q n.v n.v_order n.elementary_fixed) ▸ ⟨hdX, hdP.2⟩)
  have hdsq : d ^ 2 = 1 := hd2 ▸ pow_orderOf_eq_one d
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hdsq)
  have hdA : d ∈ normalizer (A : Set G) := by
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · intro ha
      rw [hinv a ha]
      exact A.inv_mem ha
    · intro ha
      have hh := A.inv_mem ha
      rw [← hinv (d * a * d⁻¹) ha] at hh
      have heq : d * (d * a * d⁻¹) * d⁻¹ = a := by
        calc
          _ = (d * d) * a * (d * d)⁻¹ := by group
          _ = a := by rw [← pow_two, hdsq]; simp
      rwa [heq] at hh
  have hdNX : d ∈ normalizer (X : Set G) := by
    apply le_normalizer_map N.subtype
    exact mem_map_of_mem N.subtype ((normalizer_eq_top K).symm ▸
      (show (⟨d, e.sylow_le_normalizer hdP.1⟩ : N) ∈ ⊤ from mem_top _))
  have hdB : d ∈ normalizer (zpowers n.b : Set G) := by
    rw [← n.core_fixed]
    exact inf_normalizer_le_normalizer_inf
      ⟨hdNX, normalizer_le_normalizer_centralizer A hdA⟩
  have hbfix : n.b ∈ X ⊓ centralizer (A : Set G) := by
    rw [n.core_fixed]
    exact mem_zpowers _
  have hbJ : n.b ∈ J := e.sylow_subgroup_commutator_le_core h X n.core_le_sylow
    (n.core_fixed_le_derived hbfix)
  have hnotcomm : ¬ Commute d n.b := by
    intro hc
    obtain ⟨f, hfa, _, _, _, _⟩ := e.normalizer_fixed_outside_omega_fixed_join
      h hN n.sylow_lt_normalizer n.Q n.v n.v_order n.elementary_fixed d hdP hd2 hdW
    have hbF : n.b ∈ f.F := by
      rw [← f.original_core_centralizer_eq_fixed_join h, hfa]
      exact ⟨hbJ, mem_centralizer_singleton_iff.mpr hc.symm.eq⟩
    let : IsElementaryAbelian 2 f.F := f.elementary
    have hh := orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p := 2) n.b hbF)
    rw [n.b_order] at hh
    norm_num at hh
  have hdb : d * n.b * d⁻¹ = n.b⁻¹ := by
    have hm := (mem_normalizer_iff.mp hdB n.b).mp (mem_zpowers n.b)
    rw [mem_zpowers_iff_mem_range_orderOf, n.b_order] at hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    have hi4 := Finset.mem_range.mp hi
    have hord : orderOf (d * n.b * d⁻¹) = 4 :=
      ((MulAut.conj d).orderOf_eq n.b).trans n.b_order
    interval_cases i
    · simp only [pow_zero] at he
      rw [← he, orderOf_one] at hord
      norm_num at hord
    · exact (hnotcomm (mul_inv_eq_iff_eq_mul.mp (by simpa using he.symm))).elim
    · have hp : (d * n.b * d⁻¹) ^ 2 = 1 := by
        rw [← he, ← pow_mul]
        change n.b ^ 4 = 1
        exact n.b_order ▸ pow_orderOf_eq_one n.b
      have hh := orderOf_dvd_of_pow_eq_one hp
      rw [hord] at hh
      norm_num at hh
    · have hb4 : n.b ^ 4 = 1 := n.b_order ▸ pow_orderOf_eq_one n.b
      rw [← he]
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, hb4]
  have hdb' : d⁻¹ * n.b⁻¹ * d = n.b := by
    have hh := congrArg Inv.inv hdb
    simpa only [mul_inv_rev, inv_inv, hdinv, mul_assoc] using hh
  have hdt : Tits.parrottCommutator d n.t ∈ zpowers z :=
    core_derived_pc h hdJ n.t_mem_inf.1
  have hdtne : Tits.parrottCommutator d n.t ≠ 1 := by
    intro heq
    apply hdX
    change d ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype
    rw [n.core_eq_sylow_centralizer]
    exact ⟨hdP.1, mem_centralizer_singleton_iff.mpr
      ((Tits.parrottCommutator_eq_one_iff _ _).mp heq).eq⟩
  refine ⟨d, hdJ, hdsq, ?_, ?_⟩
  · change (d⁻¹ * n.b⁻¹ * d) * n.b = n.v
    rw [hdb', ← pow_two, n.b_sq]
  · rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hdt
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hdt
    have hi2 := Finset.mem_range.mp hi
    interval_cases i
    · exact (hdtne (by simpa using he.symm)).elim
    · simpa using he.symm
end Stellmacher.Recognition
