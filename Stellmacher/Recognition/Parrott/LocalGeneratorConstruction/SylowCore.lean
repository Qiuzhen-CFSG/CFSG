module

public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.Geometry
public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.SylowAction
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreDerivedOmega
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreDerivedOrder
public import Stellmacher.Recognition.Parrott.LocalNormalizer.ElementaryFusion
public import Stellmacher.Recognition.Parrott.LocalNormalizer.InvolutionCosets
public import Stellmacher.Recognition.Parrott.SecondNormalizerGrowthLocal
public import Stellmacher.Recognition.Parrott.SylowABGeometry
public import Stellmacher.Recognition.Parrott.SylowCoreCaseChoice
public import Stellmacher.Recognition.Parrott.SylowCoreChoice
public import Stellmacher.Recognition.Parrott.SylowCoreCosets
public import Stellmacher.Recognition.Parrott.SylowInvertingInvolutionSelection
public import Stellmacher.Recognition.Parrott.SylowSeedConstruction
public import Stellmacher.Recognition.Parrott.SylowThreeGeneratorSelection

/-!
# Parrott generators from local inputs: SylowCore

The local normalizer geometry selects the involution d inverting the supplied
three-centralizer generator b. Transport of the outer root chooses a, while
commutator covariance determines the two possible core cases. The resulting
seed satisfies (1)–(15) and generates the literal original core and Sylow
subgroup. No subgroup or fusion mark is replaced.

The derived-core normalizer identity and local normalizer solvability in
`ParrottLocalInputs` replace the ambient N₂ assumption. The original APIs
remain unchanged, and F, the supplied Sylow subgroup, t and v remain literal.

Source: D. Parrott, *A characterization of the Tits simple group* (1972),
§3, printed pp.678–682, with the local geometry of §§1–2.
-/

section

/- SylowInvertingInvolutionSelection: local-input version of the original construction. -/

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

private theorem SylowInvertingInvolutionSelection_core_derived_pc (h : ParrottCentralizerHypotheses z)
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
public theorem ParrottNormalizerFusionData.exists_three_generator_involution_of_local_inputs
    [IsSimpleGroup G] (_hns : ¬ Group.IsSolvable G)
    (hlocal : ParrottLocalInputs z) (h : ParrottCentralizerHypotheses z)
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
    e.exists_normalizer_fixed_outer_involution_inverting_three_of_local_inputs h hlocal
      n.sylow_lt_normalizer n.Q n.v n.v_order n.elementary_fixed
  have hdJ : d ∈ J := by
    by_contra hout
    exact hdW (e.sylow_outer_involution_mem_normalizer_omega_of_local_inputs h hlocal
      n.sylow_lt_normalizer d hdP.1 hd2 hout)
  have hdX : d ∉ X := by
    intro hdX
    exact hdW ((e.normalizer_core_fixed_involution_centralizer_of_local_inputs h hlocal
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
    obtain ⟨f, hfa, _, _, _, _⟩ := e.normalizer_fixed_outside_omega_fixed_join_of_local_inputs
      h hlocal n.sylow_lt_normalizer n.Q n.v n.v_order n.elementary_fixed d hdP hd2 hdW
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
    SylowInvertingInvolutionSelection_core_derived_pc h hdJ n.t_mem_inf.1
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

end

section

/- SylowThreeGeneratorSelection: local-input version of the original construction. -/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

/-- The original-core involution selection reduces the three-generator
construction to the compatible a,b relations from the Q action. -/
public theorem ParrottSylowActionData.exists_three_generators_of_ab_selection_of_local_inputs
    [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowActionData n) (hns : ¬ Group.IsSolvable G)
    (hlocal : ParrottLocalInputs z) (h : ParrottCentralizerHypotheses z)
    (a : G)
    (habasis : closure ({z, n.t, n.v, f.u, a} : Set G) = e.F)
    (hbw : Tits.parrottCommutator n.b f.w = 1)
    (haw : Tits.parrottCommutator a f.w = z)
    (hbu : Tits.parrottCommutator n.b f.u = z)
    (hab : Tits.parrottCommutator a n.b = n.t)
    (hax : Tits.parrottCommutator a f.x = 1 ∨
      Tits.parrottCommutator a f.x = n.t) :
    Nonempty (ParrottSylowThreeGeneratorData n) := by
  obtain ⟨d, hdJ, hd2, hdb, hdt⟩ :=
    n.exists_three_generator_involution_of_local_inputs hns hlocal h
  exact f.exists_three_generators_of_ab_and_involution h a d
    habasis hbw haw hbu hab hax hdJ hd2 hdb hdt

end Stellmacher.Recognition

end

section

/- SylowABGeometry: local-input version of the original construction. -/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

private theorem SylowABGeometry_core_derived_pc [Finite G] (h : ParrottCentralizerHypotheses z)
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

private theorem SylowABGeometry_central_commutator_eq_z [Finite G] (h : ParrottCentralizerHypotheses z)
    {g k : G} (hc : Tits.parrottCommutator g k ∈ zpowers z)
    (hne : ¬ Commute g k) : Tits.parrottCommutator g k = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hc
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hc
  have hi2 : i < 2 := Finset.mem_range.mp hi
  interval_cases i
  · exact (hne ((Tits.parrottCommutator_eq_one_iff _ _).mp
      (by simpa using heq.symm))).elim
  · simpa using heq.symm

/-- Equation (2) for b,u is forced for every supplied action frame. -/
public theorem ParrottSylowActionData.b_commutator_u_of_local_inputs [Finite G]
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z)
    (hlocal : ParrottLocalInputs z) : Tits.parrottCommutator n.b f.u = z := by
  let N := normalizer (e.F : Set G)
  let X := (pCore 2 N).map N.subtype
  let D := (commutator X).map X.subtype
  have hbD : n.b ∈ D := n.core_fixed_le_derived (by
    rw [n.core_fixed]; exact mem_zpowers _)
  have hFD : e.F ≤ D := e.elementary_le_normalizer_core_derived_of_local_inputs h hlocal n.sylow_lt_normalizer
  have hDcard : Nat.card D = 64 := e.normalizer_core_derived_order_of_local_inputs h hlocal n.sylow_lt_normalizer
  have hbF : n.b ∉ e.F := by
    intro hb
    let : IsElementaryAbelian 2 e.F := e.elementary
    have hh : n.b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian n.b hb
    rw [n.b_sq] at hh
    have ho := n.v_order
    rw [hh, orderOf_one] at ho
    omega
  have hgen : zpowers n.b ⊔ e.F = D := by
    let B := zpowers n.b ⊔ e.F
    have hBD : B ≤ D := sup_le (zpowers_le.mpr hbD) hFD
    have hFB : e.F < B := lt_of_le_of_ne le_sup_right (by
      intro heq
      exact hbF (heq ▸ (show n.b ∈ B from mem_sup_left (mem_zpowers _))))
    have hlt : Nat.card e.F < Nat.card B := by
      have hle := card_le_of_le hFB.le
      exact lt_of_le_of_ne hle (fun heq => hFB.ne (eq_of_le_of_card_ge hFB.le heq.ge))
    have hdvd := card_dvd_of_le (show e.F ≤ B from le_sup_right)
    rw [e.card] at hlt hdvd
    obtain ⟨k, hk⟩ := hdvd
    apply eq_of_le_of_card_ge hBD
    rw [hDcard]
    omega
  have hu : f.u ∈ E ⊓ e.F := by
    rw [← f.inf_basis]; exact subset_closure (by simp)
  have hb := n.three_generator_b_properties h
  apply SylowABGeometry_central_commutator_eq_z h (SylowABGeometry_core_derived_pc h hb.1 hu.1)
  intro hbu
  have hbC : n.b ∈ centralizer ((E ⊓ e.F : Subgroup G) : Set G) := by
    rw [← f.inf_basis, centralizer_closure]
    apply mem_centralizer_iff.mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact (mem_centralizer_singleton_iff.mp (map_subtype_le _ hb.1)).symm
    · exact hb.2.1.symm.eq
    · exact (show Commute n.b n.v by rw [← n.b_sq]; exact Commute.self_pow _ _).symm.eq
    · exact hbu.symm.eq
  have hDC : D ≤ centralizer ((E ⊓ e.F : Subgroup G) : Set G) := by
    rw [← hgen]
    apply sup_le (zpowers_le.mpr hbC)
    let : IsElementaryAbelian 2 e.F := e.elementary
    intro g hg k hk
    exact setLike_mul_comm (s := e.F) hk.2 hg
  have hDC := hDC.trans_eq (e.elementary_inf_centralizer h)
  have hDA : D = E ⊔ e.F := eq_of_le_of_card_ge hDC
    (by rw [hDcard, e.elementary_join_card h])
  have hED : E ≤ D := hDA ▸ le_sup_left
  have hEF : E ≤ e.F := by
    have hDE := e.normalizer_core_derived_inf_original_derived_of_local_inputs h hlocal n.sylow_lt_normalizer
    have hh : E ≤ D ⊓ E := le_inf hED le_rfl
    exact (hh.trans_eq hDE).trans inf_le_right
  have hEcard : Nat.card E = 32 := by
    rw [card_map_of_injective (K := commutator (pCore 2 H))
      ((H).subtype_injective.comp (pCore 2 H).subtype_injective)]
    exact (parrott_centralizer_structure z h).2.2.2.2.2.2.1
  exact e.ne_derived (eq_of_le_of_card_ge hEF (by rw [e.card, hEcard])).symm

/-- A conjugator in the supplied Q transports x into the original core. -/
public theorem ParrottSylowActionData.exists_three_conjugate_in_core_of_local_inputs [Finite G]
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z)
    (hlocal : ParrottLocalInputs z) :
    ∃ q : n.Q, ((q : normalizer (e.F : Set G)) : G) * f.x *
      ((q : normalizer (e.F : Set G)) : G)⁻¹ ∈ J := by
  let HC := centralizer ({z} : Set G)
  let JC := pCore 2 HC
  let EC := (commutator JC).map (HC.subtype.comp JC.subtype)
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let X := K.map N.subtype
  let U := omega₁ K (p := 2)
  let W := U.map (N.subtype.comp K.subtype)
  have hxX : f.x ∈ X := by
    change f.x ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype
    rw [n.core_eq_sylow_centralizer]
    exact ⟨(f.sylow_eq.symm ▸ mem_sup_left (mem_zpowers f.x)),
      mem_centralizer_singleton_iff.mpr
        ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt)⟩
  have hxW : f.x ∉ W := by
    intro hx
    have hWC : W = X ⊓ centralizer
        ((center U).map ((N.subtype.comp K.subtype).comp U.subtype) : Set G) :=
      n.omega_eq_centralizer
    rw [hWC] at hx
    have hv : n.v ∈ (center U).map ((N.subtype.comp K.subtype).comp U.subtype) := by
      have hZ : (center U).map ((N.subtype.comp K.subtype).comp U.subtype) =
          (zpowers z ⊔ zpowers n.t) ⊔ zpowers n.v := n.omega_center_eq
      rw [hZ]
      exact mem_sup_right (mem_zpowers n.v)
    have hc : Commute f.x n.v := (mem_centralizer_iff.mp hx.2 n.v hv).symm
    have ht : n.t = 1 := f.eq01_xv.symm.trans
      ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
    have ho := n.t_order
    rw [ht, orderOf_one] at ho
    norm_num at ho
  have hsqJ : f.x ^ 2 ∉ JC.map HC.subtype := by
    intro hx
    have hw : f.w ∈ EC := by
      change f.w ∈ E
      rw [← f.derived_basis]; exact subset_closure (by simp)
    have hh := SylowABGeometry_core_derived_pc h hx hw
    rw [f.square_commutator_w] at hh
    exact n.v_not_mem_core_center (n.core_center_eq.symm ▸ mem_sup_left hh)
  have hsq2 : (f.x ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using f.eq01_x
  have hsqOrder : orderOf (f.x ^ 2) = 2 := orderOf_eq_prime hsq2
    (fun heq => hsqJ (heq ▸ (JC.map HC.subtype).one_mem))
  obtain ⟨q, hq⟩ := e.normalizer_core_involution_transport_of_local_inputs h hlocal n.sylow_lt_normalizer
    n.Q n.core_fixed_le_derived (f.x ^ 2) (X.pow_mem hxX 2) hsq2
  let qN : N := q
  have hqE : (qN : G) * f.x ^ 2 * (qN : G)⁻¹ ∈ EC :=
    e.outer_involution_normalizer_conjugate_mem_derived h (f.x ^ 2) hsqJ hsqOrder qN hq
  let a := (qN : G) * f.x * (qN : G)⁻¹
  have haX : a ∈ X := by
    obtain ⟨xN, hxN, hex⟩ := hxX
    refine ⟨qN * xN * qN⁻¹, (inferInstance : K.Normal).conj_mem xN hxN qN, ?_⟩
    change (qN : G) * (xN : G) * (qN : G)⁻¹ = a
    change (xN : G) = f.x at hex
    rw [hex]
  have ha2 : a ^ 2 ∈ EC := by
    have heq : a ^ 2 = (qN : G) * f.x ^ 2 * (qN : G)⁻¹ :=
      (map_pow (MulAut.conj (qN : G)) f.x 2).symm
    rwa [heq]
  have hNW : N ≤ normalizer (W : Set G) := by
    let V := U.map K.subtype
    let : U.Characteristic := omega₁_characteristic K
    let : V.Normal := ConjAct.normal_of_characteristic_of_normal
    have hh := le_normalizer_map («H» := V) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, V, W, map_map] using hh
  refine ⟨q, ?_⟩
  by_contra haJ
  have haW : a ∈ W := e.normalizer_core_outer_square_mem_derived_mem_omega_of_local_inputs h hlocal
    n.sylow_lt_normalizer a haX ha2 haJ
  exact hxW ((mem_normalizer_iff.mp (hNW qN.property) f.x).mpr haW)

private theorem SylowABGeometry_pc_swap (g k : G) :
    Tits.parrottCommutator g k = (Tits.parrottCommutator k g)⁻¹ := by
  simp only [Tits.parrottCommutator]; group

private theorem SylowABGeometry_map_pc (r : G ≃* G) (g k : G) :
    r (Tits.parrottCommutator g k) = Tits.parrottCommutator (r g) (r k) := by
  simp only [Tits.parrottCommutator, map_mul, map_inv]

/-- The Q action chooses a with its elementary basis, equations (2),(5),
and the required a,x alternative, for every supplied action frame. -/
public theorem ParrottSylowActionData.exists_a_selection_of_local_inputs [Finite G]
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z)
    (hlocal : ParrottLocalInputs z) :
    ∃ a : G, closure ({z,n.t,n.v,f.u,a} : Set G) = e.F ∧
      Tits.parrottCommutator a f.w = z ∧
      Tits.parrottCommutator a n.b = n.t ∧
      (Tits.parrottCommutator a f.x = 1 ∨ Tits.parrottCommutator a f.x = n.t) := by
  classical
  let : IsElementaryAbelian 2 e.F := e.elementary
  obtain ⟨q, hqx⟩ := f.exists_three_conjugate_in_core_of_local_inputs h hlocal
  let qG : G := ((q : normalizer (e.F : Set G)) : G)
  let r : G ≃* G := MulAut.conj qG
  have hqA : qG ∈ (n.Q : Subgroup (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype := mem_map_of_mem _ q.property
  have hrv : r n.v = n.v := by
    change qG*n.v*qG⁻¹=n.v
    rw [n.v_fixed qG hqA, mul_inv_cancel_right]
  have hrb : r n.b = n.b := by
    change qG*n.b*qG⁻¹=n.b
    rw [(n.three_generator_b_properties h).2.2 qG hqA, mul_inv_cancel_right]
  have hrtpc : Tits.parrottCommutator (r f.x) n.v = r n.t := by
    rw [← hrv, ← SylowABGeometry_map_pc, f.eq01_xv]
  have hrt : r n.t = z := by
    rw [← hrtpc]
    apply SylowABGeometry_central_commutator_eq_z h (SylowABGeometry_core_derived_pc h hqx n.v_mem_inf.1)
    intro hc
    have hh : r n.t = 1 := hrtpc.symm.trans ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
    have ht : n.t=1 := r.injective (hh.trans (map_one r).symm)
    exact n.t_not_mem_zpowers (ht ▸ (zpowers z).one_mem)
  have hst : r.symm z = n.t := (r.symm_apply_eq).mpr hrt.symm
  have hsb : r.symm n.b = n.b := (r.symm_apply_eq).mpr hrb.symm
  let a := r.symm f.u
  have hu : f.u ∈ E ⊓ e.F := by
    rw [← f.inf_basis]; exact subset_closure (by simp)
  have hw : f.w ∈ E := by
    rw [← f.derived_basis]; exact subset_closure (by simp)
  have haF : a ∈ e.F := by
    have hqN : qG⁻¹ ∈ normalizer (e.F : Set G) :=
      (normalizer (e.F : Set G)).inv_mem (q : normalizer (e.F : Set G)).property
    simpa only [a, r, MulAut.conj_symm_apply, inv_inv] using
      (mem_normalizer_iff.mp hqN f.u).mp hu.2
  have hz2 : z^2=1 := h.involution ▸ pow_orderOf_eq_one z
  have hzinv : z⁻¹=z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz2)
  have hab : Tits.parrottCommutator a n.b = n.t := by
    change Tits.parrottCommutator (r.symm f.u) n.b = n.t
    rw [← hsb, ← SylowABGeometry_map_pc, SylowABGeometry_pc_swap f.u n.b, f.b_commutator_u_of_local_inputs h hlocal, hzinv, hst]
  have haE : a ∉ E := by
    intro ha
    have hh := SylowABGeometry_core_derived_pc h (n.three_generator_b_properties h).1 ha
    rw [SylowABGeometry_pc_swap n.b a, hab] at hh
    exact n.t_not_mem_zpowers (by simpa only [inv_inv] using (zpowers z).inv_mem hh)
  have habasis : closure ({z,n.t,n.v,f.u,a} : Set G) = e.F := by
    have hreorder : ({z,n.t,n.v,f.u,a} : Set G) = {z,n.t,n.v,f.u} ∪ {a} := by
      ext g; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto
    rw [hreorder, Subgroup.closure_union, ← zpowers_eq_closure, f.inf_basis]
    apply eq_of_le_of_card_ge (sup_le inf_le_right (zpowers_le.mpr haF))
    rw [card_sup_zpowers_of_normalizing_involution (E ⊓ e.F) a
      (elemPow_eq_one_of_isElementaryAbelian a haF) (fun hh => haE hh.1)]
    · rw [e.inf_card, e.card]
    · apply Subgroup.centralizer_le_normalizer
      intro g hg
      exact setLike_mul_comm (s := e.F) hg.2 haF
  have haw : Tits.parrottCommutator a f.w = z := by
    apply SylowABGeometry_central_commutator_eq_z h (SylowABGeometry_core_derived_pc h (e.le_core haF) hw)
    intro hc
    apply haE
    rw [← parrott_derived_centralizer z h, ← f.derived_basis, centralizer_closure]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact setLike_mul_comm (s := e.F) e.z_mem_inf.2 haF
    · exact setLike_mul_comm (s := e.F) n.t_mem_inf.2 haF
    · exact setLike_mul_comm (s := e.F) n.v_mem_inf.2 haF
    · exact setLike_mul_comm (s := e.F) hu.2 haF
    · exact hc.symm.eq
  have haxmem : Tits.parrottCommutator a f.x ∈ zpowers n.t := by
    have hh := mem_map_of_mem r.symm.toMonoidHom (SylowABGeometry_core_derived_pc h hqx hu.1)
    rw [MonoidHom.map_zpowers] at hh
    change r.symm (Tits.parrottCommutator (r f.x) f.u) ∈ zpowers (r.symm z) at hh
    rw [SylowABGeometry_map_pc, r.symm_apply_apply, hst] at hh
    rw [SylowABGeometry_pc_swap a f.x]
    exact (zpowers n.t).inv_mem hh
  refine ⟨a, habasis, haw, hab, ?_⟩
  rw [mem_zpowers_iff_mem_range_orderOf, n.t_order] at haxmem
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp haxmem
  have hi2 : i < 2 := Finset.mem_range.mp hi
  interval_cases i
  · exact Or.inl (by simpa using heq.symm)
  · exact Or.inr (by simpa using heq.symm)

/-- All first-three-generator choices are discharged except the b,w equation.
The supplied z,t,v,F,T are retained throughout. -/
public theorem ParrottSylowActionData.exists_three_generators_of_commutator_bw_of_local_inputs
    [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowActionData n) (hns : ¬ Group.IsSolvable G)
    (hlocal : ParrottLocalInputs z) (h : ParrottCentralizerHypotheses z)
    (hbw : Tits.parrottCommutator n.b f.w = 1) :
    Nonempty (ParrottSylowThreeGeneratorData n) := by
  obtain ⟨a, haF, haw, hab, hax⟩ := f.exists_a_selection_of_local_inputs h hlocal
  exact f.exists_three_generators_of_ab_selection_of_local_inputs hns hlocal h a haF hbw haw
    (f.b_commutator_u_of_local_inputs h hlocal) hab hax

end Stellmacher.Recognition

end

section

/- SylowCoreCosets: local-input version of the original construction. -/

namespace Stellmacher.Recognition.ParrottSylowInitialData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- The five correlated core coset alternatives for the supplied initial frame.

Covariance follows from the centralizer hypotheses. The elementary coefficient
calculation then selects the common Boolean; the other local inputs are not
needed at this coordinate step.
-/
public theorem exists_core_coset_alternatives_of_local_inputs [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowInitialData n) (_hns : ¬ Group.IsSolvable G)
    (_hlocal : ParrottLocalInputs z) (h : ParrottCentralizerHypotheses z) :
    ∃ caseTwo : Bool, f.CoreCosetAlternatives caseTwo := by
  have hc : f.CoreCovariance := f.core_covariance h
  exact f.exists_core_coset_alternatives_of_covariance h hc

end Stellmacher.Recognition.ParrottSylowInitialData

end

section

/- SylowCoreChoice: local-input version of the original construction. -/

namespace Stellmacher.Recognition.ParrottSylowInitialData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Choose either set of core relations from the original initial frame.
Only `a` and `c` are adjusted. The type of `g` preserves the supplied normalizer
data and all through-(10) fields, including the actual closure equalities. -/
public theorem exists_core_relations_of_local_inputs [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowInitialData n) (hns : ¬ Group.IsSolvable G)
    (hlocal : ParrottLocalInputs z) (h : ParrottCentralizerHypotheses z) :
    ∃ (caseTwo : Bool) (g : ParrottSylowInitialData n),
      g.CoreRelations caseTwo ∧
      g.u = f.u ∧ g.w = f.w ∧ g.x = f.x ∧ g.b = f.b ∧ g.d = f.d ∧
      (g.a = f.a ∨ g.a = f.a * n.t) ∧
      ∃ r ∈ Subgroup.closure ({f.w, n.v, n.t, f.u} : Set G), g.c = f.c * r := by
  obtain ⟨caseTwo, hc⟩ := f.exists_core_coset_alternatives_of_local_inputs hns hlocal h
  exact ⟨caseTwo, f.exists_core_relations_of_coset_alternatives h caseTwo hc⟩

end Stellmacher.Recognition.ParrottSylowInitialData

end

section

/- SylowCoreCaseChoice: local-input version of the original construction. -/

namespace Stellmacher.Recognition.ParrottSylowInitialData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Choose a frame satisfying either printed set of core relations, with the
supplied marked normalizer data and all equations through (10) preserved. -/
public theorem exists_core_case_of_local_inputs [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowInitialData n) (hns : ¬ Group.IsSolvable G)
    (hlocal : ParrottLocalInputs z) (h : ParrottCentralizerHypotheses z) :
    ∃ (caseTwo : Bool) (f' : ParrottSylowInitialData n), f'.CoreRelations caseTwo := by
  obtain ⟨caseTwo, f', hf', _⟩ := f.exists_core_relations_of_local_inputs hns hlocal h
  exact ⟨caseTwo, f', hf'⟩

end Stellmacher.Recognition.ParrottSylowInitialData

end

section

/- SylowSeedConstruction: local-input version of the original construction. -/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

namespace ParrottSylowInitialData

/-- Every actual initial frame extends, after the proved core choices, to a
seed satisfying either printed case of (11)–(15). -/
public theorem exists_seed_of_local_inputs [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowInitialData n) (hns : ¬ Group.IsSolvable G)
    (hlocal : ParrottLocalInputs z) (h : ParrottCentralizerHypotheses z) :
    ∃ caseTwo : Bool, Nonempty (ParrottSylowSeedData n caseTwo) := by
  obtain ⟨caseTwo, f', hc⟩ := f.exists_core_case_of_local_inputs hns hlocal h
  exact ⟨caseTwo, ⟨f'.toSeed h hc⟩⟩

end ParrottSylowInitialData

/-- Complete the seed from an action frame whose w commutes with the supplied
three-centralizer generator. All other generator choices are discharged. -/
public theorem ParrottSylowActionData.exists_seed_of_commutator_bw_of_local_inputs
    [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowActionData n) (hns : ¬ Group.IsSolvable G)
    (hlocal : ParrottLocalInputs z) (h : ParrottCentralizerHypotheses z)
    (hbw : Tits.parrottCommutator n.b f.w = 1) :
    ∃ caseTwo : Bool, Nonempty (ParrottSylowSeedData n caseTwo) := by
  obtain ⟨g⟩ := f.exists_three_generators_of_commutator_bw_of_local_inputs hns hlocal h hbw
  obtain ⟨i⟩ := g.exists_initial h
  exact i.exists_seed_of_local_inputs hns hlocal h

/-- The supplied normalizer data admit actual Sylow seed generators satisfying
either printed case of equations (1)–(15), with z,t,v and E,F,J,T preserved. -/
public theorem ParrottNormalizerFusionData.exists_sylow_seed_of_local_inputs
    [Finite G] [IsSimpleGroup G]
    (n : ParrottNormalizerFusionData e) (hns : ¬ Group.IsSolvable G)
    (hlocal : ParrottLocalInputs z) (h : ParrottCentralizerHypotheses z) :
    ∃ caseTwo : Bool, Nonempty (ParrottSylowSeedData n caseTwo) := by
  obtain ⟨f, hbw⟩ := n.exists_sylow_action_commutator_bw_of_local_inputs h hlocal
  exact f.exists_seed_of_commutator_bw_of_local_inputs hns hlocal h hbw

end Stellmacher.Recognition

end
