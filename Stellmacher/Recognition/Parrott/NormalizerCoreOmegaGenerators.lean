module
public import Stellmacher.Recognition.Parrott.NormalizerCoreOmegaFixed
public import Stellmacher.Recognition.Parrott.CoreQuotientAction
public import Theory.GroupAction.FiveFourInvolutionFixed

/-!
# The core part of the normalizer omega from involution conjugates

For an outer involution y in the actual normalizer core K, write V=C_E(y)
and B=C_J(V). Then B lies in Ω₁(K). Indeed E lies in Ω₁(K), and normality
of Ω₁(K) in N_G(F) puts [y,J] in it as well. The three-subgroup lemma
shows that E[y,J] centralizes V. On J/E the displacement of y has order
four, so |E[y,J]|≥128=|B|. This proves E[y,J]=B without selecting an
order-four lift of a quotient element.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.674 and 677, the computation Ω₁(K)=⟨B,y⟩. The displacement argument
supplies the generation implicit in that computation.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Commutators of the actual outer involution with the whole original core,
together with E, generate its fixed-space centralizer inside that core.
In particular this order-128 subgroup lies in the actual omega image. -/
public theorem normalizer_core_outer_fixed_kernel_le_omega
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let embed := N.subtype.comp K.subtype
    ∀ y : G, y ∈ K.map N.subtype → orderOf y = 2 → y ∉ J.map H.subtype →
      let V := E ⊓ centralizer ({y} : Set G)
      J.map H.subtype ⊓ centralizer (V : Set G) ≤ U.map embed := by
  intro H J E N K U embed y hy hy2 hyJ V
  let L := J.map H.subtype
  let B := L ⊓ centralizer (V : Set G)
  let X := U.map embed
  let Y := zpowers y
  let R := E ⊔ ⁅Y, L⁆
  have hyH : y ∈ H := d.sylow_le_centralizer (d.normalizer_core_le_sylow hy)
  let yH : H := ⟨y, hyH⟩
  let j := H.subtype.comp J.subtype
  have hj : Function.Injective j := H.subtype_injective.comp J.subtype_injective
  obtain ⟨hVcard, hBcard, hBK, _, _, _⟩ :=
    d.normalizer_core_outer_fixed_centralizer h hN hproper y hy hy2 hyJ
  change Nat.card B = 128 at hBcard
  have hEL : E ≤ L := by
    rintro e ⟨eJ, _, rfl⟩
    exact mem_map_of_mem H.subtype eJ.property
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map j
  have hEB : E ≤ B := le_inf hEL ((le_centralizer E).trans (centralizer_le inf_le_left))
  have hEX : E ≤ X := by
    intro e he
    obtain ⟨eN, heK, heq⟩ := hBK (hEB he)
    let eK : K := ⟨eN, heK⟩
    refine ⟨eK, subset_closure ?_, heq⟩
    apply Subtype.ext
    apply Subtype.ext
    change (eN : G) ^ (2 ^ 1) = 1
    rw [pow_one, show (eN : G) = e from heq]
    exact elemPow_eq_one_of_isElementaryAbelian e he
  have hyX : y ∈ X := by
    obtain ⟨yN, hyK, heq⟩ := hy
    let yK : K := ⟨yN, hyK⟩
    refine ⟨yK, subset_closure ?_, heq⟩
    apply Subtype.ext
    apply Subtype.ext
    change (yN : G) ^ (2 ^ 1) = 1
    rw [pow_one, show (yN : G) = y from heq]
    exact hy2 ▸ pow_orderOf_eq_one y
  have hNX : N ≤ normalizer (X : Set G) := by
    let W := U.map K.subtype
    let : U.Characteristic := omega₁_characteristic K
    let : W.Normal := ConjAct.normal_of_characteristic_of_normal
    have hh := le_normalizer_map (H := W) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, W, X, map_map] using hh
  have hRX : R ≤ X := by
    refine sup_le hEX ?_
    exact (commutator_mono (zpowers_le.mpr hyX) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        (d.core_le_sylow.trans (d.sylow_le_normalizer.trans hNX)))
  have hYL : Y ≤ normalizer (L : Set G) := by
    have hh := le_normalizer_map (H := J) H.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] at hh
    exact (zpowers_le.mpr hyH).trans hh
  have hYV : Y ≤ centralizer (V : Set G) := by
    apply zpowers_le.mpr
    intro v hv
    exact mem_centralizer_singleton_iff.mp hv.2
  have hLV : ⁅L, V⁆ ≤ zpowers z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro v hv l hl
    obtain ⟨b, hb, rfl⟩ := hv.1
    obtain ⟨lH, hlJ, rfl⟩ := hl
    obtain ⟨hZ, _, _, _, hupper, _, _, _⟩ := parrott_centralizer_structure z h
    have hbc : ⁅b, (⟨lH, hlJ⟩ : J)⁆ ∈ center J := by
      have hbU : b ∈ Subgroup.upperCentralSeries J 2 := hupper ▸ hb
      simpa only [Subgroup.upperCentralSeries_one] using
        (Subgroup.mem_upperCentralSeries_succ_iff.mp hbU (⟨lH, hlJ⟩ : J))
    rw [← hZ]
    exact mem_map_of_mem j hbc
  have hzY : zpowers z ≤ centralizer (Y : Set G) := by
    apply le_centralizer_iff.mpr
    rw [zpowers_eq_closure, centralizer_closure]
    exact zpowers_le.mpr hyH
  have hdouble : ⁅⁅Y, L⁆, V⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · exact commutator_eq_bot_iff_le_centralizer.mpr (hLV.trans hzY)
    · rw [commutator_comm V Y, commutator_eq_bot_iff_le_centralizer.mpr hYV,
        commutator_bot_left]
  have hRB : R ≤ B := sup_le hEB (le_inf
    (le_normalizer_iff_commutator_le_right.mp hYL)
    (commutator_eq_bot_iff_le_centralizer.mp hdouble))
  let D := commutator J
  let W := J ⧸ D
  let q := QuotientGroup.mk' D
  let P := R.comap j
  have hPmap : P.map j = R := by
    apply map_comap_eq_self
    have hjrange : j.range = L := by rw [MonoidHom.range_comp, J.range_subtype]
    rw [hjrange]
    exact hRB.trans inf_le_left
  have hDP : D ≤ P := by
    intro b hb
    exact mem_sup_left (mem_map_of_mem j hb)
  obtain ⟨helem, hWcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 W := helem
  obtain ⟨f, hf, heval⟩ := parrott_core_quotient_action z h
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let fM := f.comp e.symm.toMonoidHom
  let u := e (QuotientGroup.mk' J yH)
  have hu : orderOf u = 2 := by
    rw [e.orderOf_eq]
    apply orderOf_eq_prime
    · rw [← map_pow]
      have hyH2 : yH ^ 2 = 1 := Subtype.ext (hy2 ▸ pow_orderOf_eq_one y)
      rw [hyH2, map_one]
    · intro hh
      exact hyJ (mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff yH).mp hh))
  let c := fM u
  have hc : c = f (QuotientGroup.mk' J yH) := by
    simp only [c, fM, u, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply]
  have hfixed : Nat.card (FixedPoints.subgroup (zpowers c) W) = 4 :=
    (Theory.GroupAction.five_four_involution_fixed_displacement hWcard φ hφ fM
      (hf.comp e.symm.injective) u hu).1
  let δ : W →* W := {
    toFun := fun w => c w * w⁻¹
    map_one' := by simp
    map_mul' := by
      intro w t
      simp only [map_mul, mul_inv_rev]
      ac_rfl }
  have hker : δ.ker = FixedPoints.subgroup (zpowers c) W := by
    ext w
    change c w * w⁻¹ = 1 ↔ w ∈ FixedPoints.subgroup (zpowers c) W
    rw [mul_inv_eq_one]
    exact (MulAut.mem_fixed_zpowers_iff c w).symm
  have hδcard : Nat.card δ.range = 4 := by
    have hh := δ.ker.card_mul_index
    rw [index_ker, hker, hfixed, hWcard] at hh
    omega
  have hδP : δ.range ≤ P.map q := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective D w
    let a' : J := ⟨yH * (a : H) * yH⁻¹, (inferInstance : J.Normal).conj_mem a a.property yH⟩
    refine ⟨a' * a⁻¹, ?_, ?_⟩
    · change j (a' * a⁻¹) ∈ R
      apply mem_sup_right
      have hh := commutator_mem_commutator (mem_zpowers y)
        (mem_map_of_mem H.subtype a.property)
      exact hh
    · change q (a' * a⁻¹) = c (q a) * (q a)⁻¹
      rw [map_mul, map_inv, hc, heval yH a a' rfl]
  have hRcard : 128 ≤ Nat.card R := by
    have hp := (card_le_of_le hδP)
    rw [hδcard] at hp
    have hDcard : Nat.card D = 32 :=
      (parrott_centralizer_structure z h).2.2.2.2.2.2.1
    have hh := relIndex_mul_relIndex (⊥ : Subgroup J) D P bot_le hDP
    rw [relIndex_bot_left, relIndex_bot_left, hDcard] at hh
    have hqidx := relIndex_ker P q
    rw [QuotientGroup.ker_mk'] at hqidx
    change D.relIndex P = Nat.card (P.map q) at hqidx
    rw [hqidx] at hh
    have hPr : Nat.card P = Nat.card R :=
      (card_map_of_injective (K := P) hj).symm.trans (congrArg (fun S : Subgroup G => Nat.card S) hPmap)
    rw [hPr] at hh
    exact (Nat.mul_le_mul_left 32 hp).trans_eq hh
  have hRB_eq : R = B := eq_of_le_of_card_ge hRB (by rw [hBcard]; exact hRcard)
  change B ≤ X
  rw [← hRB_eq]
  exact hRX

end Stellmacher.Recognition.ParrottSecondElementaryData
