module
public import Stellmacher.Recognition.Parrott.NormalizerInvolutionCosets
public import Stellmacher.Recognition.Parrott.OuterCoreFixedCentralization

/-!
# Outer roots with square in the derived core

Write H = C_G(z), J = O₂(H), E = J′ and K = O₂(N_G(F)). An element
k ∈ K outside J whose square is in E lies in Ω₁(K). Choose an outer
involution y ∈ K. Their images in the cyclic Sylow subgroup of H/J are
the same involution, so ky ∈ J. Both (ky)² and k² lie in E, hence
[ky,y] ∈ E. The fixed-space centralization theorem puts ky in C_J(C_E(y)),
which is contained in Ω₁(K); multiplying by y proves the result.

This supplies the root-level bridge after transporting an involutory square.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.674 and 677–678, the calculation Ω₁(K) = ⟨B,y⟩ and the transport x ∼_N c*.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem outer_mul_mem_core (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ k y : H, (k : G) ∈ (d.sylow : Subgroup G) →
      (y : G) ∈ (d.sylow : Subgroup G) →
      k ^ 2 ∈ J → y ^ 2 = 1 → k ∉ J → y ∉ J → k * y ∈ J := by
  intro H J k y hk hy hk2 hy2 hkJ hyJ
  let q := QuotientGroup.mk' J
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let model := e.toMonoidHom.comp q
  let A := (d.localSylow : Subgroup H).map model
  let : IsCyclic A :=
    (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ A
      (d.localSylow.isPGroup'.map model)).1
  have hmem (u : H) (hu : (u : G) ∈ (d.sylow : Subgroup G)) : model u ∈ A := by
    rw [d.sylow_map] at hu
    obtain ⟨v, hv, heq⟩ := hu
    have hvu : v = u := H.subtype_injective heq
    exact mem_map_of_mem model (hvu ▸ hv)
  have hord (u : H) (hu : (u : G) ∈ (d.sylow : Subgroup G))
      (hu2 : u ^ 2 ∈ J) (huJ : u ∉ J) : orderOf (⟨model u, hmem u hu⟩ : A) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change model u ^ 2 = 1
      rw [← map_pow]
      change e (q (u ^ 2)) = 1
      rw [show q (u ^ 2) = 1 from (QuotientGroup.eq_one_iff _).mpr hu2, map_one]
    · intro hh
      have hm : model u = 1 := congrArg A.subtype hh
      have hq : q u = 1 := e.injective (hm.trans (map_one e).symm)
      exact huJ ((QuotientGroup.eq_one_iff u).mp hq)
  have heq : model k = model y := congrArg A.subtype
    (IsCyclic.eq_of_orderOf_eq_two (hord k hk hk2 hkJ)
      (hord y hy (hy2 ▸ J.one_mem) hyJ))
  apply (QuotientGroup.eq_one_iff (k * y)).mp
  apply e.injective
  change model (k * y) = e 1
  rw [map_mul, heq, ← map_mul, ← pow_two, hy2, map_one, map_one]

/-- An outer element of the normalizer core whose square lies in the original
derived core belongs to the actual omega subgroup. -/
public theorem ParrottSecondElementaryData.normalizer_core_outer_square_mem_derived_mem_omega
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∀ k : G, k ∈ K.map N.subtype → k ^ 2 ∈ E → k ∉ J.map H.subtype →
      k ∈ (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) := by
  intro H J E N K k hk hk2 hkJ
  let U := omega₁ K (p := 2)
  let W := U.map (N.subtype.comp K.subtype)
  let DH := (commutator J).map J.subtype
  obtain ⟨y, hy, hy2, hyJ⟩ :=
    d.exists_normalizer_core_involution_outside_original_core h hN hproper
  let yH : H := ⟨y, d.sylow_le_centralizer (d.normalizer_core_le_sylow hy)⟩
  let kH : H := ⟨k, d.sylow_le_centralizer (d.normalizer_core_le_sylow hk)⟩
  have hyH2 : yH ^ 2 = 1 := Subtype.ext (hy2 ▸ pow_orderOf_eq_one y)
  have hyHJ : yH ∉ J := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hkHJ : kH ∉ J := fun hh => hkJ (mem_map_of_mem H.subtype hh)
  have hkHD : kH ^ 2 ∈ DH := by
    have hh : k ^ 2 ∈ DH.map H.subtype := by simpa only [DH, map_map] using hk2
    exact (mem_map_iff_mem (f := H.subtype) H.subtype_injective).mp hh
  have hkHJ2 : kH ^ 2 ∈ J := (map_subtype_le (commutator J)) hkHD
  have haJ : kH * yH ∈ J := outer_mul_mem_core d h kH yH
    (d.normalizer_core_le_sylow hk) (d.normalizer_core_le_sylow hy)
    hkHJ2 hyH2 hkHJ hyHJ
  let aJ : J := ⟨kH * yH, haJ⟩
  let : IsElementaryAbelian 2 (J ⧸ commutator J) :=
    (parrott_core_abelianization_structure z h).1
  have ha2 : (kH * yH) ^ 2 ∈ DH := by
    have hh : aJ ^ 2 ∈ commutator J := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (commutator J) (aJ ^ 2) = 1
      rw [map_pow]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (J ⧸ commutator J)) _
    exact mem_map_of_mem J.subtype hh
  have hcomm : ⁅kH * yH, yH⁆ ∈ DH := by
    let : DH.Normal := ConjAct.normal_of_characteristic_of_normal
    have heq : ⁅kH * yH, yH⁆ = (kH * yH) ^ 2 * (yH * kH ^ 2 * yH⁻¹)⁻¹ := by
      simp only [commutatorElement_def, pow_two, mul_inv_rev, inv_inv, mul_assoc,
        mul_inv_cancel_left]
      simp only [← mul_assoc yH yH, ← pow_two yH, hyH2, one_mul,
        mul_inv_cancel_left]
    rw [heq]
    exact DH.mul_mem ha2 (DH.inv_mem ((inferInstance : DH.Normal).conj_mem _ hkHD yH))
  let V := E ⊓ centralizer ({y} : Set G)
  have haC : k * y ∈ centralizer (V : Set G) := by
    intro v hv
    obtain ⟨vJ, hvJ, heq⟩ := hv.1
    have hvy : Commute (vJ : H) yH := by
      apply H.subtype_injective
      change (vJ : G) * y = y * (vJ : G)
      change (vJ : G) = v at heq
      rw [heq]
      exact mem_centralizer_singleton_iff.mp hv.2
    have hh := parrott_outer_core_centralizes_derived_fixed_of_commutator_mem z h yH
      ((Subgroup.orderOf_coe yH).symm.trans hy2) hyHJ (kH * yH) haJ hcomm
      (vJ : H) (mem_map_of_mem J.subtype hvJ) hvy
    have hhG := congrArg H.subtype hh.symm.eq
    change (vJ : G) * (k * y) = (k * y) * (vJ : G) at hhG
    change (vJ : G) = v at heq
    rwa [heq] at hhG
  have haW : k * y ∈ W := d.normalizer_core_outer_fixed_kernel_le_omega h hN hproper
    y hy hy2 hyJ ⟨mem_map_of_mem H.subtype haJ, haC⟩
  have hyW : y ∈ W := d.normalizer_core_square_one_mem_omega y hy
    (hy2 ▸ pow_orderOf_eq_one y)
  have hh := W.mul_mem haW hyW
  simpa only [mul_assoc, ← pow_two, show y ^ 2 = 1 from hy2 ▸ pow_orderOf_eq_one y,
    mul_one] using hh
end Stellmacher.Recognition
