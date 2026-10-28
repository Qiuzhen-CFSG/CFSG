module

public import Stellmacher.Recognition.Parrott.NormalizerCoreOmegaFixed
public import Stellmacher.Recognition.Parrott.DerivedTCoreInvolutions
public import Stellmacher.Recognition.Parrott.OuterCoreFixedCentralization
public import Theory.GroupTheory.PGroup.OmegaCyclicImage

/-!
# Involutions centralize the outer derived fixed space

For the supplied second elementary subgroup and Sylow subgroup, every
square-one element of the normalizer core centralizes the derived fixed
space of an outer involution y. Core involutions lie in E∨F; the Sylow
fixes the defining generator of F modulo E. Two outer involutions have
the same image in the cyclic two-subgroup of H/J. Their product is in J,
and its commutator with y is its square, hence lies in J′. In both cases
the commuting actions on J′ give pointwise fixation of C_{J′}(y).

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.674 and 677.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem outer_involutions_mul_mem_core (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ k y : H, (k : G) ∈ (d.sylow : Subgroup G) →
      (y : G) ∈ (d.sylow : Subgroup G) →
      k ^ 2 = 1 → y ^ 2 = 1 → k ∉ J → y ∉ J → k * y ∈ J := by
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
      (hu2 : u ^ 2 = 1) (huJ : u ∉ J) : orderOf (⟨model u, hmem u hu⟩ : A) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change model u ^ 2 = 1
      exact (map_pow model u 2).symm.trans (by rw [hu2, map_one])
    · intro hh
      have hm : model u = 1 := congrArg A.subtype hh
      have hq : q u = 1 := e.injective (hm.trans (map_one e).symm)
      exact huJ ((QuotientGroup.eq_one_iff u).mp hq)
  have heq : model k = model y := congrArg A.subtype
    (IsCyclic.eq_of_orderOf_eq_two (hord k hk hk2 hkJ) (hord y hy hy2 hyJ))
  apply (QuotientGroup.eq_one_iff (k * y)).mp
  apply e.injective
  change model (k * y) = e 1
  rw [map_mul, heq, ← map_mul, ← pow_two, hy2, map_one, map_one]

/-- Every square-one element of the actual normalizer core centralizes the
fixed derived space of an actual involution outside the original core. -/
public theorem normalizer_core_involutions_centralize_outer_fixed
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∀ y : G, y ∈ K.map N.subtype → orderOf y = 2 → y ∉ J.map H.subtype →
      ∀ k : G, k ∈ K.map N.subtype → k ^ 2 = 1 →
        k ∈ centralizer (E ⊓ centralizer ({y} : Set G) : Set G) := by
  intro H J E N K y hy hy2 hyJ k hk hk2
  let V := E ⊓ centralizer ({y} : Set G)
  let C := centralizer (V : Set G)
  have hyT := d.normalizer_core_le_sylow hy
  have hkT := d.normalizer_core_le_sylow hk
  let yH : H := ⟨y, d.sylow_le_centralizer hyT⟩
  let kH : H := ⟨k, d.sylow_le_centralizer hkT⟩
  have hyH2 : orderOf yH = 2 := (Subgroup.orderOf_coe yH).symm.trans hy2
  have hyHJ : yH ∉ J := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hcentral (x : H) (hx : x ∈ J)
      (hxy : ⁅x, yH⁆ ∈ (commutator J).map J.subtype) : (x : G) ∈ C := by
    intro v hv
    obtain ⟨vJ, hvJ, heq⟩ := hv.1
    have hvy : Commute (vJ : H) yH := by
      apply H.subtype_injective
      change (vJ : G) * y = y * (vJ : G)
      change (vJ : G) = v at heq
      rw [heq]
      exact mem_centralizer_singleton_iff.mp hv.2
    have hh := parrott_outer_core_centralizes_derived_fixed_of_commutator_mem
      z h yH hyH2 hyHJ x hx hxy (vJ : H) (mem_map_of_mem J.subtype hvJ) hvy
    have hhG := congrArg H.subtype hh.symm.eq
    change (vJ : G) * (x : G) = (x : G) * (vJ : G) at hhG
    change (vJ : G) = v at heq
    rwa [heq] at hhG
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEC : E ≤ C := (le_centralizer E).trans (centralizer_le inf_le_left)
  have hFC : d.F ≤ C := by
    rw [d.fixed_join]
    exact sup_le (zpowers_le.mpr (hcentral d.a d.a_mem_core
      (d.sylow_commutator_a_mem_derived h yH hyT))) (inf_le_left.trans hEC)
  by_cases hkJ : k ∈ J.map H.subtype
  · obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
      d.exists_normalizer_core_center_generator h hN hproper
    have htZ : t ∈ (center K).map (N.subtype.comp K.subtype) := by
      rw [hcenter]
      exact mem_sup_right (mem_zpowers t)
    have hKeq := d.normalizer_core_eq_sylow_centralizer h hN hproper t htZ htz
    have hcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) = 1024 := by
      rw [← hKeq, card_map_of_injective N.subtype_injective]
      exact (d.normalizer_core_order h hN hproper).2.1
    have hkt : k ∈ centralizer ({t} : Set G) := (hKeq ▸ hk).2
    exact (sup_le hEC hFC) (d.t_centralizer_core_involution_mem_elementary_join
      h t ht htz hcard k ⟨hkJ, hkt⟩ hk2)
  · have hkHJ : kH ∉ J := fun hh => hkJ (mem_map_of_mem H.subtype hh)
    have hkH2 : kH ^ 2 = 1 := Subtype.ext hk2
    have hyHsq : yH ^ 2 = 1 := hyH2 ▸ pow_orderOf_eq_one yH
    have haJ : kH * yH ∈ J :=
      d.outer_involutions_mul_mem_core h kH yH hkT hyT hkH2 hyHsq hkHJ hyHJ
    let aJ : J := ⟨kH * yH, haJ⟩
    let : IsElementaryAbelian 2 (J ⧸ commutator J) :=
      (parrott_core_abelianization_structure z h).1
    have haD : aJ ^ 2 ∈ commutator J := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (commutator J) (aJ ^ 2) = 1
      rw [map_pow]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (J ⧸ commutator J)) _
    have hcomm : ⁅kH * yH, yH⁆ = (kH * yH) ^ 2 := by
      have hki : kH⁻¹ = kH := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hkH2)
      have hyi : yH⁻¹ = yH := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hyHsq)
      simp only [commutatorElement_def, mul_inv_rev, hki, hyi, pow_two]
      simp only [mul_assoc, ← pow_two yH, hyHsq, mul_one]
    have haC : k * y ∈ C := hcentral (kH * yH) haJ
      (by rw [hcomm]; exact mem_map_of_mem J.subtype haD)
    have hyC : y ∈ C := by
      intro v hv
      exact mem_centralizer_singleton_iff.mp hv.2
    have hh := C.mul_mem haC hyC
    have hysq : y ^ 2 = 1 := hy2 ▸ pow_orderOf_eq_one y
    have hky : k * y * y = k := by
      rw [mul_assoc, ← pow_two, hysq, mul_one]
    exact hky ▸ hh

end Stellmacher.Recognition.ParrottSecondElementaryData
