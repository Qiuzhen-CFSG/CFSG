module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.ReflectionFixedSeed
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.EndpointInvolutionPointCore
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointRootCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.FixedCore
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCore
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.FixedCore

/-!
# An actual cyclic-four root inverted by the same endpoint reflection

The endpoint reflection fixes a marked involution in the full normalizer
cubic centralizer. Its literal conjugate seed contains the original
point-core line of the reflection. The reflection lies outside that seed's
whole cyclic-four core, since its cubic inversion survives the point-core
quotient. The determinant-one root obstruction then forces it to invert
the central cyclic-four generator, which centralizes the same cubic.

The two intentional same-package import-all edges reuse square-one
recognition in the whole core and the odd-order fixation of its central
cyclic-four generator. No actor classification or mixed relation is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem cubic_inverter_not_point_core (v t r : G)
    (ht : t ∈ involutionCentralizer v) (hr : r ∈ involutionCentralizer v)
    (ht3 : orderOf t = 3) (hinv : r * t * r⁻¹ = t⁻¹) :
    r ∉ (involutionCentralizer v).pCoreIn 2 := by
  let H := involutionCentralizer v
  let q := QuotientGroup.mk' (pCore 2 H)
  let tH : H := ⟨t,ht⟩
  let rH : H := ⟨r,hr⟩
  have htH3 : orderOf tH = 3 := (orderOf_coe tH).symm.trans ht3
  have hq3 : orderOf (q tH) = 3 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) tH
      (by rw [htH3]; decide)).trans htH3
  intro hrQ
  have hrK : rH ∈ pCore 2 H :=
    (mem_map_iff_mem H.subtype_injective (K := pCore 2 H) (x := rH)).mp hrQ
  have hqr : q rH = 1 := (QuotientGroup.eq_one_iff rH).mpr hrK
  have hi : q tH = (q tH)⁻¹ := by
    have hh := congrArg q (show rH * tH * rH⁻¹ = tH⁻¹ from Subtype.ext hinv)
    simpa only [map_mul,map_inv,hqr,one_mul,inv_one,mul_one] using hh
  have hq2 : (q tH) ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp hi
  have hd := orderOf_dvd_of_pow_eq_one hq2
  rw [hq3] at hd
  norm_num at hd

/-- Original paired endpoint data provide a central order-four root at
the reflection's fixed seed point, centralized by the same cubic and
inverted by the same reflection. The conjugator and literal seed survive. -/
theorem TypeAt.endpoint_reflection_fixed_root (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (hWA : W ≤ A) (hWB : W ≤ B)
    (hB16 : Nat.card B = 16) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (hBP : B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W)
    (hB : B = A.map (MulAut.conj p).toMonoidHom)
    (hBA : B ≤ normalizer (A : Set G))
    (d : NaturalEndpointData A) (hBd : B ≤ d.carrier)
    (h64 : Nat.card (A ⊔ B : Subgroup G) = 64)
    (hpureB : ∀ b ∈ B, b ≠ 1 → IsConj b z)
    (hpointsB : ∀ b ∈ B, b ≠ 1 →
      Nat.card (B ⊓ (involutionCentralizer b).pCoreIn 2 : Subgroup G) = 8)
    (u t r : G) (huV : u ∈ V) (huW : u ∉ W)
    (huN : u ∈ normalizer (A : Set G)) (hut : Commute u t)
    (ht : t ∈ d.carrier) (ht3 : orderOf t = 3)
    (hr : r ∈ d.carrier) (hrA : r ∉ A) (hr2 : orderOf r = 2)
    (hinv : r * t * r⁻¹ = t⁻¹) :
    let E := normalizer (A : Set G) ⊓ centralizer ({t} : Set G)
    ∃ v g c : G, v ∈ E ∧ orderOf v = 2 ∧ Commute v r ∧
      g ∈ E ∧ g * u * g⁻¹ = v ∧
      TypeAt v (V.map (MulAut.conj g).toMonoidHom) ∧
      V.map (MulAut.conj g).toMonoidHom = zpowers v ⊔ (A ⊓ centralizer ({v} : Set G)) ∧
      Nat.card (A ⊓ centralizer ({v} : Set G) : Subgroup G) = 4 ∧
      orderOf c = 4 ∧ c ^ 2 = v ∧
      c ∈ (center ((involutionCentralizer v).pCoreIn 2)).map
        ((involutionCentralizer v).pCoreIn 2).subtype ∧
      c ∈ (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)).pCoreIn 2 ∧
      Commute c t ∧ r * c * r⁻¹ = c⁻¹ := by
  obtain ⟨v,g,hvE,hv2,hvr,hgE,hgu,hvT,hseed,hplane⟩ :=
    h.endpoint_reflection_fixed_seed W A hWV hW4 hAC hAP d u t r
      huV huW huN hut ht ht3 hr hr2 hinv
  let U := V.map (MulAut.conj g).toMonoidHom
  have hv1 : v ≠ 1 := by intro he; simp [he] at hv2
  have hvA : v ∉ A := by
    intro he
    have hh : v ∈ A ⊓ centralizer ({t} : Set G) := ⟨he,hvE.2⟩
    rw [d.cubic_radical_centralizer t ht ht3] at hh
    exact hv1 hh
  obtain ⟨_,w,hwA,hw2,_,hrQw,_,hfix⟩ := h.endpoint_involution_point_core
    W A B hWV hW4 hWA hWB hB16 hAC hAP hBP p hp hpW hB hBA d hBd
      h64 hpureB hpointsB r hr hrA hr2
  have hvw : Commute v w := hfix v hvE.1 hvr
  have hwU : w ∈ U := by
    rw [show U = zpowers v ⊔ (A ⊓ centralizer ({v} : Set G)) from hseed]
    exact mem_sup_right ⟨hwA,mem_centralizer_singleton_iff.mpr hvw.symm.eq⟩
  have hw1 : w ≠ 1 := by intro he; simp [he] at hw2
  have hwv : w ≠ v := fun he => hvA (he ▸ hwA)
  have hrv : r ∈ involutionCentralizer v := mem_centralizer_singleton_iff.mpr hvr.symm.eq
  have htv : t ∈ involutionCentralizer v :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hvE.2).symm
  have hrSq : r ^ 2 = 1 := hr2 ▸ pow_orderOf_eq_one r
  have hrP : r ∉ (normalizer (U : Set G)).pCoreIn 2 := by
    intro he
    have hrU : r ∈ U := (core_square_one hvT r he).mp hrSq
    have hrQ : r ∈ (involutionCentralizer v).pCoreIn 2 := by
      change r ∈ (pCore 2 (involutionCentralizer v)).map (involutionCentralizer v).subtype
      rw [← hvT.centralizer_fitting]
      exact hvT.seed_le_core hrU
    exact cubic_inverter_not_point_core v t r htv hrv ht3 hinv hrQ
  obtain ⟨c,hc4,hc2,hcZ,hcP⟩ := hvT.exists_point_core_central_four
  have hct : Commute c t := cubic_central_four hvT t c htv ht3 hc4 hcZ
  have hnc : ¬ Commute r c := hvT.point_core_involution_not_commute_root
    w v r c hwU hw1 hvT.involution_mem_seed hv1 hwv hrQw hrSq hrP hvr.symm hcP hc2
  have hrc := hvT.point_core_central_four_inverted c hc4 hcZ r hrv hnc
  exact ⟨v,g,c,hvE,hv2,hvr,hgE,hgu,hvT,hseed,hplane,hc4,hc2,hcZ,hcP,hct,hrc⟩

end CFSG.Quasithin.HigmanSims
