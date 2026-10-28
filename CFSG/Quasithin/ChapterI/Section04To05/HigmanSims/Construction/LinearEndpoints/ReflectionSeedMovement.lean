module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.ConjugateEndpointPair
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.OddCore
public import Theory.GroupTheory.NormalizerQuotientInner
public import Theory.GroupTheory.OddKernelInvolutionFibers
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedRadicals

/-!
# The original endpoint reflection moves the distinguished seed involution

The centralizer in the radical of a seed involution outside the plane is
exactly that plane. Its stabilizer inside the endpoint is the whole common
subgroup, by the orders 960 and 10752. Consequently a reflection outside
the common subgroup moves the same original involution. The movement
persists in the cubic odd-core quotient because the odd kernel is central.

The intentional same-package import-all edge reuses the private fixed-seed
calculation underlying the original paired radicals.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem radical_seed_centralizer (h : TypeAt z V) (W A : Subgroup G)
    (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (u : G) (huV : u ∈ V) (huW : u ∉ W) :
    A ⊓ centralizer ({u} : Set G) = W := by
  let := h.elementary
  have hWA : W ≤ A := hAP ▸ (show A ⊓ (normalizer (V : Set G)).pCoreIn 2 ≤ A from inf_le_left)
  apply le_antisymm
  · rintro a ⟨haA, hau⟩
    by_cases haP : a ∈ (normalizer (V : Set G)).pCoreIn 2
    · exact hAP ▸ (show a ∈ A ⊓ (normalizer (V : Set G)).pCoreIn 2 from ⟨haA, haP⟩)
    · exact (huW ((fixed_seed h W hWV hW4 a (hAC haA) haP u huV).mp
        (mem_centralizer_singleton_iff.mp hau))).elim
  · intro a ha
    exact ⟨hWA ha, mem_centralizer_singleton_iff.mpr (setLike_mul_comm (hWV ha) huV)⟩

private theorem endpoint_plane_stabilizer (h : TypeAt z V) (W P J : Subgroup G)
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (hP960 : Nat.card P = 960)
    (hJ : J ≤ P ⊓ normalizer (W : Set G)) (hJ192 : Nat.card J = 192) :
    P ⊓ normalizer (W : Set G) = J := by
  have hd₁ : Nat.card (P ⊓ normalizer (W : Set G) : Subgroup G) ∣ 960 :=
    hP960 ▸ card_dvd_of_le (show P ⊓ normalizer (W : Set G) ≤ P from inf_le_left)
  have hd₂ : Nat.card (P ⊓ normalizer (W : Set G) : Subgroup G) ∣ 10752 :=
    h.normalizer_card ▸ card_dvd_of_le
      (inf_le_right.trans (h.plane_normalizer_le_seed_normalizer W hWV hW4))
  have hd : Nat.card (P ⊓ normalizer (W : Set G) : Subgroup G) ∣ 192 := by
    have hh := Nat.dvd_gcd hd₁ hd₂
    norm_num at hh
    exact hh
  exact (eq_of_le_of_card_ge hJ (by
    rw [hJ192]
    exact Nat.le_of_dvd (by decide : 0 < 192) hd)).symm

/-- Every element of the same original endpoint outside its whole common
subgroup moves each original seed involution outside the fixed plane. -/
theorem TypeAt.endpoint_reflection_moves_seed (h : TypeAt z V)
    (W A : Subgroup G) [IsElementaryAbelian 2 A]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (d : NaturalEndpointData A) (J : Subgroup G)
    (hJ : J ≤ d.carrier ⊓ normalizer (W : Set G)) (hJ192 : Nat.card J = 192)
    (u : G) (huV : u ∈ V) (huW : u ∉ W)
    (r : G) (hr : r ∈ d.carrier) (hrJ : r ∉ J) :
    r * u * r⁻¹ ≠ u := by
  intro he
  have hrU : r ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have hrW : r ∈ normalizer (W : Set G) := by
    rw [← radical_seed_centralizer h W A hWV hW4 hAC hAP u huV huW]
    exact inf_normalizer_le_normalizer_inf
      ⟨d.normalizes hr, (centralizer ({u} : Set G)).le_normalizer hrU⟩
  exact hrJ (endpoint_plane_stabilizer h W d.carrier J hWV hW4 d.carrier_card hJ hJ192 ▸
    (show r ∈ d.carrier ⊓ normalizer (W : Set G) from ⟨hr, hrW⟩))

/-- The same original reflection moves the same marked involution in the
full cubic centralizer quotient. No replacement endpoint or reflection is
chosen, and the quotient action is the literal normalizer action. -/
theorem TypeAt.endpoint_reflection_moves_cubic_quotient (h : TypeAt z V)
    (W A : Subgroup G) [IsElementaryAbelian 2 A]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (d : NaturalEndpointData A) (J : Subgroup G)
    (hJ : J ≤ d.carrier ⊓ normalizer (W : Set G)) (hJ192 : Nat.card J = 192)
    (u : G) (huV : u ∈ V) (huW : u ∉ W)
    (t : G) (ht : t ∈ involutionCentralizer u) (ht3 : orderOf t = 3)
    (r : G) (hr : r ∈ d.carrier) (hrJ : r ∉ J)
    (hrC : r ∈ normalizer (centralizer ({t} : Set G) : Set G)) :
    let C := centralizer ({t} : Set G)
    let O := pPrimeCore 2 C
    ∀ uC : C, (uC : G) = u →
      normalizerQuotientAction C O ⟨r, hrC⟩ (QuotientGroup.mk' O uC) ≠
        QuotientGroup.mk' O uC := by
  intro C O uC huC he
  have hu1 : u ≠ 1 := fun he => huW (he ▸ W.one_mem)
  have huT := h.at_seed_point u huV hu1
  have hu2 : orderOf uC = 2 := by
    rw [← orderOf_coe, huC]
    exact huT.involution
  let q := QuotientGroup.mk' O
  let a := C.normalizerMonoidHom ⟨r, hrC⟩
  have heq : q (a uC) = q uC := by
    exact (quotientAut_apply_mk O a uC).symm.trans he
  have hker : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact pPrimeCore_coprime_card
  obtain ⟨k, hk⟩ := involutions_same_image_conj_ker q hker
    ((a.orderOf_eq uC).trans hu2) hu2 heq
  have hkO : (k : C) ∈ O := (QuotientGroup.eq_one_iff (k : C)).mp k.property
  have hkT : ((k : C) : G) ∈ zpowers t :=
    huT.cubic_centralizer_oddCore t ht ht3 ▸ mem_map_of_mem C.subtype hkO
  have haU : (a uC : G) ∈ centralizer (zpowers t : Set G) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using (a uC).property
  have hc : ((k : C) : G) * (a uC : G) = (a uC : G) * ((k : C) : G) :=
    haU _ hkT
  have hh := congrArg (fun x : C => (x : G)) hk
  change ((k : C) : G) * (a uC : G) * ((k : C) : G)⁻¹ = (uC : G) at hh
  rw [hc, mul_inv_cancel_right] at hh
  apply h.endpoint_reflection_moves_seed W A hWV hW4 hAC hAP d J hJ hJ192 u huV huW r hr hrJ
  change r * (uC : G) * r⁻¹ = (uC : G) at hh
  rwa [huC] at hh

end CFSG.Quasithin.HigmanSims
