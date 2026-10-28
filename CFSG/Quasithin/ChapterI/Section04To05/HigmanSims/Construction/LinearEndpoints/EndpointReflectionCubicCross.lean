module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCubic
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.MixedProduct
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.InvertedCubicCommutator

/-!
# The original endpoint reflection controls freely selected cubic generators

The original TypeAt geometry forces the selected reflection to act as a
transposition on the cubic-centralizer quotient. Consequently any two cubics
centralizing the same torus and inverted by that reflection have commutator
of square one. The two cubics may be selected anew; neither is required to
be the mixed product arising from the initial conjugate reflection marking.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Two freely selected cubics satisfy the cross-relation under the same
original torus and reflection, whose action is forced by TypeAt geometry. -/
theorem TypeAt.endpoint_reflection_cubic_cross_relation (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hA16 : Nat.card A = 16) (hB16 : Nat.card B = 16)
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (hBP : B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (hC : A ⊔ B ≤ centralizer (W : Set G))
    (hBA : B ≤ normalizer (A : Set G))
    (d : NaturalEndpointData A) (hBd : B ≤ d.carrier)
    (h64 : Nat.card (A ⊔ B : Subgroup G) = 64)
    (hpureB : ∀ b ∈ B, b ≠ 1 → IsConj b z)
    (hpointsB : ∀ b ∈ B, b ≠ 1 →
      Nat.card (B ⊓ (involutionCentralizer b).pCoreIn 2 : Subgroup G) = 8)
    (u c t r : G) (huV : u ∈ V) (huW : u ∉ W)
    (hcP : c ∈ (normalizer (V : Set G)).pCoreIn 2)
    (hc2 : c ^ 2 = u) (hct : Commute c t)
    (hB : B = A.map (MulAut.conj c).toMonoidHom)
    (ht3 : orderOf t = 3)
    (ht : t ∈ d.carrier) (hr : r ∈ d.carrier)
    (hrJ : r ∉ (A ⊔ B) ⊔ zpowers t)
    (hr2 : orderOf r = 2) (hinv : r * t * r⁻¹ = t⁻¹)
    (ell n : G) (hellt : Commute ell t) (hnt : Commute n t)
    (hell3 : ell ^ 3 = 1) (hn3 : n ^ 3 = 1)
    (hrell : r * ell * r⁻¹ = ell⁻¹) (hrn : r * n * r⁻¹ = n⁻¹) :
    ⁅ell, n⁆ ^ 2 = 1 := by
  have hWA : W ≤ A := hAP ▸
    (show A ⊓ (normalizer (V : Set G)).pCoreIn 2 ≤ A from inf_le_left)
  have hWB : W ≤ B := hBP ▸
    (show B ⊓ (normalizer (V : Set G)).pCoreIn 2 ≤ B from inf_le_left)
  have hAC : A ≤ centralizer (W : Set G) := le_sup_left.trans hC
  have hu1 : u ≠ 1 := fun he => huW (he ▸ W.one_mem)
  have huT := h.at_seed_point u huV hu1
  have huP : u ∈ (normalizer (V : Set G)).pCoreIn 2 := hc2 ▸ pow_mem hcP 2
  have huN : u ∈ normalizer (A : Set G) :=
    (h.plane_radical_core_normalizer W A hWV hW4 hA16 hWA hAC hAP u huP).mpr
      (by rw [show u ^ 2 = 1 from huT.involution ▸ pow_orderOf_eq_one u]; exact W.one_mem)
  have hut : Commute u t := hc2 ▸ hct.pow_left 2
  have htU : t ∈ involutionCentralizer u := mem_centralizer_singleton_iff.mpr hut.symm.eq
  have hcW : c ^ 2 ∉ W := by rwa [hc2]
  have hrA : r ∉ A := fun he => hrJ (mem_sup_left (mem_sup_left he))
  obtain ⟨v, _, k, hvE, hv2, hvr, _, _, _, _, _, hk4, hk2, _, _, hkt, hrk⟩ :=
    h.endpoint_reflection_fixed_root W A B hWV hW4 hWA hWB hB16 hAC hAP hBP
      c hcP hcW hB hBA d hBd h64 hpureB hpointsB u t r
        huV huW huN hut ht ht3 hr hrA hr2 hinv
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  let q := QuotientGroup.mk' O
  obtain ⟨φ⟩ := huT.cubic_centralizer_quotient_perm_five d t htU ht ht3 huN
  obtain ⟨hrC, a, ha, _, heval⟩ := huT.cubic_quotient_reflection_transposition d
    t r v k htU ht ht3 huN hr hr2 hinv hvE hv2 hvr hkt hk4 hk2 hrk φ
  let ellC : C := ⟨ell, mem_centralizer_singleton_iff.mpr hellt.eq⟩
  let nC : C := ⟨n, mem_centralizer_singleton_iff.mpr hnt.eq⟩
  have hellC3 : ellC ^ 3 = 1 := Subtype.ext hell3
  have hnC3 : nC ^ 3 = 1 := Subtype.ext hn3
  have hαell : C.normalizerMonoidHom ⟨r, hrC⟩ ellC = ellC⁻¹ := Subtype.ext hrell
  have hαn : C.normalizerMonoidHom ⟨r, hrC⟩ nC = nC⁻¹ := Subtype.ext hrn
  have hax : a * φ (q ellC) * a⁻¹ = (φ (q ellC))⁻¹ := by
    rw [heval, hαell, map_inv, map_inv]
  have hay : a * φ (q nC) * a⁻¹ = (φ (q nC))⁻¹ := by
    rw [heval, hαn, map_inv, map_inv]
  exact huT.cubic_centralizer_inverted_cubics_commutator_square t htU ht3
    φ ellC nC hellC3 hnC3 a ha hax hay

end CFSG.Quasithin.HigmanSims
