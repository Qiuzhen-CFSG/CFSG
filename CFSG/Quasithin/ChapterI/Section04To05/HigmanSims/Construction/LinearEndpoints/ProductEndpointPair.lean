module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.MixedProduct
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.EndpointModel
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.CubicReflections
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.CubicReflections

/-!
# The original conjugate endpoint pair with its mixed cubic relation

The original TypeAt construction retains both actual endpoint carriers,
whole intersection, all radical/core markings, the first opposite-root
marking, and the same conjugate involutions. Their product now has order
three by the original cubic-centralizer and reflection-root argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

/-- Original HS local data supply the same marked conjugate endpoints and
actual reflections whose product has order three. -/
theorem TypeAt.exists_root_marked_conjugate_endpoint_pair (h : TypeAt z V) :
    ∃ (W A B : Subgroup G) (u c t : G) (hAE : IsElementaryAbelian 2 A)
      (hBE : IsElementaryAbelian 2 B), letI := hAE; letI := hBE
      W ≤ V ∧ Nat.card W = 4 ∧ Nat.card A = 16 ∧ Nat.card B = 16 ∧
      A ≤ normalizer (B : Set G) ∧ B ≤ normalizer (A : Set G) ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ B = W ∧ ⁅A, B⁆ ≤ W ∧ Nat.card (A ⊔ B : Subgroup G) = 64 ∧
      A ⊔ B ≤ centralizer (W : Set G) ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧ (∀ x ∈ B, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ x ∈ B, x ≠ 1 → Nat.card (B ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      u ∈ V ∧ u ≠ 1 ∧ u ∉ W ∧ TypeAt u V ∧
      V ⊓ centralizer ({t} : Set G) = zpowers u ∧
      c ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ c ^ 2 = u ∧ orderOf c = 4 ∧ Commute c t ∧
      (normalizer (V : Set G)).pCoreIn 2 ⊓ centralizer ({t} : Set G) = zpowers c ∧
      B = A.map (MulAut.conj c).toMonoidHom ∧ A = B.map (MulAut.conj c).toMonoidHom ∧
      orderOf t = 3 ∧ t ∈ normalizer (W : Set G) ∧
      Disjoint (A ⊔ B) (zpowers t) ∧
      ∃ (d : NaturalEndpointData A) (hBA : B ≤ normalizer (A : Set G)),
        Representation.SL2FourNatural.BorelFactors.U0.map d.embedding =
          ((d.symplectic_quotient.toMonoidHom.comp
            (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))).comp
              (inclusion hBA)).range ∧
        let P₂ := d.carrier.map (MulAut.conj c).toMonoidHom
        let J := (A ⊔ B) ⊔ zpowers t
        B ≤ d.carrier ∧ A ≤ P₂ ∧ B ≤ P₂ ∧ t ∈ d.carrier ⊓ P₂ ∧
        P₂ ≤ normalizer (B : Set G) ∧ Nat.card P₂ = 960 ∧
        d.carrier ⊓ P₂ = J ∧ Nat.card J = 192 ∧ c ∈ normalizer (J : Set G) ∧
        d.carrier.pCoreIn 2 = A ∧ P₂.pCoreIn 2 = B ∧
        ∃ (e₁ : d.carrier ≃* Point) (e₂ : P₂ ≃* Point) (k : d.carrier ≃* P₂),
          (A.subgroupOf d.carrier).map e₁.toMonoidHom = pCore 2 Point ∧
          (B.subgroupOf P₂).map e₂.toMonoidHom = pCore 2 Point ∧
          (∀ x, (k x : G) = c * (x : G) * c⁻¹) ∧ (∀ x, e₂ (k x) = e₁ x) ∧
          ∃ r s : G, r ∈ d.carrier ∧ s ∈ P₂ ∧ s = c * r * c⁻¹ ∧
            r ∉ J ∧ s ∉ J ∧ orderOf r = 2 ∧ orderOf s = 2 ∧
            r * t * r⁻¹ = t⁻¹ ∧ s * t * s⁻¹ = t⁻¹ ∧
            r * s ∈ centralizer ({t} : Set G) ∧ r * s ≠ 1 ∧ orderOf (r*s)=3 := by
  obtain ⟨W,A,B,p,t,hAE,hBE,hAB,hBA,hWV,hW4,hA16,hB16,hp,hpW,hB,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,ht3,htW,hdis,h192,d,dB,hBd,
    _,htd,_,hRA,_⟩ := h.exists_paired_natural_endpoints
  let := hAE
  let := hBE
  have hWA : W ≤ A := hi ▸ (show A ⊓ B ≤ A from inf_le_left)
  have hAC : A ≤ centralizer (W : Set G) := le_sup_left.trans hC
  obtain ⟨u,c,huV,hu1,huW,huT,hVfix,hcP,hc2,hc4,hct,hPfix,hBc⟩ :=
    h.paired_endpoint_cubic_conjugating_core W A B hWV hW4 hA16 hWA hAC hAP
      p hp hpW hB d t htd.1 htW ht3
  let α := MulAut.conj c
  let P₂ := d.carrier.map α.toMonoidHom
  let S := A ⊔ B
  let J := S ⊔ zpowers t
  have hcW : c ^ 2 ∉ W := by rwa [hc2]
  have hcSqN : c ^ 2 ∈ normalizer (A : Set G) :=
    (h.plane_radical_core_normalizer W A hWV hW4 hA16 hWA hAC hAP
      (c ^ 2) (pow_mem hcP 2)).mpr (by
        rw [← pow_mul, show 2 * 2 = orderOf c from hc4.symm, pow_orderOf_eq_one]
        exact W.one_mem)
  have hAc : A = B.map α.toMonoidHom := by
    rw [hBc, map_map]
    have he : α.toMonoidHom.comp α.toMonoidHom = (MulAut.conj (c ^ 2)).toMonoidHom := by
      ext x
      change c * (c * x * c⁻¹) * c⁻¹ = c ^ 2 * x * (c ^ 2)⁻¹
      simp only [pow_two]
      group
    rw [he]
    exact (mem_normalizer_iff_map_conj_eq.mp hcSqN).symm
  have hSmap : S.map α.toMonoidHom = S := by
    change (A ⊔ B).map α.toMonoidHom = A ⊔ B
    rw [Subgroup.map_sup, ← hBc, ← hAc, sup_comm]
  have hαt : α t = t := by
    change c * t * c⁻¹ = t
    rw [hct.eq, mul_inv_cancel_right]
  have hJmap : J.map α.toMonoidHom = J := by
    change (S ⊔ zpowers t).map α.toMonoidHom = S ⊔ zpowers t
    rw [Subgroup.map_sup, hSmap, MonoidHom.map_zpowers, show α.toMonoidHom t = t from hαt]
  have hcJN : c ∈ normalizer (J : Set G) := mem_normalizer_iff_map_conj_eq.mpr hJmap
  have hAP₂ : A ≤ P₂ := by
    rw [hAc]
    exact map_mono hBd
  have hBP₂ : B ≤ P₂ := by
    rw [hBc]
    exact map_mono d.kernel_le
  have htP₂ : t ∈ P₂ := ⟨t, htd.1, hαt⟩
  have hP₂N : P₂ ≤ normalizer (B : Set G) := by
    have hh := map_mono (f := α.toMonoidHom) d.normalizes
    rw [map_equiv_normalizer_eq, ← hBc] at hh
    exact hh
  have hP₂card : Nat.card P₂ = 960 :=
    (card_map_of_injective α.injective).trans d.carrier_card
  have hJle : J ≤ d.carrier ⊓ P₂ :=
    sup_le (sup_le (le_inf d.kernel_le hAP₂) (le_inf hBd hBP₂))
      (zpowers_le.mpr ⟨htd.1, htP₂⟩)
  have hinter : d.carrier ⊓ P₂ = J :=
    h.paired_endpoint_whole_intersection W A hWV hW4 hA16 hWA hAC hAP c hcP hcW
      d.carrier P₂ J d.normalizes (hBc ▸ hP₂N) d.carrier_card hJle h192
  obtain ⟨hcore₁,e₁,he₁⟩ := point_parabolic_of_natural_endpoint A d.carrier d.complement
    d.kernel_le d.normalizes d.quotient d.quotient_surjective d.quotient_kernel
    d.coordinates d.action d.is_complement
  have hcore₂ : P₂.pCoreIn 2 = B := by
    change (d.carrier.map α.toMonoidHom).pCoreIn 2 = B
    rw [← map_pCoreIn_of_injective 2 _ _ α.injective, hcore₁]
    exact hBc.symm
  let k : d.carrier ≃* P₂ := d.carrier.equivMapOfInjective α.toMonoidHom α.injective
  let e₂ : P₂ ≃* Point := k.symm.trans e₁
  have hcore₂' : pCore 2 P₂ = B.subgroupOf P₂ := by
    apply map_injective P₂.subtype_injective
    rw [map_subgroupOf_eq_of_le hBP₂]
    exact hcore₂
  have he₂ : (B.subgroupOf P₂).map e₂.toMonoidHom = pCore 2 Point := by
    rw [← hcore₂', pCore_map_iso]
  have hJN : J ≤ normalizer (S : Set G) := by
    rw [← hinter]
    exact (le_trans (le_inf (inf_le_left.trans d.normalizes) (inf_le_right.trans hP₂N))
      (normalizer_inf_normalizer_le_normalizer_sup A B))
  have htJ : t ∈ J := mem_sup_right (mem_zpowers t)
  obtain ⟨r,hr,hr2,hrt⟩ := d.cubic_inverting_involution t htd.1 ht3
  let s := α r
  have hs : s ∈ P₂ := mem_map_of_mem α.toMonoidHom hr
  have hs2 : orderOf s = 2 := (α.orderOf_eq r).trans hr2
  have hst : s * t * s⁻¹ = t⁻¹ := by
    have hh := congrArg α hrt
    simpa only [map_mul, map_inv, hαt] using hh
  have hrJ : r ∉ J := inverting_not_in_common S J le_sup_left hJN h64 h192 t htJ ht3 r hr2 hrt
  have hsJ : s ∉ J := inverting_not_in_common S J le_sup_left hJN h64 h192 t htJ ht3 s hs2 hst
  have hrs : r * s ∈ centralizer ({t} : Set G) := by
    have he : (r*s) * t * (r*s)⁻¹ = t := by
      calc
        (r*s) * t * (r*s)⁻¹ = r * (s*t*s⁻¹) * r⁻¹ := by group
        _ = r * t⁻¹ * r⁻¹ := by rw [hst]
        _ = (r*t*r⁻¹)⁻¹ := by group
        _ = t := by rw [hrt, inv_inv]
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have hrs1 : r * s ≠ 1 := by
    intro he
    have hrP₂ : r ∈ P₂ := (eq_inv_of_mul_eq_one_left he) ▸ P₂.inv_mem hs
    exact hrJ (hinter ▸ (show r ∈ d.carrier ⊓ P₂ from ⟨hr,hrP₂⟩))
  refine ⟨W,A,B,u,c,t,hAE,hBE,hWV,hW4,hA16,hB16,hAB,hBA,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,huV,hu1,huW,huT,hVfix,
    hcP,hc2,hc4,hct,hPfix,hBc,hAc,ht3,htW,hdis,d,hBA,hRA,hBd,hAP₂,hBP₂,⟨htd.1,htP₂⟩,
    hP₂N,hP₂card,hinter,h192,hcJN,hcore₁,hcore₂,e₁,e₂,k,he₁,he₂,?_,?_,
    r,s,hr,hs,rfl,hrJ,hsJ,hr2,hs2,hrt,hst,hrs,hrs1,?_⟩
  · intro x
    rfl
  · intro x
    exact congrArg e₁ (k.symm_apply_apply x)
  · exact h.endpoint_conjugate_reflection_product_order W A B hWV hW4 hA16 hB16
      hAP hBP hC hBA d hBd h64 hpureB hpointsB u c t r huV huW hcP hc2 hc4 hct
      hBc ht3 htW h192 htd.1 hr hrJ hr2 hrt

end CFSG.Quasithin.HigmanSims
