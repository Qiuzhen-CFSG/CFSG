module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.QuotientReflectionAction
public import Theory.SpecificGroups.SymmetricFive.MarkedCubicRootReflection
import Mathlib.GroupTheory.Perm.Fin

/-!
# The original reflection has a transposition actor on the cubic quotient

The actual fixed involution in the marked order-six image identifies the
inner actor of the reflection there. An actual inverted cyclic-four root
then distinguishes the transposition actor on the specified S5 quotient.
The original quotient map and any given quotient marking are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

set_option synthInstance.maxSize 1024 in
private theorem symmetric_three_commuting_involutions :
    ∀ a b : Equiv.Perm (Fin 3), a ≠ 1 → b ≠ 1 →
      a^2=1 → b^2=1 → a*b=b*a → a=b := by
  decide +kernel

/-- A reflection with its actual fixed involution and inverted cyclic-four
root induces a transposition on any specified marking of the original
cubic-centralizer quotient. -/
theorem TypeAt.cubic_quotient_reflection_transposition (h : TypeAt z V)
    {A : Subgroup G} [IsElementaryAbelian 2 A] (d : NaturalEndpointData A)
    (t r v c : G) (htz : t∈involutionCentralizer z) (ht : t∈d.carrier)
    (ht3 : orderOf t=3) (hzN : z∈normalizer (A : Set G))
    (hr : r∈d.carrier) (hr2 : orderOf r=2) (hinv : r*t*r⁻¹=t⁻¹)
    (hvE : v∈normalizer (A : Set G)⊓centralizer ({t} : Set G))
    (hv2 : orderOf v=2) (hvr : Commute v r) (hct : Commute c t)
    (hc4 : orderOf c=4) (hc2 : c^2=v) (hrc : r*c*r⁻¹=c⁻¹)
    (φ : ((centralizer ({t} : Set G))⧸pPrimeCore 2 (centralizer ({t} : Set G)))
      ≃* Equiv.Perm (Fin 5)) :
    let C := centralizer ({t} : Set G)
    let O := pPrimeCore 2 C
    let q := QuotientGroup.mk' O
    ∃ hrC : r∈normalizer (C : Set G),
      ∃ a : Equiv.Perm (Fin 5), a.IsSwap ∧
        (MulAut.congr φ) (normalizerQuotientAction C O ⟨r,hrC⟩)=MulAut.conj a ∧
        ∀ x : C, a*φ (q x)*a⁻¹=φ (q (C.normalizerMonoidHom ⟨r,hrC⟩ x)) := by
  classical
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  let X := C⧸O
  let q := QuotientGroup.mk' O
  let E := normalizer (A : Set G)⊓C
  let H := (E.subgroupOf C).map q
  obtain ⟨hrC,β,_,hβ2,hβ,hαq,k,hk2,hβk⟩ :=
    h.cubic_quotient_reflection_inner d t r htz ht ht3 hzN hr hr2 hinv
  let α := normalizerQuotientAction C O ⟨r,hrC⟩
  let α5 := (MulAut.congr φ) α
  obtain ⟨_,_,_,_,hH6,_,⟨eH⟩,_⟩ := h.cubic_quotient_marked_six d t htz ht ht3 hzN
  have hO : O.map C.subtype=zpowers t := h.cubic_centralizer_oddCore t htz ht3
  have hk3 : Nat.card q.ker=3 := by
    rw [QuotientGroup.ker_mk',←card_map_of_injective C.subtype_injective,hO,Nat.card_zpowers,ht3]
  have hker : IsPGroup 3 q.ker := IsPGroup.of_card (n:=1) (by simpa using hk3)
  let vC : C := ⟨v,hvE.2⟩
  let cC : C := ⟨c,mem_centralizer_singleton_iff.mpr hct.eq⟩
  have hvC2 : orderOf vC=2 := (orderOf_coe vC).symm.trans hv2
  have hcC4 : orderOf cC=4 := (orderOf_coe cC).symm.trans hc4
  have hqv2 : orderOf (q vC)=2 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hker vC (by rw [hvC2]; decide)).trans hvC2
  have hqc4 : orderOf (q cC)=4 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hker cC (by rw [hcC4]; decide)).trans hcC4
  have hvH : q vC∈H := mem_map_of_mem q hvE
  let vH : H := ⟨q vC,hvH⟩
  have hvH2 : orderOf vH=2 := (orderOf_coe vH).symm.trans hqv2
  have hrvc : C.normalizerMonoidHom ⟨r,hrC⟩ vC=vC := by
    apply Subtype.ext
    change r*v*r⁻¹=v
    rw [hvr.symm.eq,mul_inv_cancel_right]
  have hβv : β vH=vH := by
    apply Subtype.ext
    rw [hβ]
    change α (q vC)=q vC
    rw [hαq,hrvc]
  have hkv : k=vH := by
    apply eH.injective
    apply symmetric_three_commuting_involutions
    · intro he
      have hh := eH.orderOf_eq k
      rw [he,hk2,orderOf_one] at hh
      omega
    · intro he
      have hh := eH.orderOf_eq vH
      rw [he,hvH2,orderOf_one] at hh
      omega
    · rw [←map_pow,show k^2=1 by simpa only [hk2] using pow_orderOf_eq_one k,map_one]
    · rw [←map_pow,show vH^2=1 by simpa only [hvH2] using pow_orderOf_eq_one vH,map_one]
    · rw [←map_mul,←map_mul]
      apply congrArg eH
      have hh : k*vH*k⁻¹=vH := by simpa only [hβk,MulAut.conj_apply] using hβv
      exact mul_inv_eq_iff_eq_mul.mp hh
  have hα2 : α^2=1 := by
    change (normalizerQuotientAction C O ⟨r,hrC⟩)^2=1
    rw [←map_pow]
    have hh : (⟨r,hrC⟩ : normalizer (C : Set G))^2=1 :=
      Subtype.ext (hr2 ▸ pow_orderOf_eq_one r)
    rw [hh,map_one]
  have hα52 : α5^2=1 := by rw [←map_pow,hα2,map_one]
  obtain ⟨s,hs⟩ := exists_prime_orderOf_dvd_card' (G:=H) 3 (by rw [hH6]; decide)
  have hsX : orderOf (s : X)=3 := (orderOf_coe s).trans hs
  have hs5 : orderOf (φ (s : X))=3 := (φ.orderOf_eq _).trans hsX
  have hc5 : orderOf (φ (q cC))=4 := (φ.orderOf_eq _).trans hqc4
  have hrcC : C.normalizerMonoidHom ⟨r,hrC⟩ cC=cC⁻¹ := Subtype.ext hrc
  have hαc : α5 (φ (q cC))=(φ (q cC))⁻¹ := by
    change φ (α (φ.symm (φ (q cC))))=(φ (q cC))⁻¹
    rw [φ.symm_apply_apply,hαq,hrcC,map_inv,map_inv]
  have hcs : α5 (φ (s : X))=(φ (q cC))^2*φ (s : X)*((φ (q cC))^2)⁻¹ := by
    have hαs : α (s : X)=q vC*(s : X)*(q vC)⁻¹ := by
      rw [←hβ,hβk,hkv]
      rfl
    have hqcv : (q cC)^2=q vC := by
      rw [←map_pow]
      exact congrArg q (Subtype.ext hc2)
    change φ (α (φ.symm (φ (s : X))))=_
    rw [φ.symm_apply_apply,hαs,map_mul,map_mul,map_inv,←hqcv,map_pow]
  obtain ⟨a,ha,hαa⟩ :=
    Theory.SpecificGroups.SymmetricFive.involutive_automorphism_transposition_of_inverted_root
      α5 hα52 (φ (s : X)) (φ (q cC)) hs5 hc5 hαc hcs
  refine ⟨hrC,a,ha,hαa,?_⟩
  intro x
  have hh := DFunLike.congr_fun hαa (φ (q x))
  change φ (α (φ.symm (φ (q x))))=a*φ (q x)*a⁻¹ at hh
  rw [φ.symm_apply_apply,hαq] at hh
  exact hh.symm

end CFSG.Quasithin.HigmanSims
