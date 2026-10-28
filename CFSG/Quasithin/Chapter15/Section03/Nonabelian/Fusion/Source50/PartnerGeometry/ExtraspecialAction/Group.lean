module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Actor
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The extraspecial partner kernel and centralizer

The source orders make E a maximal abelian subgroup of Uʸ. The two disjoint
commutator lines then identify X∩Q_H with E, so the actual actor image is
an elementary group of order 2^(s+1). The centralizer of the index-two X
in Uʸ has order at most four: modulo the center, one commutator detects it.
The marked four-group V₀ attains this bound, giving C_E(X)=V₀.

Source: Aschbacher–Smith, 15.3.56(3–4), printed pp.1147–1148.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
variable {G : Type*} [Group G]

private theorem commutator_mem_extraspecial_center
    {P : Type*} [Group P] [IsExtraspecial 2 P] (x y : P) : ⁅x,y⁆ ∈ center P := by
  let := IsExtraspecial.quotient_elementary_abelian 2 P
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (center P) ⁅x,y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

private theorem index_two_centralizer_card_le
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (X : Subgroup P) (hindex : X.index=2) : Nat.card (centralizer (X:Set P))  ≤  4 := by
  obtain ⟨a, _, ha⟩ := index_eq_two_iff_exists_notMem_and.mp hindex
  let C := centralizer (X:Set P)
  let f : C →* center P := {
    toFun c := ⟨⁅a,(c:P)⁆, commutator_mem_extraspecial_center a c⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' c d := by
      apply Subtype.ext
      change ⁅a,(c:P)*(d:P)⁆ = ⁅a,(c:P)⁆ * ⁅a,(d:P)⁆
      rw [commutatorElement_mul_right_eq_mul_conj,
        mul_assoc ⁅a,(c:P)⁆ (c:P),
        mem_center_iff.mp (commutator_mem_extraspecial_center a (d:P)) (c:P)]
      simp only [← mul_assoc, mul_inv_cancel_right] }
  have hZC : center P  ≤  C := center_le_centralizer _
  have hk : f.ker = (center P).subgroupOf C := by
    ext c
    change (⟨⁅a,(c:P)⁆,_⟩ : center P)=1 ↔ (c:P)∈center P
    rw [Subtype.ext_iff, coe_one, commutatorElement_eq_one_iff_mul_comm, mem_center_iff]
    constructor
    · intro hac b
      rcases ha b with hb | hb
      · have hh := c.property (b*a) hb
        have he : b*a*(c:P) = b*(c:P)*a := by rw [mul_assoc, hac, ← mul_assoc]
        rw [he, ← mul_assoc] at hh
        exact mul_right_cancel hh
      · exact c.property b hb
    · exact fun hc => hc a
  have hkc : Nat.card f.ker=2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv]
    exact IsExtraspecial.center_order_p 2 P
  have hr : Nat.card f.range  ≤  2 := by
    rw [← IsExtraspecial.center_order_p 2 P]
    exact Nat.card_le_card_of_injective _ f.range.subtype_injective
  have hh := f.ker.card_mul_index
  rw [hkc, index_ker] at hh
  change 2 * Nat.card f.range = Nat.card (centralizer (X:Set P)) at hh
  omega

private theorem conjugate_extraspecial
    (P : Subgroup G) [IsExtraspecial 2 P] (y : G) :
    IsExtraspecial 2 (rightConjugate P y) :=
  IsExtraspecial.of_mulEquiv
    (P.equivMapOfInjective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective)
    inferInstance

private theorem conjugate_center (P Z : Subgroup G) (y : G) (hZP : Z ≤ P)
    (hcenter : center P=Z.subgroupOf P) :
    center (rightConjugate P y)=(rightConjugate Z y).subgroupOf (rightConjugate P y) := by
  let e := P.equivMapOfInjective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective
  ext u
  constructor
  · intro hu
    have hc := (centerCongr e.symm ⟨u,hu⟩).property
    change e.symm u ∈ center P at hc
    rw [hcenter] at hc
    exact ⟨(e.symm u:G),hc,congrArg Subtype.val (e.apply_symm_apply u)⟩
  · rintro ⟨z,hz,he⟩
    let zP : P := ⟨z,hZP hz⟩
    have hc : zP∈center P := hcenter ▸ hz
    have hh := (centerCongr e ⟨zP,hc⟩).property
    have he' : e zP=u := Subtype.ext he
    exact he' ▸ hh

private theorem derived_le_center_mark (P Z : Subgroup G) [IsExtraspecial 2 P]
    (hcenter : center P=Z.subgroupOf P) : ⁅P,P⁆ ≤ Z := by
  apply commutator_le.mpr
  intro a ha b hb
  have hc := commutator_mem_extraspecial_center (⟨a,ha⟩:P) (⟨b,hb⟩:P)
  rw [hcenter] at hc
  exact hc

variable [Finite G] (Z ZS : Subgroup G)

omit [Finite G] in
/-- The literal partner centralizes the point plane. -/
theorem partner_le_plane_centralizer (V₀ : Subgroup G) (y : G)
    (hZS : ZS ≤ centralizerH Z) (hplane : V₀=Z⊔rightConjugate Z y)
    (hy : y∈normalizer (V₀:Set G)) : partnerX Z ZS y ≤ centralizer (V₀:Set G) := by
  have hU := closureU_le_H hZS
  have hF : intersectionF Z ZS y ≤ centralizer (V₀:Set G) := by
    apply le_centralizer_iff.mpr
    rw [hplane]
    exact sup_le (le_centralizer_iff.mp (inf_le_left.trans hU))
      (le_centralizer_iff.mp (by rw [intersectionF, rightConjugate_centralizer]; exact inf_le_right))
  have hV : rightConjugate V₀ y=V₀ :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (V₀:Set G)).inv_mem hy)
  have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hF
  change partnerX Z ZS y ≤ rightConjugate (centralizer (V₀:Set G)) y at hh
  rwa [rightConjugate_centralizer,hV] at hh

/-- The index-two partner has precisely the marked plane as its centralizer
inside the elementary intersection. -/
theorem intersectionE_centralizer_partner
    [IsExtraspecial 2 (closureU Z ZS)] (V₀ : Subgroup G) (y : G)
    (hZS : ZS ≤ centralizerH Z) (hplane : V₀=Z⊔rightConjugate Z y)
    (hy : y∈normalizer (V₀:Set G)) (hVE : V₀ ≤ intersectionE Z ZS y)
    (hVcard : Nat.card V₀=4)
    (hindex : (intersectionF Z ZS y).relIndex (closureU Z ZS)=2) :
    intersectionE Z ZS y ⊓ centralizer (partnerX Z ZS y:Set G)=V₀ := by
  let P := rightConjugate (closureU Z ZS) y
  let X := partnerX Z ZS y
  let E := intersectionE Z ZS y
  have hXP : X ≤ P := map_mono inf_le_left
  have hEP : E ≤ P := inf_le_right.trans hXP
  let := conjugate_extraspecial (closureU Z ZS) y
  have hi : (X.subgroupOf P).index=2 := by
    change X.relIndex P=2
    change ((intersectionF Z ZS y).map (MulAut.conj y⁻¹).toMonoidHom).relIndex
      ((closureU Z ZS).map (MulAut.conj y⁻¹).toMonoidHom) = 2
    rw [relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hindex
  have hh := index_two_centralizer_card_le (X.subgroupOf P) hi
  have heq : centralizer (X.subgroupOf P:Set P) =
      (P⊓centralizer (X:Set G)).subgroupOf P := by
    ext p
    constructor
    · intro hp
      refine ⟨p.property,?_⟩
      intro x hx
      exact congrArg Subtype.val (hp (⟨x,hXP hx⟩:P) hx)
    · intro hp x hx
      exact Subtype.ext (hp.2 x hx)
  rw [heq,Nat.card_congr (subgroupOfEquivOfLe
    (show P⊓centralizer (X:Set G) ≤ P from inf_le_left)).toEquiv] at hh
  have hVC : V₀ ≤ P⊓centralizer (X:Set G) := le_inf (hVE.trans hEP)
    (le_centralizer_iff.mp (partner_le_plane_centralizer Z ZS V₀ y hZS hplane hy))
  have he := eq_of_le_of_card_ge hVC (hVcard ▸ hh)
  apply le_antisymm
  · exact (inf_le_inf hEP le_rfl).trans he.ge
  · exact le_inf hVE (hVC.trans inf_le_right)


/-- The source orders force the exact actor kernel, its elementary image and
its order; the fixed ambient subgroup is the original marked plane. -/
theorem partner_group_action_data
    [IsExtraspecial 2 (closureU Z ZS)]
    (V₀ : Subgroup G) (y : G) (s : ℕ)
    [IsElementaryAbelian 2 (intersectionE Z ZS y)]
    (hcenter : center (closureU Z ZS)=Z.subgroupOf (closureU Z ZS))
    (hZS : ZS ≤ centralizerH Z) (hZcard : Nat.card Z=2)
    (hplane : V₀=Z ⊔ rightConjugate Z y) (hVU : V₀ ≤ closureU Z ZS)
    (hy : y∈normalizer (V₀:Set G)) (hdis : Disjoint Z (rightConjugate Z y))
    (hVcard : Nat.card V₀=4) (hUQ : closureU Z ZS ≤ coreQ Z)
    (hcomm : ⁅closureU Z ZS,coreQ Z⁆ ≤ Z)
    (hUcard : Nat.card (closureU Z ZS)=2^(2*s+5))
    (hEcard : Nat.card (intersectionE Z ZS y)=2^(s+3)) :
    partnerX Z ZS y ⊓ coreQ Z=intersectionE Z ZS y ∧
    IsElementaryAbelian 2 (Recognition.actorImage Z (partnerX Z ZS y)) ∧
    Nat.card (Recognition.actorImage Z (partnerX Z ZS y))=2^(s+1) ∧
    intersectionE Z ZS y ⊓ centralizer (partnerX Z ZS y:Set G)=V₀ ∧
    ⁅partnerX Z ZS y,intersectionE Z ZS y⁆ ≤ rightConjugate Z y := by
  have hZU : Z ≤ closureU Z ZS := (show Z ≤ V₀ by rw [hplane]; exact le_sup_left).trans hVU
  have hZyV : rightConjugate Z y ≤ V₀ := by rw [hplane]; exact le_sup_right
  have hVg : rightConjugate V₀ y=V₀ :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (V₀:Set G)).inv_mem hy)
  have hVU' : V₀ ≤ rightConjugate (closureU Z ZS) y := by
    rw [←hVg]
    exact map_mono hVU
  have hE := intersectionE_eq Z ZS V₀ y hZS hplane hy
  have hVE : V₀ ≤ intersectionE Z ZS y := by rw [hE]; exact le_inf hVU hVU'
  have hEP : intersectionE Z ZS y ≤ rightConjugate (closureU Z ZS) y := by
    rw [hE]; exact inf_le_right
  have hXP : partnerX Z ZS y ≤ rightConjugate (closureU Z ZS) y := map_mono inf_le_left
  let := conjugate_extraspecial (closureU Z ZS) y
  have hcenter' := conjugate_center (closureU Z ZS) Z y hZU hcenter
  have hderived := derived_le_center_mark _ _ hcenter'
  have hCE : center (rightConjugate (closureU Z ZS) y) ≤
      (intersectionE Z ZS y).subgroupOf (rightConjugate (closureU Z ZS) y) := by
    rw [hcenter']
    exact comap_mono (hZyV.trans hVE)
  have hsquare : (Nat.card (intersectionE Z ZS y))^2 =
      2 * Nat.card (rightConjugate (closureU Z ZS) y) := by
    have hc : Nat.card (rightConjugate (closureU Z ZS) y)=Nat.card (closureU Z ZS) :=
      card_map_of_injective (MulAut.conj y⁻¹).injective
    rw [hc,hUcard,hEcard,←pow_mul,←pow_succ']
    congr 1
    omega
  have hself := ambient_selfCentralizing_of_card_sq _ _ hEP hCE hsquare
  have hkernel := partner_inf_core_of_selfCentralizing Z ZS y hUQ hE hcomm
    hderived hdis hself.le
  have hindex := intersectionF_index Z ZS y hcenter hZcard (hZyV.trans hVU) hdis
  have hXH : partnerX Z ZS y ≤ centralizerH Z :=
    (partner_le_plane_centralizer Z ZS V₀ y hZS hplane hy).trans
      (centralizer_le (show Z ≤ V₀ by rw [hplane]; exact le_sup_left))
  refine ⟨hkernel,partner_actor_elementary Z ZS y hcenter' (hZyV.trans (hVU.trans hUQ)),
    partner_actor_card Z ZS y s hXH hkernel hindex hUcard hEcard,
    intersectionE_centralizer_partner Z ZS V₀ y hZS hplane hy hVE hVcard hindex,
    (commutator_mono hXP hEP).trans hderived⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
