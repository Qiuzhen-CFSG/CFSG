module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.ExtraspecialAction.Group
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.LocalRestrictions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers.Geometry
public import Theory.GroupAction.BinaryTransvectionImage
public import Mathlib.FieldTheory.Finiteness

/-!
# Full transvections on the actual partner quotient

The commutators [X,E] lie in Zʸ. Since Z and Zʸ are disjoint, a vector
of E/Z fixed by X has a representative centralizing X. Thus the exact
ambient centralizer C_E(X)=V₀ gives the fixed line V₀/Z. The same
commutator bound puts every displacement in that line. Binary duality
then realizes every center transvection by a single actor in the literal
image of X in H/O₂(H). All spaces and actions are the existing recognition
carriers and quotient maps.

Source: Aschbacher–Smith, 15.3.56(4), printed p.1148.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.ExtraspecialAction
open Recognition LocalRestrictions
variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

omit [Finite G] in
private theorem imageSpace_mk_iff (A : Subgroup G) (hZA : Z ≤ A)
    (u : closureU Z ZS) :
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u) ∈
      vectorSubspace Z ZS A ↔ (u:G) ∈ A := by
  change u ∈ (vectorImage Z ZS A).comap (QuotientGroup.mk' _) ↔ _
  rw [vectorImage_preimage Z ZS A hZA]
  rfl

omit [Finite G] in
private theorem imageSpace_mono {A B : Subgroup G} (h : A ≤ B) :
    vectorSubspace Z ZS A ≤ vectorSubspace Z ZS B := by
  intro w hw
  change w.toMul ∈ vectorImage Z ZS B
  exact map_mono (comap_mono h) hw

omit [Finite G] in
private theorem plane_generator (V₀ E : Subgroup G)
    (hZU : Z ≤ V₀) (hVU : V₀ ≤ closureU Z ZS) (hVE : V₀ ≤ E)
    (hZcard : Nat.card Z=2) (hVcard : Nat.card V₀=4) :
    ∃ v : vectorSubspace Z ZS E, (v:Space Z ZS) ≠ 0 ∧
      Submodule.span (ZMod 2) {(v:Space Z ZS)}=vectorSubspace Z ZS V₀ := by
  have hh := ResidualOrbits.Normalizers.vectorImage_card_mul_center Z ZS V₀ hVU hZU
  rw [hZcard,hVcard] at hh
  have hc : Nat.card (vectorSubspace Z ZS V₀)=2 := by
    have he : Nat.card (vectorSubspace Z ZS V₀)=Nat.card (vectorImage Z ZS V₀) :=
      Nat.card_congr {
        toFun := fun x => ⟨x.val.toMul,x.property⟩
        invFun := fun x => ⟨Additive.ofMul x.val,x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [he]
    omega
  obtain ⟨v,hv,hall⟩ := (Nat.card_eq_two_iff' (0:vectorSubspace Z ZS V₀)).mp hc
  let w : vectorSubspace Z ZS E := ⟨v,imageSpace_mono Z ZS hVE v.property⟩
  refine ⟨w,fun h => hv (Subtype.ext h),?_⟩
  apply le_antisymm
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr v.property)
  · intro x hx
    by_cases h : (⟨x,hx⟩:vectorSubspace Z ZS V₀)=0
    · have he : x=0 := congrArg Subtype.val h
      rw [he]
      exact Submodule.zero_mem _
    · have he : x=(w:Space Z ZS) := congrArg Subtype.val (hall ⟨x,hx⟩ h)
      rw [he]
      exact Submodule.mem_span_singleton_self _

omit [Finite G] in
private theorem displacement_mem_plane
    (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z))
    (V₀ : Subgroup G) (y : G)
    (hZyV : rightConjugate Z y ≤ V₀)
    (hderived : ⁅partnerX Z ZS y,intersectionE Z ZS y⁆ ≤ rightConjugate Z y)
    (x : actorImage Z (partnerX Z ZS y))
    (e : vectorSubspace Z ZS (intersectionE Z ZS y)) :
    actorRepresentation Z ZS hk x e-e ∈ vectorSubspace Z ZS V₀ := by
  obtain ⟨h,hh,hx⟩ := x.property
  obtain ⟨u,hu,he⟩ := (show e.val.toMul ∈ vectorImage Z ZS (intersectionE Z ZS y) from e.property)
  let u' : closureU Z ZS := ⟨(h:G)*(u:G)*(h:G)⁻¹,
    (mem_normalizer_iff.mp (H_normalizes_closureU Z ZS h.property) u).mp u.property⟩
  have hd : ((u'/u:closureU Z ZS):G)=⁅(h:G),(u:G)⁆ := by
    change ((h:G)*(u:G)*(h:G)⁻¹) / (u:G)=_
    simp only [commutatorElement_def,div_eq_mul_inv]
  have hm : u'/u ∈ V₀.subgroupOf (closureU Z ZS) := by
    change ((u'/u:closureU Z ZS):G)∈V₀
    rw [hd]
    exact hZyV (hderived (commutator_mem_commutator hh hu))
  have him : QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) (u'/u) ∈ vectorImage Z ZS V₀ :=
    ⟨_,hm,rfl⟩
  have he' : (e:Space Z ZS)=Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u) :=
    (congrArg Additive.ofMul he).symm
  rw [←hx,he',actorRepresentation_mk,toMul_ofMul,quotientAction_mk]
  change QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u' /
    QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u ∈ vectorImage Z ZS V₀
  simpa only [map_div] using him

omit [Finite G] in
private theorem fixed_iff_plane
    (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z))
    (V₀ : Subgroup G) (y : G) (hXH : partnerX Z ZS y ≤ centralizerH Z)
    (hZV : Z ≤ V₀) (hdis : Disjoint Z (rightConjugate Z y))
    (hderived : ⁅partnerX Z ZS y,intersectionE Z ZS y⁆ ≤ rightConjugate Z y)
    (hcentral : intersectionE Z ZS y ⊓ centralizer (partnerX Z ZS y:Set G)=V₀)
    (e : vectorSubspace Z ZS (intersectionE Z ZS y)) :
    (∀ x : actorImage Z (partnerX Z ZS y),actorRepresentation Z ZS hk x e=e) ↔
      (e:Space Z ZS)∈vectorSubspace Z ZS V₀ := by
  obtain ⟨u,hu,he⟩ := (show e.val.toMul ∈ vectorImage Z ZS (intersectionE Z ZS y) from e.property)
  have he' : (e:Space Z ZS)=Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u) :=
    (congrArg Additive.ofMul he).symm
  rw [he',imageSpace_mk_iff Z ZS V₀ hZV]
  constructor
  · intro hfix
    rw [←hcentral]
    refine ⟨hu,?_⟩
    intro x hx
    let h : centralizerH Z := ⟨x,hXH hx⟩
    let a : actorImage Z (partnerX Z ZS y) := ⟨QuotientGroup.mk' _ h,⟨h,hx,rfl⟩⟩
    have hh := hfix a
    change actorRepresentation Z ZS hk (QuotientGroup.mk' _ h) _ = _ at hh
    rw [actorRepresentation_mk,toMul_ofMul,quotientAction_mk] at hh
    have hz := QuotientGroup.eq_iff_div_mem.mp (Additive.ofMul.injective hh)
    have hz' : ⁅x,(u:G)⁆∈Z := by
      change (x*(u:G)*x⁻¹) / (u:G) ∈ Z at hz
      simpa only [commutatorElement_def,div_eq_mul_inv] using hz
    have hc := hderived (commutator_mem_commutator hx hu)
    have hone := disjoint_def.mp hdis hz' hc
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  · intro hplane x
    have hc := (hcentral.ge hplane).2
    obtain ⟨h,hh,hx⟩ := x.property
    rw [←hx,actorRepresentation_mk,toMul_ofMul,quotientAction_mk]
    congr 2
    apply Subtype.ext
    change (h:G)*(u:G)*(h:G)⁻¹=(u:G)
    rw [hc h hh,mul_inv_cancel_right]

/-- Full center transvections on the original E/Z. Both inclusions of the
image are explicit: each functional is realized by one entire actor. -/
theorem full_center_transvections
    (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z))
    (V₀ : Subgroup G) (y : G) (hXH : partnerX Z ZS y ≤ centralizerH Z)
    (hplane : V₀=Z ⊔ rightConjugate Z y) (hVU : V₀ ≤ closureU Z ZS)
    (hdis : Disjoint Z (rightConjugate Z y))
    (hZcard : Nat.card Z=2) (hVcard : Nat.card V₀=4)
    (hderived : ⁅partnerX Z ZS y,intersectionE Z ZS y⁆ ≤ rightConjugate Z y)
    (hcentral : intersectionE Z ZS y ⊓ centralizer (partnerX Z ZS y:Set G)=V₀) :
    ∃ v : vectorSubspace Z ZS (intersectionE Z ZS y), (v:Space Z ZS) ≠ 0 ∧
      Submodule.span (ZMod 2) {(v:Space Z ZS)}=vectorSubspace Z ZS V₀ ∧
      (∀ x : actorImage Z (partnerX Z ZS y),
        ∃ φ : Module.Dual (ZMod 2) (vectorSubspace Z ZS (intersectionE Z ZS y)), φ v=0 ∧
          ∀ e : vectorSubspace Z ZS (intersectionE Z ZS y),
            actorRepresentation Z ZS hk x e=(e:Space Z ZS)+φ e • (v:Space Z ZS)) ∧
      (∀ φ : Module.Dual (ZMod 2) (vectorSubspace Z ZS (intersectionE Z ZS y)), φ v=0 →
        ∃ x : actorImage Z (partnerX Z ZS y),
          ∀ e : vectorSubspace Z ZS (intersectionE Z ZS y),
            actorRepresentation Z ZS hk x e=(e:Space Z ZS)+φ e • (v:Space Z ZS)) := by
  have hZV : Z ≤ V₀ := by rw [hplane]; exact le_sup_left
  have hZyV : rightConjugate Z y ≤ V₀ := by rw [hplane]; exact le_sup_right
  have hVE : V₀ ≤ intersectionE Z ZS y := hcentral.ge.trans inf_le_left
  obtain ⟨v,hv,hline⟩ := plane_generator Z ZS V₀ _ hZV hVU hVE hZcard hVcard
  refine ⟨v,hv,hline,?_⟩
  apply BinaryTransvection.full_action_of_fixed_space
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space Z ZS)).toMonoidHom.comp
      (actorRepresentation Z ZS hk).asGroupHom).comp (actorImage Z (partnerX Z ZS y)).subtype)
    (vectorSubspace Z ZS (intersectionE Z ZS y)) v hv
  · intro x e
    rw [hline]
    exact displacement_mem_plane Z ZS hk V₀ y hZyV hderived x e
  · intro e
    change (∀ x : actorImage Z (partnerX Z ZS y),actorRepresentation Z ZS hk x e=e) ↔ _
    rw [fixed_iff_plane Z ZS hk V₀ y hXH hZV hdis hderived hcentral,←hline]
    constructor
    · intro he
      obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp he
      exact Submodule.mem_span_singleton.mpr ⟨a,Subtype.ext ha⟩
    · intro he
      obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp he
      exact Submodule.mem_span_singleton.mpr ⟨a,congrArg Subtype.val ha⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.ExtraspecialAction
