module

public import Stellmacher.SectionNine.DistanceOneExtractedQuaternionProduct
public import Theory.GroupTheory.QuaternionInvolutionFixedEight

/-!
# The final extracted-core intersection in source (8)

The faithful initial-center conclusion and actual distance-one extraction
imply that its coatom C=Z_a intersect G_next is exactly Z_a intersect Q_d.
This identity is proved before initial core equality and before the extracted
product V is known to lie in the terminal core. It supplies the genuine
input used by the maximal-V₁ construction and later core-structure assembly.

The extracted product V=C joined with D is a quaternion central product of
order32 and is a normal two-subgroup of the extracted group E. The actual
quotient E/(E intersect Q_d) is an odd-dihedral product with central two-core.
Its image of V is therefore central, giving [V,E]≤Q_d. Choose an involution
s in Z_a outside C. The source(2) centralizer calculation identifies C_V(s)
with the elementary subgroup C of order8. The intrinsic quaternion theorem
identifies [V,s] with this same fixed subgroup, so C≤Q_d. Conversely the
normal two-subgroup E intersect Q_d lies in O2(E), giving Z_a intersect Q_d
inside the extracted coatom. No initial core equality is used in either
inclusion.

Source: Stellmacher(9.1), Journal of Algebra190 (1997), p.47, final identity
of (8). All quotient, conjugator, action and coatom data are those of the
actual extraction. The faithful conclusion supplies the order16/8/32 and
quaternion recognition inputs through previously proved geometry.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
open scoped commutatorElement

private theorem extracted_commutator_le_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length=1) (data : DistanceOneActionData ctx)
    (V : Subgroup G) (hVE : V≤data.E) (hVp : IsPGroup 2 V)
    (hEV : data.E≤Subgroup.normalizer (V:Set G)) :
    ⁅V,data.E⁆≤q ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨model⟩ := data.quotient
  let _ := model.barL_group
  let _ := model.barL_finite
  have hforward : ctx.criticalPath.a'∈neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [neighborhood,ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  let _ := z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hforward
  let _ : IsMulCommutative data.coatom :=
    IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
      setLike_mul_comm (s:=z ctx.Γ ctx.criticalPath.a)
        (data.coatom_eq ▸ ha).1 (data.coatom_eq ▸ hb).1
  let _ : IsMulCommutative model.barA0 := by
    rw [model.barA0_image]
    infer_instance
  have hc := dihedralProduct_twoCore_le_center model.barL model.barA0
    (model.p^model.n) model.p_odd.pow model.model
  let W := V.subgroupOf data.E
  let _ : W.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVE).mpr hEV
  have hWp : IsPGroup 2 W := hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVE).symm
  have hWcore : W≤pCore 2 data.E := le_sSup ⟨inferInstance,hWp⟩
  have hm : (pCore 2 data.E).map model.quotientMap≤pCore 2 model.barL :=
    le_sSup ⟨pCore_normal.map model.quotientMap model.quotient_surjective,
      pCore_isPGroup.map model.quotientMap⟩
  apply Subgroup.commutator_le.mpr
  intro v hv e he
  let vn : data.E := ⟨v,hVE hv⟩
  let en : data.E := ⟨e,he⟩
  have hh := Subgroup.mem_center_iff.mp
    (hc (hm (Subgroup.mem_map_of_mem model.quotientMap (hWcore (show vn∈W from hv))))) (model.quotientMap en)
  have hk : ⁅vn,en⁆∈model.quotientMap.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement,commutatorElement_def,← hh]
    simp [mul_assoc]
  exact (model.quotient_kernel ▸ hk).2

private theorem initial_core_intersection_le_coatom
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (data : DistanceOneActionData ctx) :
    z ctx.Γ ctx.criticalPath.a⊓q ctx.Γ ctx.criticalPath.a'≤data.coatom := by
  let Q := q ctx.Γ ctx.criticalPath.a'
  have hE : data.E≤Subgroup.normalizer (Q:Set G) :=
    data.E_le.trans (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a')
  have hQp : IsPGroup 2 Q := by
    change IsPGroup 2 (q ctx.Γ ctx.criticalPath.a')
    rw [q,ctx.Γ.twoCoreAt_def]
    exact pCore_isPGroup.map _
  let K := Q.subgroupOf data.E
  let _ : K.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hE
  have hKp : IsPGroup 2 K :=
    (hQp.to_le (show K.map data.E.subtype≤Q from by rintro y ⟨x,hx,rfl⟩; exact hx)).of_equiv
      (K.equivMapOfInjective data.E.subtype data.E.subtype_injective).symm
  have hKcore : K≤pCore 2 data.E := le_sSup ⟨inferInstance,hKp⟩
  have hZaE : z ctx.Γ ctx.criticalPath.a≤data.E := by rw [data.generated]; exact le_sup_left
  intro a ha
  rw [data.coatom_eq]
  refine ⟨ha.1,?_⟩
  exact Subgroup.mem_map_of_mem data.E.subtype (hKcore (show (⟨a,hZaE ha.1⟩:data.E)∈K from ha.2))

public theorem distance_one_final_core_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length=1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (data : DistanceOneActionData ctx) :
    z ctx.Γ ctx.criticalPath.a⊓stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a)=
      z ctx.Γ ctx.criticalPath.a⊓q ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let Za := z Γ cp.a
  let C := Za⊓stabilizer Γ next
  let D := z Γ next⊓stabilizer Γ cp.a
  let V := C⊔D
  have hgeom := distance_one_local_geometry ctx hb data
  have hfour : 4≤(V⊓q Γ cp.a).relIndex V := by
    have hh := Subgroup.relIndex_mul_relIndex (⊥:Subgroup G) (V⊓q Γ cp.a) V bot_le inf_le_left
    simp only [Subgroup.relIndex_bot_left] at hh
    have hp : 0<Nat.card (V⊓q Γ cp.a:Subgroup G) := Nat.card_pos
    have hbound : 4*Nat.card (V⊓q Γ cp.a:Subgroup G)≤Nat.card V := hgeom.2.2
    nlinarith
  obtain ⟨_,_,hCcard,_,hVcard⟩ := distance_one_extracted_product_center_card
    ctx hb hfaith data.toDistanceOneExtractionData data.coatom_stabilizer hfour hgeom.1
  change Nat.card C=8 at hCcard
  change Nat.card V=32 at hVcard
  have hmodel := distance_one_extracted_quaternion_product ctx hb hfaith data
  change IsCentralProductQ8Q8 V at hmodel
  have hVE : V≤data.E := by
    rw [data.generated]
    exact sup_le_sup inf_le_left inf_le_left
  have hEV : data.E≤Subgroup.normalizer (V:Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono le_sup_left le_rfl).trans data.product_action)
  have hVp : IsPGroup 2 V := isPGroup_iff_card_dvd_pow.mpr ⟨5,by rw [hVcard]; decide⟩
  have hcomm := extracted_commutator_le_core ctx hb data V hVE hVp hEV
  have hZaE : Za≤data.E := by rw [data.generated]; exact le_sup_left
  have hZaCard : Nat.card Za=16 := hfaith.1
  have hnot : ¬Za≤C := by
    intro hh
    have hh' := Subgroup.card_le_of_le hh
    rw [hZaCard,hCcard] at hh'
    omega
  obtain ⟨s,hs,hsC⟩ := SetLike.not_le_iff_exists.mp hnot
  have hcoatom : s∉data.coatom := by
    rw [data.coatom_stabilizer]
    exact hsC
  have hfix := distance_one_extracted_centralizer ctx hb data.toDistanceOneExtractionData s hs hcoatom
  have hneighbor : cp.a'∈neighborhood Γ cp.a := by
    rw [neighborhood,Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hneighbor
  have hs2 : s^2=1 := elemPow_eq_one_of_isElementaryAbelian s hs
  have hCexp : ∀c∈C,c^2=1 := by
    intro c hc
    exact elemPow_eq_one_of_isElementaryAbelian c (show c∈Za from hc.1)
  have hCcomm : ⁅V,Subgroup.zpowers s⁆=C := by
    obtain ⟨L,R,hL,hR,hjoin,hinter,hcommute,_⟩ := hmodel
    have hCelem : IsElementaryAbelian 2 C := {
      toIsMulCommutative := IsMulCommutative.of_setLike_mul_comm
        (fun x hx y hy => setLike_mul_comm (s:=Za) hx.1 hy.1)
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun c => Subtype.ext (hCexp c c.property)) }
    have hf : (L⊔R)⊓Subgroup.centralizer ({s}:Set G)=C := by rw [← hjoin]; exact hfix
    have hh := Subgroup.commutator_zpowers_eq_fixed_eight L R hL hR hinter hcommute
      (hjoin ▸ hVcard) s hs2 (hjoin ▸ hEV (hZaE hs))
      (by rw [hf]; exact hCcard) (by rw [hf]; exact hCelem)
    rwa [hf,← hjoin] at hh
  have hCQ : C≤q Γ cp.a' := by
    rw [← hCcomm]
    exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr (hZaE hs))).trans hcomm
  apply le_antisymm (le_inf inf_le_left hCQ)
  rw [← data.coatom_stabilizer]
  exact initial_core_intersection_le_coatom ctx data
end Stellmacher.SectionNine
