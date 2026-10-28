module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionLocalTableLarge
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.SourceUpper
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ExtendedAffinePlaneRestriction
public import Theory.Representation.BinaryAlternatingFiveExtension.OuterClasses.Transport

/-!
# Controlled outer involution classes in the doubled source completion

The marked doubled-plane comparison preserves both its translation core and
its ordinary index-two subgroup. Pulling back the actual Sylow therefore
retains permutation parity. The exact source commutator, graph-centralizer
order32 and central root instantiate the affine outer two-class theorem.
Mapping its conjugators through this same plane endpoint places every outer
Sylow involution in the graph or graph-root class with a witness in the
original completion image.

This discharges the outer-coset premise in the controlled full-Sylow cover
used for exceptional generation and the two-class conclusion of
Aschbacher--Smith F.4.37 and F.5.3, printed pp.293 and 300.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation.AlternatingFiveExtension
open SylowCommutator
local notation "hn" => Nat.le_refl 1
local notation "PE" => Extension.plane 1 hn
local notation "U" => upperProjective 1 hn
local notation "T" => Source.sylowImage
open scoped commutatorElement
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

private theorem plane_ordinary_sylow_image (a : PE) (ha : a∈(extendedPlaneSylow : Subgroup PE))
    (ho : a∈Extension.binaryPlaneInclusion.range) :
    i (c.right a) ∈ sourceOrdinaryUpper c i := by
  have har : a.val.right=1 := by
    obtain ⟨p,rfl⟩ := ho
    rfl
  let u : U := ⟨a.val.left,(extendedUpper_mem a.val).mp ha⟩
  have hb : (Extension.amalgam 1 hn).right (ordinaryUpperInclusion u)=a := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact har.symm
  refine ⟨u,?_⟩
  change i (c.middle (ordinaryUpperInclusion u))=i (c.right a)
  rw [←hb,DFunLike.congr_fun c.compatible]
  rfl

private theorem source_affine_realization (hi : Function.Injective i) :
    ∃ (j : Model →* G) (_ : Function.Injective j) (S : Sylow 2 Model),
      (S : Subgroup Model).map j=T c i ∧ translations.map j=Q c i true ∧
      (∀ a, j a∈i.range) ∧
      ∀ x : Model, x∈(S : Subgroup Model) → x.right∈alternatingGroup (Fin 5) →
        j x∈sourceOrdinaryUpper c i := by
  obtain ⟨E,hz,hQ,hB⟩ := UnitaryTwo.ExtendedAffinePlane.exists_marked_plane_equiv
  have heven := UnitaryTwo.ExtendedAffinePlane.map_symmetricEmbedding_range E hQ
  let j : Model →* G := (i.comp c.right).comp E.toMonoidHom
  have hj : Function.Injective j := (endpointMap_injective c i hi true).comp E.injective
  let S : Sylow 2 Model := extendedPlaneSylow.mapSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  have hT : (S : Subgroup Model).map j=T c i := by
    change (((extendedPlaneSylow : Subgroup PE).map E.symm.toMonoidHom).map j)=_
    rw [map_map]
    have hcomp : j.comp E.symm.toMonoidHom=i.comp c.right := by
      apply MonoidHom.ext
      intro x
      exact congrArg (i.comp c.right) (E.apply_symm_apply x)
    rw [hcomp]
    exact source_sylowImage_eq_planeSylow c i
  have hcore : translations.map j=Q c i true := by
    calc
      translations.map j=(translations.map E.toMonoidHom).map (i.comp c.right) := (map_map _ _ _).symm
      _=UnitaryTwo.ExtendedAffinePlane.planeCore.map (i.comp c.right) :=
        congrArg (fun K : Subgroup PE => K.map (i.comp c.right)) hQ
      _=(pCore 2 (planeParabolic 1 hn)).map ((i.comp c.right).comp Source.planeInclusion) := by
        rw [UnitaryTwo.ExtendedAffinePlane.planeCore,map_map]
        rfl
      _=Q c i true := (Q_eq_map_pCore c i true).symm
  refine ⟨j,hj,S,hT,hcore,fun a => ⟨c.right (E a),rfl⟩,?_⟩
  intro x hx hxodd
  have hxOrd : E x∈Extension.binaryPlaneInclusion.range := by
    rw [←heven]
    apply mem_map_of_mem
    rw [OverlapFactorizationExtension.symmetricEmbedding_range]
    exact hxodd
  obtain ⟨p,hp,hpx⟩ := hx
  have hEp : E x=p := by rw [←hpx]; exact E.apply_symm_apply p
  change i (c.right (E x))∈sourceOrdinaryUpper c i
  rw [hEp] at hxOrd ⊢
  exact plane_ordinary_sylow_image c i p hp hxOrd


private def graphInT : T c i := ⟨Source.graphElement c i,source_graph_mem_sylowImage c i⟩
private def sourceGraphCentralizerEquiv :
    centralizer ({graphInT c i} : Set (T c i)) ≃ Tf c i where
  toFun x := ⟨⟨x.val.val,mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite G]
/-- Every outer Sylow involution is graph or graph-root, through the original plane endpoint. -/
theorem source_outer_involution_classes_in_range (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (x : G) (hx : x∈T c i)
    (hxnot : x∉sourceOrdinaryUpper c i) (ho : orderOf x=2) :
    (∃ k∈i.range, k*Source.graphElement c i*k⁻¹=x) ∨
    (∃ k∈i.range, k*(Source.graphElement c i*rootElement c i z)*k⁻¹=x) := by
  obtain ⟨j,hj,S,hT,hQ,hrange,heven⟩ := source_affine_realization c i h.embedding_injective
  let d : S ≃* T c i := ((S : Subgroup Model).equivMapOfInjective j hj).trans
    (MulEquiv.subgroupCongr hT)
  have hd (a : S) : (d a).val=j a.val := rfl
  have hback (a : T c i) : j (d.symm a).val=a.val :=
    (hd (d.symm a)).symm.trans (congrArg Subtype.val (d.apply_symm_apply a))
  let fT := graphInT c i
  let zT : T c i := ⟨rootElement c i z,source_root_mem_sylowImage c i z h⟩
  let tT : T c i := ⟨sourceMarkedShort c i,source_short_mem_sylowImage c i⟩
  let xT : T c i := ⟨x,hx⟩
  let f := d.symm fT
  let r := d.symm zT
  let t := d.symm tT
  let a := d.symm xT
  have hfv : j f.val=Source.graphElement c i := hback fT
  have hrv : j r.val=rootElement c i z := hback zT
  have htv : j t.val=sourceMarkedShort c i := hback tT
  have hav : j a.val=x := hback xT
  have hfo : orderOf f=2 := (d.symm.orderOf_eq fT).trans
    ((orderOf_injective (T c i).subtype (T c i).subtype_injective fT).symm.trans
      (source_graph_order c i h.embedding_injective))
  have hto : orderOf t=2 := (d.symm.orderOf_eq tT).trans
    ((orderOf_injective (T c i).subtype (T c i).subtype_injective tT).symm.trans
      (source_short_order c i h.embedding_injective))
  have hVS : translations≤(S : Subgroup Model) := by
    intro v hv
    have hv' : j v∈(S : Subgroup Model).map j := by
      rw [hT]
      apply source_Q_plane_le_sylowImage c i
      rw [←hQ]
      exact mem_map_of_mem j hv
    exact (mem_map_iff_mem hj).mp hv'
  have htV : t.val∈translations := by
    apply (mem_map_iff_mem hj).mp
    rw [htv,hQ]
    exact source_short_mem_Q c i
  have htrans : (translations.subgroupOf S).map (j.comp (S : Subgroup Model).subtype)=Q c i true := by
    rw [←map_map,subgroupOf_map_subtype,inf_eq_left.mpr hVS,hQ]
  have hc : ⁅translations.subgroupOf S,zpowers f⁆=zpowers t := by
    apply map_injective (f := j.comp (S : Subgroup Model).subtype)
      (hj.comp (S : Subgroup Model).subtype_injective)
    rw [map_commutator,htrans,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    change ⁅Q c i true,zpowers (j f.val)⁆=zpowers (j t.val)
    rw [hfv,htv]
    exact source_short_commutator c i h.embedding_injective
  have hfc : Nat.card (centralizer ({f} : Set S))=32 := by
    rw [←Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv d.symm fT).toEquiv,
      Nat.card_congr (sourceGraphCentralizerEquiv c i),source_Tf_card c i h.embedding_injective]
  have hrcenter : r∈center S := by
    apply mem_center_iff.mpr
    intro b
    apply d.injective
    apply Subtype.ext
    have hzb := mem_centralizer_singleton_iff.mp
      ((source_root_centralizer c i z h).symm ▸ (sylowImage_le_M c i false (d b).property))
    simpa only [map_mul,Subgroup.coe_mul,r,d.apply_symm_apply,zT] using hzb
  have hr1 : r≠1 := by
    intro hh
    have hh' : rootElement c i z=1 := hrv.symm.trans (by rw [hh]; exact j.map_one)
    have hro := source_root_order c i z h
    rw [hh',orderOf_one] at hro
    omega
  have ha2 : a*a=1 := by
    apply Subtype.ext
    apply hj
    change j (a.val*a.val)=j 1
    rw [map_mul,hav,map_one]
    simpa [ho,pow_two] using pow_orderOf_eq_one x
  have hao : a.val.right∉alternatingGroup (Fin 5) := by
    intro hh
    exact hxnot (hav ▸ heven a.val a.property hh)
  rcases OuterClasses.outer_classes_in_sylow S f r t hfo hto htV hc hfc hrcenter hr1 a ha2 hao with hh | hh
  · obtain ⟨k,hk⟩ := isConj_iff.mp hh
    exact Or.inl ⟨j k,hrange k,by simpa only [map_mul,map_inv,hfv,hav] using congrArg j hk⟩
  · obtain ⟨k,hk⟩ := isConj_iff.mp hh
    exact Or.inr ⟨j k,hrange k,by simpa only [map_mul,map_inv,hfv,hrv,hav] using congrArg j hk⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
