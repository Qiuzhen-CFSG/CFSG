module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsPlane
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsPointFixed
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionPlaneCommutator
/-!
# The literal plane endpoint graph centralizers

The graph centralizer in the doubled plane endpoint splits as the ordinary
fixed group times its marked graph involution. The binary projective map is
injective, so both decompositions transport to the actual source subgroups.
Source: Aschbacher--Smith F.5.3, p.300.
-/
noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "P" => planeParabolicSU F (form F σ hσ)
local notation "PX" => UnitaryFourOuter.plane F σ hσ
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)
private def binaryPlaneMatrixEquiv : PX ≃* modelEndpoint true :=
  (UnitaryFourOuter.plane F σ hσ).equivMapOfInjective
    (Extension.extensionProjection 1 hn) (Extension.extensionProjection_injective 1 hn)
private def ordinaryPlaneFixedEquiv : modelFixed true ≃* graphFixedPlane := by
  let e : planeParabolicSU F (form F σ hσ) ≃* ordinaryEndpoint true :=
    (planeParabolicSU F (form F σ hσ)).equivMapOfInjective
      (projection 1 hn) (projection_injective 1 hn)
  have hm (a : planeParabolicSU F (form F σ hσ)) :
      e a ∈ modelFixed true ↔ a ∈ graphFixedPlane := by
    change ordinaryInclusion true (e a) ∈ centralizer ({modelGraph true} : Set (modelEndpoint true)) ↔ _
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      have hh := congrArg (fun x : modelEndpoint true => x.val.left) h
      change projection 1 hn a.val * Extension.projectiveAction 1 hn 1 1 =
        1 * Extension.projectiveAction 1 hn UnitaryFourOuter.generator (projection 1 hn a.val) at hh
      have he : Extension.projectiveAut 1 hn (projection 1 hn a.val) = projection 1 hn a.val := by
        simpa only [map_one, MulAut.one_apply, one_mul, mul_one,
          Extension.projectiveAction_generator] using hh.symm
      change UnitaryFourOuter.matrixHom F σ hσ a.val = a.val
      apply (projection_injective 1 hn)
      exact (Extension.projectiveAut_project 1 hn a.val).symm.trans he
    · intro h
      have he : Extension.projectiveAut 1 hn (projection 1 hn a.val) = projection 1 hn a.val :=
        (Extension.projectiveAut_project 1 hn a.val).trans (congrArg (projection 1 hn) h)
      apply Subtype.ext
      apply SemidirectProduct.ext
      · change projection 1 hn a.val * Extension.projectiveAction 1 hn 1 1 =
          1 * Extension.projectiveAction 1 hn UnitaryFourOuter.generator (projection 1 hn a.val)
        simpa only [map_one, MulAut.one_apply, one_mul, mul_one,
          Extension.projectiveAction_generator] using he.symm
      · exact one_mul _ |>.trans (mul_one _).symm
  refine {
    toFun := fun a => ⟨e.symm a.val, (hm _).mp (by rw [e.apply_symm_apply]; exact a.property)⟩
    invFun := fun a => ⟨e a.val, (hm a.val).mpr a.property⟩
    left_inv := ?_
    right_inv := ?_
    map_mul' := ?_ }
  · intro a; apply Subtype.ext; exact e.apply_symm_apply a.val
  · intro a; apply Subtype.ext; exact e.symm_apply_apply a.val
  · intro a b; apply Subtype.ext; exact map_mul e.symm a.val b.val

private def matrixPlaneGraphElement : PX :=
  ⟨UnitaryFourOuter.sigma F σ hσ,(P).one_mem⟩

private def matrixPlaneGraph : Subgroup PX := centralizer ({matrixPlaneGraphElement} : Set PX)

private theorem plane_commutes_graph_iff (a : PX) :
    a ∈ matrixPlaneGraph ↔
      UnitaryFourOuter.matrixHom F σ hσ a.val.left = a.val.left := by
  rw [matrixPlaneGraph,mem_centralizer_singleton_iff]
  constructor
  · intro h
    have he := congrArg (fun x : PX => x.val.left) h
    simpa [matrixPlaneGraphElement,UnitaryFourOuter.sigma,
      UnitaryFourOuter.action_generator,UnitaryFourOuter.matrixAut] using he.symm
  · intro h
    apply Subtype.ext
    apply SemidirectProduct.ext
    · simpa [matrixPlaneGraphElement,UnitaryFourOuter.sigma,
        UnitaryFourOuter.action_generator,UnitaryFourOuter.matrixAut] using h.symm
    · change a.val.right * UnitaryFourOuter.generator = UnitaryFourOuter.generator * a.val.right
      exact mul_comm _ _

private theorem action_fixed (a : UnitaryFourOuter.C2) (b : graphFixedPlane) :
    UnitaryFourOuter.action F σ hσ a b.val.val = b.val.val := by
  rcases UnitaryFourOuter.c2_cases a with ha | ha
  · simp [ha]
  · rw [ha,UnitaryFourOuter.action_generator]
    exact b.property

/-- The graph centralizer in the literal doubled plane endpoint is the direct
product of the ordinary fixed group and the same graph C2. -/
private def matrixPlaneGraphEquiv : matrixPlaneGraph ≃* graphFixedPlane × UnitaryFourOuter.C2 where
  toFun a := (⟨⟨a.val.val.left,a.val.property⟩,by exact (plane_commutes_graph_iff _).mp a.property⟩,
    a.val.val.right)
  invFun a := ⟨⟨⟨a.1.val.val,a.2⟩,a.1.val.property⟩,
    by exact (plane_commutes_graph_iff _).mpr a.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b := by
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      change a.val.val.left * UnitaryFourOuter.action F σ hσ a.val.val.right b.val.val.left =
        a.val.val.left * b.val.val.left
      rw [action_fixed a.val.val.right
        ⟨⟨b.val.val.left,b.val.property⟩,(plane_commutes_graph_iff _).mp b.property⟩]
    · rfl

private theorem plane_graph_projection :
    binaryPlaneMatrixEquiv matrixPlaneGraphElement = modelGraph true := by
  apply Subtype.ext
  exact Extension.extensionProjection_sigma 1 hn

/-- The same model centralizer is transported through the injective projective
map; the specified graph involution is preserved. -/
private def modelPlaneGraphEquiv :
    centralizer ({modelGraph true} : Set (modelEndpoint true)) ≃* matrixPlaneGraph where
  toFun x := ⟨binaryPlaneMatrixEquiv.symm x.val, by
    apply mem_centralizer_singleton_iff.mpr
    apply binaryPlaneMatrixEquiv.injective
    rw [map_mul,map_mul,plane_graph_projection,binaryPlaneMatrixEquiv.apply_symm_apply]
    exact mem_centralizer_singleton_iff.mp x.property⟩
  invFun y := ⟨binaryPlaneMatrixEquiv y.val, by
    apply mem_centralizer_singleton_iff.mpr
    rw [← plane_graph_projection,← map_mul,← map_mul]
    exact congrArg binaryPlaneMatrixEquiv (mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv x := Subtype.ext (binaryPlaneMatrixEquiv.apply_symm_apply x.val)
  right_inv y := Subtype.ext (binaryPlaneMatrixEquiv.symm_apply_apply y.val)
  map_mul' x y := Subtype.ext (map_mul binaryPlaneMatrixEquiv.symm x.val y.val)

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
    (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

/-- The actual source E₂ is the direct product of the ordinary fixed plane
group and the marked graph C2. -/
public def source_E_plane_equiv_fixedPlane (hi : Function.Injective i) :
    E c i true ≃* graphFixedPlane × UnitaryFourOuter.C2 := by
  let e := (centralizer ({modelGraph true} : Set (modelEndpoint true))).equivMapOfInjective
    (endpointMap c i true) (endpointMap_injective c i hi true)
  exact ((e.trans (MulEquiv.subgroupCongr (E_eq_map_centralizer c i hi true).symm)).symm.trans
    modelPlaneGraphEquiv).trans matrixPlaneGraphEquiv

private theorem source_E_plane_equiv_fixedPlane_symm_val (hi : Function.Injective i)
    (a : graphFixedPlane × UnitaryFourOuter.C2) :
    ((source_E_plane_equiv_fixedPlane c i hi).symm a).val =
      endpointMap c i true (binaryPlaneMatrixEquiv (matrixPlaneGraphEquiv.symm a).val) := by
  rfl


private def reorderPlaneProduct : (C2 × S4) × C2 ≃* (C2 × C2) × S4 where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
/-- The literal second endpoint's graph centralizer is E₄ × S₄. -/
public def source_E_plane_equiv (hi : Function.Injective i) :
    E c i true ≃* (C2 × C2) × S4 :=
  (source_E_plane_equiv_fixedPlane c i hi).trans
    ((MulEquiv.prodCongr EndpointPlane.graphFixedPlaneEquivProduct (MulEquiv.refl C2)).trans
      reorderPlaneProduct)
/-- The literal long root has a nonidentity central coordinate in E₂. -/
public theorem source_E_plane_root_coordinate (hi : Function.Injective i)
    (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
    (hz : rootElement c i z ∈ E c i true) :
    (source_E_plane_equiv c i hi ⟨rootElement c i z,hz⟩).1 ≠ 1 := by
  let x : E c i true := ⟨rootElement c i z,hz⟩
  let u := source_E_plane_equiv_fixedPlane c i hi x
  have he : endpointMap c i true
      (binaryPlaneMatrixEquiv (matrixPlaneGraphEquiv.symm u).val) = rootElement c i z := by
    rw [← source_E_plane_equiv_fixedPlane_symm_val]
    exact congrArg Subtype.val ((source_E_plane_equiv_fixedPlane c i hi).symm_apply_apply x)
  rw [source_root_eq_planeParameter c i z h] at he
  have hp : binaryPlaneMatrixEquiv (matrixPlaneGraphEquiv.symm u).val =
      Source.planeInclusion (planeParameterMap (Multiplicative.ofAdd
        (UnitaryFourShortRoot.longParameter F σ))) :=
    endpointMap_injective c i hi true he
  have hproj := congrArg (fun a : modelEndpoint true => a.val.left) hp
  have hmat : u.1.val.val = UnitaryFourPlaneRadical.unipotentSU F σ hσ
      (UnitaryFourShortRoot.longParameter F σ) :=
    projection_injective 1 hn hproj
  have hentry : u.1.val.val.val.val =
      !![1,0,0,1;0,1,0,0;0,0,1,0;0,0,0,1] := by
    rw [hmat]
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [UnitaryFourPlaneRadical.unipotentSU,
        UnitaryFourPlaneRadical.unipotentMatrix,UnitaryFourShortRoot.longParameter]
  have hcoord := EndpointPlane.graphFixedPlaneEquivProduct_long_coordinate u.1 hentry
  intro hbad
  apply hcoord
  exact congrArg Prod.fst hbad

/-- The ordinary second endpoint's fixed subgroup is C₂ × S₄. -/
public def source_D_plane_equiv (hi : Function.Injective i) :
    Dendpoint c i true ≃* C2 × S4 :=
  ((modelFixed true).equivMapOfInjective (ordinaryMap c i true)
    (ordinaryMap_injective c i hi true)).symm.trans
    (ordinaryPlaneFixedEquiv.trans EndpointPlane.graphFixedPlaneEquivProduct)
/-- The inverse plane identification retains the actual ordinary endpoint. -/
public theorem source_D_plane_equiv_symm_val (hi : Function.Injective i) (a : C2 × S4) :
    ((source_D_plane_equiv c i hi).symm a).val =
      ordinaryMap c i true (((planeParabolicSU F (form F σ hσ)).equivMapOfInjective
        (projection 1 hn) (projection_injective 1 hn))
          (EndpointPlane.graphFixedPlaneEquivProduct.symm a).val) := by
  rfl
/-- Both actual graph centralizers have the asserted F.5.3 isomorphism type. -/
public def source_E_equiv (hi : Function.Injective i) (b : Bool) :
    E c i b ≃* (C2 × C2) × S4 := by
  cases b
  · exact source_E_point_equiv c i hi
  · exact source_E_plane_equiv c i hi
/-- Both ordinary fixed endpoint groups have the asserted F.5.3 type. -/
@[expose] public def source_Dendpoint_equiv (hi : Function.Injective i) (b : Bool) :
    Dendpoint c i b ≃* C2 × S4 := by
  cases b
  · exact source_D_point_equiv c i hi
  · exact source_D_plane_equiv c i hi

public theorem source_Dendpoint_equiv_false (hi : Function.Injective i) :
    source_Dendpoint_equiv c i hi false = source_D_point_equiv c i hi := rfl

public theorem source_Dendpoint_equiv_true (hi : Function.Injective i) :
    source_Dendpoint_equiv c i hi true = source_D_plane_equiv c i hi := rfl
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
