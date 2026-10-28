module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionResidualDihedralLift
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionResidualJoinData
/-!
# The literal generators of the endpoint residual cores

The endpoint C₂ × S₄ inverse maps retain their binary matrices. Comparing
four Klein-four generators with the faithful common dihedral representation
identifies the two endpoint placements. Its central involution is exactly
the source product tz. Conjugacy in the S₄ core lifts through the actual
endpoint map, so its conjugators remain in C_G(f).

Source: Aschbacher–Smith F.5.5, printed pp.301–302.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Matrix Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "D8" => DihedralGroup 4
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)
open ResidualJoinModel

theorem sourceHom_eq_point (a : D8) (x : pointParabolicSU F (form F σ hσ))
    (hx : x.val=matrixElement a) :
    ordinaryMap c i false (UnitaryTwo.PointInvolution.matrixPointEquiv x)=sourceHom c i a := by
  apply congrArg i
  apply congrArg c.left
  apply Subtype.ext
  apply congrArg SemidirectProduct.inl
  exact congrArg (projection 1 hn) hx

theorem sourceHom_eq_plane (a : D8) (x : planeParabolicSU F (form F σ hσ))
    (hx : x.val=matrixElement a) :
    ordinaryMap c i true (((planeParabolicSU F (form F σ hσ)).equivMapOfInjective
      (projection 1 hn) (projection_injective 1 hn)) x)=sourceHom c i a := by
  change i (c.right _) = i (c.middle _)
  rw [DFunLike.congr_fun c.compatible]
  apply congrArg i
  apply congrArg c.right
  apply Subtype.ext
  apply congrArg SemidirectProduct.inl
  exact congrArg (projection 1 hn) hx

private theorem point0_matrix :
    (graphFixedPointEquivLocal.symm (EndpointPoint.graphFixedLocalEquivProduct.symm
      (1,(doubleSwap 0)))).val.val = matrixElement (.sr 0) := by
  apply Subtype.ext
  apply Units.ext
  change (EndpointPoint.graphFixedLocalEquivProduct.symm (1,(doubleSwap 0))).val.val.val.val = _
  simp only [doubleSwap, Fin.reduceEq, if_true, if_false]
  rw [EndpointPoint.graphFixedLocalEquivProduct_symm_klein_matrices.1]
  change _ = (binaryMatrix (.sr 0)).map binaryCast
  rw [binary_point_generator]
  ext j k
  fin_cases j <;> fin_cases k <;> simp [pointGenerator]
private theorem point1_matrix :
    (graphFixedPointEquivLocal.symm (EndpointPoint.graphFixedLocalEquivProduct.symm
      (1,(doubleSwap 1)))).val.val = matrixElement (.sr 2) := by
  apply Subtype.ext
  apply Units.ext
  change (EndpointPoint.graphFixedLocalEquivProduct.symm (1,(doubleSwap 1))).val.val.val.val = _
  simp only [doubleSwap, Fin.reduceEq, if_true, if_false]
  rw [EndpointPoint.graphFixedLocalEquivProduct_symm_klein_matrices.2]
  have hm : binaryMatrix (.sr 2)=!![1,1,0,1;0,1,0,0;0,0,1,1;0,0,0,1] := by decide +kernel
  change _ = (binaryMatrix (.sr 2)).map binaryCast
  rw [hm]
  ext j k
  fin_cases j <;> fin_cases k <;> simp
private theorem plane0_matrix :
    (EndpointPlane.graphFixedPlaneEquivProduct.symm (1,(doubleSwap 0))).val.val = matrixElement (.r 2) := by
  apply Subtype.ext
  apply Units.ext
  simp only [doubleSwap, Fin.reduceEq, if_true, if_false]
  rw [EndpointPlane.graphFixedPlaneEquivProduct_symm_klein_matrices.1]
  change _ = (binaryMatrix (.r 2)).map binaryCast
  rw [binary_center]
  ext j k
  fin_cases j <;> fin_cases k <;> simp
private theorem plane1_matrix :
    (EndpointPlane.graphFixedPlaneEquivProduct.symm (1,(doubleSwap 1))).val.val = matrixElement (.sr 1) := by
  apply Subtype.ext
  apply Units.ext
  simp only [doubleSwap, Fin.reduceEq, if_true, if_false]
  rw [EndpointPlane.graphFixedPlaneEquivProduct_symm_klein_matrices.2]
  change _ = (binaryMatrix (.sr 1)).map binaryCast
  rw [binary_plane_generator]
  ext j k
  fin_cases j <;> fin_cases k <;> simp [planeGenerator]

theorem sourceEndpointCoreMap_point0 (hi : Function.Injective i) :
    sourceEndpointCoreMap c i hi false (doubleSwap 0) = sourceHom c i (.sr 0) := by
  simp only [sourceEndpointCoreMap, source_Dendpoint_equiv_false, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inr_apply, Subgroup.coe_subtype]
  change ((source_D_point_equiv c i hi).symm (1,(doubleSwap 0))).val = _
  rw [source_D_point_equiv_symm_val]
  exact sourceHom_eq_point c i _ _ point0_matrix

theorem sourceEndpointCoreMap_point1 (hi : Function.Injective i) :
    sourceEndpointCoreMap c i hi false (doubleSwap 1) = sourceHom c i (.sr 2) := by
  simp only [sourceEndpointCoreMap, source_Dendpoint_equiv_false, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inr_apply, Subgroup.coe_subtype]
  change ((source_D_point_equiv c i hi).symm (1,(doubleSwap 1))).val = _
  rw [source_D_point_equiv_symm_val]
  exact sourceHom_eq_point c i _ _ point1_matrix

theorem sourceEndpointCoreMap_plane0 (hi : Function.Injective i) :
    sourceEndpointCoreMap c i hi true (doubleSwap 0) = sourceHom c i (.r 2) := by
  simp only [sourceEndpointCoreMap, source_Dendpoint_equiv_true, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inr_apply, Subgroup.coe_subtype]
  change ((source_D_plane_equiv c i hi).symm (1,(doubleSwap 0))).val = _
  rw [source_D_plane_equiv_symm_val]
  exact sourceHom_eq_plane c i _ _ plane0_matrix

theorem sourceEndpointCoreMap_plane1 (hi : Function.Injective i) :
    sourceEndpointCoreMap c i hi true (doubleSwap 1) = sourceHom c i (.sr 1) := by
  simp only [sourceEndpointCoreMap, source_Dendpoint_equiv_true, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inr_apply, Subgroup.coe_subtype]
  change ((source_D_plane_equiv c i hi).symm (1,(doubleSwap 1))).val = _
  rw [source_D_plane_equiv_symm_val]
  exact sourceHom_eq_plane c i _ _ plane1_matrix
theorem sourceHom_center (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    sourceHom c i (.r 2)=sourceMarkedShort c i * rootElement c i z := by
  rw [source_root_eq_planeParameter c i z h]
  unfold sourceMarkedShort
  rw [←map_mul]
  change i (c.middle _) = i (c.right _)
  rw [DFunLike.congr_fun c.compatible]
  apply congrArg i
  apply congrArg c.right
  apply Subtype.ext
  apply congrArg SemidirectProduct.inl
  apply congrArg (projection 1 hn)
  apply Subtype.ext
  apply Units.ext
  change (binaryMatrix (.r 2)).map binaryCast =
    UnitaryFourPlaneRadical.unipotentMatrix F
      (UnitaryFourShortRoot.shortParameter F σ + UnitaryFourShortRoot.longParameter F σ)
  rw [binary_center]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [UnitaryFourPlaneRadical.unipotentMatrix,
      UnitaryFourShortRoot.shortParameter,UnitaryFourShortRoot.longParameter]

theorem sourceEndpointCoreMap_mem_D (hi : Function.Injective i) (b : Bool)
    (a : Equiv.Perm (Fin 4)) : sourceEndpointCoreMap c i hi b a∈Dendpoint c i b :=
  ((source_Dendpoint_equiv c i hi b).symm (1,a)).property

variable [Finite G]

theorem sourceEndpointResidualCore_conjugate (hi : Function.Injective i) (b : Bool)
    (x : G) (hx : x∈sourceEndpointResidualCore c i b) (hx1 : x≠1)
    (y : G) (hy : y∈sourceEndpointResidualCore c i b) (hy1 : y≠1) :
    ∃ g∈Dendpoint c i b, g*x*g⁻¹=y := by
  rw [sourceEndpointResidualCore_eq_map c i hi b] at hx hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨d,hd,rfl⟩ := hy
  have ha1 : a≠1 := by intro h; apply hx1; rw [h,map_one]
  have hd1 : d≠1 := by intro h; apply hy1; rw [h,map_one]
  obtain ⟨g,hg⟩ := core_conjugate a ha ha1 d hd hd1
  refine ⟨sourceEndpointCoreMap c i hi b g,sourceEndpointCoreMap_mem_D c i hi b g,?_⟩
  rw [←map_inv,←map_mul,←map_mul,hg]

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
