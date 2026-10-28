module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointCentralizer
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.AmbientLocalCores
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PCoreImage

/-!
# The full original point-centralizer core image

The solvable residual of the original point-parabolic preimage maps onto
the full field-four parabolic. A two-group kernel makes its intrinsic
two-core map onto the native root plane. The actual field transport then
identifies that root plane with the Hermitian point radical.

These maps supply the original actor in the commutator calculation of
Aschbacher–Smith 8.2.11(2), printed p.722, refs/quasithin.pdf. No central
covering kernel is discarded, and the point and plane parabolics remain
distinct.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3Even.UnipotentGeometry
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
set_option backward.isDefEq.respectTransparency false

theorem native_point_root_image :
    (Matrix.PSL3.RootPlaneGeometry.rootPlane Matrix.PSL3Four.F true).map
      ((binaryImage 1).subtype.comp nativeBinaryEquiv.toMonoidHom) = UnipotentRadicals.point 1 := by
  let k := Matrix.PSL3.ExceptionalFourCover.fieldEquiv (E 1) (by rw [card_E]; norm_num)
  have he (a c : Matrix.PSL3Four.F) :
      (nativeBinaryEquiv (QuotientGroup.mk' _ (specialLinear Matrix.PSL3Four.F ⟨a,0,c⟩))).val =
        UnipotentRadicals.unipotentHom 1 ⟨k a,0,k c⟩ := by
    rw [nativeBinaryEquiv_mk]
    apply congrArg (binaryActionHom 1)
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Atlas.fieldEquivSL,specialLinear,matrix,k]
  apply le_antisymm
  · rintro _ ⟨_,⟨a,ha,rfl⟩,rfl⟩
    obtain ⟨x,c,rfl⟩ := (Matrix.PSL3.RootPlaneGeometry.mem_rootPlaneSL_point _ a).mp ha
    change (nativeBinaryEquiv (QuotientGroup.mk' _ (specialLinear _ ⟨x,0,c⟩))).val ∈ _
    rw [he]
    exact mem_map_of_mem _ ((mem_V₁ _ _).mpr rfl)
  · rintro _ ⟨u,hu,rfl⟩
    have hy := (mem_V₁ (E 1) u).mp hu
    let a := specialLinear Matrix.PSL3Four.F ⟨k.symm u.x,0,k.symm u.c⟩
    refine ⟨QuotientGroup.mk' _ a,mem_map_of_mem _ ?_,?_⟩
    · exact (Matrix.PSL3.RootPlaneGeometry.mem_rootPlaneSL_point _ a).mpr ⟨_,_,rfl⟩
    · change (nativeBinaryEquiv (QuotientGroup.mk' _ a)).val = _
      rw [he]
      apply congrArg (UnipotentRadicals.unipotentHom 1)
      exact U.ext (k.apply_symm_apply _) hy.symm (k.apply_symm_apply _)

variable {G : Type*} [Group G] [Finite G]
/-- The residual and its entire original two-core have their exact marked images. -/
theorem point_residual_images
    (L : Subgroup G) (z : G) (f : L →* Matrix.PSL3Four.PSL)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hP : Matrix.PSL3Four.ElementaryParabolic.liftedParabolic f true =
      (centralizer ({z} : Set G)).subgroupOf L) :
    ((Centralizer.localResidual L z).subgroupOf L).map f =
      Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F true ∧
    (((Centralizer.localResidual L z).pCoreIn 2).subgroupOf L).map f =
      Matrix.PSL3.RootPlaneGeometry.rootPlane Matrix.PSL3Four.F true := by
  let P₀ := Matrix.PSL3Four.ElementaryParabolic.liftedParabolic f true
  let P := L ⊓ centralizer ({z} : Set G)
  let R := Centralizer.localResidual L z
  have hRL : R ≤ L := (Centralizer.localResidual_le L z).trans inf_le_left
  have hPmap : P₀.map L.subtype = P := by
    dsimp only [P₀,P]
    rw [hP,subgroupOf_map_subtype,inf_comm]
  let eP : P₀ ≃* P := (P₀.equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr hPmap)
  have hRmap : (solvableResidual P₀).map P₀.subtype = R.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hRL,map_map]
    have hm := congrArg (Subgroup.map P.subtype)
      (map_solvableResidual_eq eP.toMonoidHom eP.surjective)
    rw [map_map] at hm
    exact hm
  have hR : (R.subgroupOf L).map f = Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F true := by
    rw [←hRmap,Matrix.PSL3Four.ElementaryParabolic.residual_image f hf,
      Matrix.PSL3Four.ElementaryParabolic.native_parabolic_eq_local]
  refine ⟨hR,?_⟩
  rw [←pCoreIn_subgroupOf 2 R L hRL,map_pCoreIn_of_ker_isPGroup f hk,hR,
    Matrix.PSL3Four.ElementaryParabolic.native_parabolic_eq_local]
  exact Matrix.PSL3.LinearThree.OuterExtensions.AmbientLocalCores.local_core_eq_rootPlane
    Matrix.PSL3Four.F (f := 2) (by decide) (by rw [Matrix.PSL3Four.card_F]; norm_num) true

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
