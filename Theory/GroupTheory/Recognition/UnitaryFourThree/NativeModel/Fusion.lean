module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.NativeModel.Residual
public import Theory.GroupTheory.Recognition.UnitaryFourThree.Orbit
/-!
# A fused involution in the native PSU₄(3) quaternion core

A signed interchange of the middle coordinates is an actual determinant-one
unitary matrix. Its right conjugate of the standard involution is the image
of the two quaternion generators, up to a scalar in the full projective
kernel. The explicit kernel of the quaternion pair shows that this conjugate
lies outside the marked central line. Together with the residual calculation
this supplies every clause of the original centralizer hypothesis.

Source: Aschbacher, *Sporadic Groups* (1994), Hypothesis 45.1, printed p.242.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
open RepresentativeCore
open RepresentativeCore.QuotientCore.Blocks

def fusionMatrix : Mat₄ := !![-1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]
theorem fusionMatrix_sq : fusionMatrix * fusionMatrix = 1 := by decide
def fusionGL : GL (Fin 4) FiniteField.Nine := ⟨fusionMatrix,fusionMatrix,fusionMatrix_sq,fusionMatrix_sq⟩
def fusionSU : SU := ⟨fusionGL,by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · change fusionMatrix.conjTranspose * 1 * fusionMatrix = 1
    decide
  · apply Units.ext
    change fusionMatrix.det=1
    decide⟩
def fusion : Carrier 4 := project 4 fusionSU

theorem fusionSU_inv : fusionSU⁻¹=fusionSU := by
  apply Subtype.ext
  apply Units.ext
  rw [su_inv]
  change fusionMatrix.conjTranspose=fusionMatrix
  decide

theorem fusion_conjugate :
    fusion⁻¹ * standardInvolution * fusion = (quaternionPair (.a 1,.a 1)).val := by
  change (project 4 fusionSU)⁻¹ * project 4 standardInvolutionSU * project 4 fusionSU = _
  rw [← map_inv,← map_mul,← map_mul]
  apply Subtype.ext
  change ProjGenLinGroup.mk (fusionSU⁻¹ * standardInvolutionSU * fusionSU).val =
    ProjGenLinGroup.mk (quaternionPairSU (.a 1,.a 1)).val
  apply ProjGenLinGroup.mk_eq_mk_iff.mpr
  let i : FiniteField.Nineˣ := Units.mk0 (-imaginary) (by decide)
  refine ⟨i,Units.ext ?_⟩
  rw [fusionSU_inv]
  change (fusionMatrix * standardInvolutionMatrix * fusionMatrix) * Matrix.scalar (Fin 4) (-imaginary) =
    RepresentativeCore.block (quaternionMatrix (.a 1)) (quaternionMatrix (.a 1))
  decide

theorem quaternion_fused_not_line :
    (quaternionPair (.a 1,.a 1)).val ∉ zpowers standardInvolution := by
  classical
  intro h
  rw [mem_zpowers_iff_mem_range_orderOf,standardInvolution_orderOf] at h
  have hh : (quaternionPair (.a 1,.a 1)).val=1 ∨
      (quaternionPair (.a 1,.a 1)).val=standardInvolution := by
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp h
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact Or.inl (by simpa only [pow_zero] using he.symm)
    · exact Or.inr (by simpa only [pow_one] using he.symm)
  rcases hh with hh | hh
  · have hp : quaternionPair (.a 1,.a 1)=1 := Subtype.ext hh
    have hk := (quaternionPair_eq_one_iff _).mp hp
    exact (by decide : ¬ ((QuaternionGroup.a 1,QuaternionGroup.a 1) = (1 : QuaternionGroup 2 × QuaternionGroup 2) ∨
      (QuaternionGroup.a 1,QuaternionGroup.a 1) = (QuaternionGroup.a 2,QuaternionGroup.a 2))) hk
  · have hp : quaternionPair (.a 1,.a 1)=quaternionPair (.a 2,1) :=
      Subtype.ext (hh.trans (congrArg Subtype.val quaternionPair_sign_left).symm)
    have hk : quaternionPair ((.a 1,.a 1) * (.a 2,1)⁻¹)=1 := by
      rw [map_mul,map_inv,hp,mul_inv_cancel]
    have hq := (quaternionPair_eq_one_iff _).mp hk
    exact (by decide : ¬ (((QuaternionGroup.a 1,QuaternionGroup.a 1) * (QuaternionGroup.a 2,1)⁻¹) =
      (1 : QuaternionGroup 2 × QuaternionGroup 2) ∨
      ((QuaternionGroup.a 1,QuaternionGroup.a 1) * (QuaternionGroup.a 2,1)⁻¹) =
      (QuaternionGroup.a 2,QuaternionGroup.a 2))) hq

theorem native_fused : ∃ g : Carrier 4,
    g⁻¹ * standardInvolution * g ∈ Theory.GroupTheory.Recognition.UnitaryFourThree.core standardInvolution ∧
    g⁻¹ * standardInvolution * g ∉ zpowers standardInvolution := by
  refine ⟨fusion,?_,?_⟩
  · rw [fusion_conjugate,native_core_eq]
    exact mem_map_of_mem standardCentralizer.subtype (quaternionPair_mem _)
  · rw [fusion_conjugate]
    exact quaternion_fused_not_line

theorem native_centralizerHypothesis :
    Theory.GroupTheory.Recognition.UnitaryFourThree.CentralizerHypothesis standardInvolution where
  involution := standardInvolution_orderOf
  factors := ⟨leftFactor,rightFactor,nativeFactorData.span,nativeFactorData.normal_left,
    nativeFactorData.normal_right,nativeFactorData.left_model,nativeFactorData.right_model,
    nativeFactorData.intersection⟩
  generalizedFitting_eq := native_generalizedFitting
  fused := native_fused

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
