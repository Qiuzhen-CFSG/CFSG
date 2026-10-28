module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus
public import Theory.AlgebraicGroup.Morphism.SL2RootRegularity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.RankOne

/-!
# Regular SL₂ maps for the four actual Spin simple-root pairs

The first map acts on two hyperbolic coordinates by a matrix and its inverse
transpose. Transvection generation puts its image in Omega, and the faithful
Spin point map lifts the homomorphism. The prescribed upper and lower curves
are the already regular Clifford root curves, so SL₂ root regularity supplies
a genuine algebraic morphism. The actual simple normalizers transport this map
to the other three simple roots. No algebraic inverse to the Spin cover is used.
The same root formulas identify the diagonal with the source coroot word.
Source: GLS3 §§1.9–1.12; Steinberg §6.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Matrix
open Triality.SimplyConnected.Pinning.PointGeneration
open scoped MatrixGroups
namespace Triality.SimplyConnected.Pinning.RankOne
@[expose] public noncomputable section
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

private def matrixAction (A : SL(2,k)) : QuadraticSpace k →ₗ[k] QuadraticSpace k where
  toFun z :=
    (![A 0 0 * z.1 0 + A 0 1 * z.1 1,A 1 0 * z.1 0 + A 1 1 * z.1 1,z.1 2,z.1 3],
     ![A 1 1 * z.2 0 - A 1 0 * z.2 1,-A 0 1 * z.2 0 + A 0 0 * z.2 1,z.2 2,z.2 3])
  map_add' z w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp <;> ring
  map_smul' c z := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp <;> ring

omit [IsAlgClosed k] [CharP k 2] in
private theorem matrixAction_one : matrixAction k 1 = 1 := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> funext i <;> fin_cases i <;> simp [matrixAction,  ]

omit [IsAlgClosed k] [CharP k 2] in
private theorem matrixAction_mul (A B : SL(2,k)) : matrixAction k (A*B) = matrixAction k A * matrixAction k B := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [matrixAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private def actionHom : SL(2,k) →* Module.End k (QuadraticSpace k) where
  toFun := matrixAction k
  map_one' := matrixAction_one k
  map_mul' := matrixAction_mul k

private def linearAction : SL(2,k) →* (QuadraticSpace k ≃ₗ[k] QuadraticSpace k) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k (QuadraticSpace k)).toMonoidHom.comp
    (actionHom k).toHomUnits

omit [IsAlgClosed k] [CharP k 2] in
private theorem linearAction_apply (A : SL(2,k)) (z : QuadraticSpace k) :
    linearAction k A z = matrixAction k A z := rfl

omit [IsAlgClosed k] [CharP k 2] in
private theorem action_preserves (A : SL(2,k)) (z : QuadraticSpace k) :
    quadraticForm k (linearAction k A z) = quadraticForm k z := by
  have hd := A.det_coe
  rw [Matrix.det_fin_two] at hd
  rw [linearAction_apply]
  simp [quadraticForm, hyperbolicForm_apply, matrixAction, Fin.sum_univ_four]
  linear_combination (z.1 0*z.2 0+z.1 1*z.2 1)*hd

private def orthogonalHom : SL(2,k) →* quadraticIsometrySubgroup (quadraticForm k) where
  toFun A := ⟨linearAction k A,(mem_quadraticIsometrySubgroup _ _).mpr (action_preserves k A)⟩
  map_one' := Subtype.ext (map_one (linearAction k))
  map_mul' A B := Subtype.ext (map_mul (linearAction k) A B)

omit [IsAlgClosed k] [CharP k 2] in
private theorem orthogonal_upper (a : k) :
    orthogonalHom k (SpecialLinearGroup.transvection (i := (0:Fin 2)) (j := 1) (by decide) a) =
      evenOrthogonalRootQuadraticPoint 4 (simpleRoot 0) a := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  change linearAction k _ z = _
  rw [linearAction_apply]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [matrixAction, typeDSimpleRootIndex, evenOrthogonalRootQuadraticPoint,
      evenOrthogonalRootIsometry, hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      SpecialLinearGroup.transvection, Matrix.transvection,
      show (-1:ℝ) ≠ 1 by norm_num, sub_eq_add_neg, add_comm] <;> ring

omit [IsAlgClosed k] in
private theorem orthogonal_lower (a : k) :
    orthogonalHom k (SpecialLinearGroup.transvection (i := (1:Fin 2)) (j := 0) (by decide) a) =
      evenOrthogonalRootQuadraticPoint 4 (negativeSimpleRoot 0) a := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  change linearAction k _ z = _
  rw [linearAction_apply]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [matrixAction, negativeRoot, typeDSimpleRootIndex,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      SpecialLinearGroup.transvection, Matrix.transvection,
      show (-1:ℝ) ≠ 1 by norm_num, CharTwo.neg_eq, add_comm]
  ring
private def omegaHom : SL(2,k) →* OmegaPoints k :=
  (orthogonalHom k).codRestrict _ (by
    intro A
    refine Matrix.SL2.transvection_induction (fun g => orthogonalHom k g ∈ commutator _) ?_ ?_ A
    · intro i j hij a
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · rw [orthogonal_upper]
        exact rootMatrix_mem_omega k _ a
      · rw [orthogonal_lower]
        exact rootMatrix_mem_omega k _ a
      · exact (hij rfl).elim
    · intro A B hA hB
      simpa only [map_mul] using (commutator _).mul_mem hA hB)

private def spinHom : SL(2,k) →* Points k :=
  (omegaPointEquiv k).symm.toMonoidHom.comp (omegaHom k)

private theorem naturalAction_spinHom (A : SL(2,k)) :
    naturalAction k (spinHom k A) = orthogonalHom k A := by
  exact congrArg Subtype.val ((omegaPointEquiv k).apply_symm_apply (omegaHom k A))

private theorem spinHom_upper (a : k) :
    spinHom k (SpecialLinearGroup.transvection (i := (0:Fin 2)) (j := 1) (by decide) a) =
      rootPoint k (simpleRoot 0) a := by
  apply naturalAction_injective k
  rw [naturalAction_spinHom,naturalAction_rootPoint,orthogonal_upper]

private theorem spinHom_lower (a : k) :
    spinHom k (SpecialLinearGroup.transvection (i := (1:Fin 2)) (j := 0) (by decide) a) =
      rootPoint k (negativeSimpleRoot 0) a := by
  apply naturalAction_injective k
  rw [naturalAction_spinHom,naturalAction_rootPoint,orthogonal_lower]

omit [CharP k 2] in
private theorem slPoint_upper (a : k) :
    slPointMulEquiv 2 (standardSL2UpperMorphism.onPoints (kPlusPoint a)) =
      SpecialLinearGroup.transvection (i := (0:Fin 2)) (j := 1) (by decide) a := by
  rw [slPointMulEquiv_apply, standardSL2UpperMorphism_kPlusPoint, typeASLRootPoint,
    Equiv.apply_symm_apply]
  rfl

omit [CharP k 2] in
private theorem slPoint_lower (a : k) :
    slPointMulEquiv 2 (standardSL2LowerMorphism.onPoints (kPlusPoint a)) =
      SpecialLinearGroup.transvection (i := (1:Fin 2)) (j := 0) (by decide) a := by
  rw [slPointMulEquiv_apply, standardSL2LowerMorphism_kPlusPoint, typeASLRootPoint,
    Equiv.apply_symm_apply]
  rfl

private theorem exists_morphism : ∃ f : Morphism (slVariety k 2) (groupVariety k),
    f.onPoints = (spinHom k).comp (slPointMulEquiv 2).toMonoidHom := by
  apply exists_sl2Morphism_of_regular_rootCurves
    ((spinHom k).comp (slPointMulEquiv 2).toMonoidHom)
    (cliffordRootMorphism k (simpleRoot 0)) (cliffordRootMorphism k (negativeSimpleRoot 0))
  · intro s
    obtain ⟨a,rfl⟩ := (additiveGroupPointEquiv k).symm.surjective s
    change spinHom k (slPointMulEquiv 2
      (standardSL2UpperMorphism.onPoints (kPlusPoint a.toAdd))) = _
    rw [slPoint_upper,spinHom_upper]
    exact (cliffordRootMorphism_kPlusPoint k _ _).symm
  · intro s
    obtain ⟨a,rfl⟩ := (additiveGroupPointEquiv k).symm.surjective s
    change spinHom k (slPointMulEquiv 2
      (standardSL2LowerMorphism.onPoints (kPlusPoint a.toAdd))) = _
    rw [slPoint_lower,spinHom_lower]
    exact (cliffordRootMorphism_kPlusPoint k _ _).symm

def HasRootMap (r : RootIndex) : Prop := ∃ f : Morphism (slVariety k 2) (groupVariety k),
  (∀ a, f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint a)) = rootPoint k r a) ∧
  (∀ a, f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint a)) =
    rootPoint k (negativeRoot r) a)

private theorem hasRootMap_zero : HasRootMap k (simpleRoot 0) := by
  obtain ⟨f,hf⟩ := exists_morphism k
  refine ⟨f,?_,?_⟩
  · intro a
    rw [hf]
    change spinHom k (slPointMulEquiv 2 (standardSL2UpperMorphism.onPoints (kPlusPoint a))) = _
    rw [slPoint_upper,spinHom_upper]
  · intro a
    rw [hf]
    change spinHom k (slPointMulEquiv 2 (standardSL2LowerMorphism.onPoints (kPlusPoint a))) = _
    rw [slPoint_lower,spinHom_lower]

private def reflectionMorphism (i : Fin 4) : Morphism (groupVariety k) (groupVariety k) where
  toVariety := conjugationByMorphism _ ((simpleNormalizer k i)⁻¹)
  map_one := by
    rw [conjugationByMorphism_apply, inv_inv]
    simpa only [mul_one] using inv_mul_cancel (simpleNormalizer k i)
  map_mul g h := by simp only [conjugationByMorphism_apply]; group

private theorem hasRootMap_reflection (i : Fin 4) {r : RootIndex} (h : HasRootMap k r) :
    HasRootMap k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) r) := by
  obtain ⟨f,hp,hm⟩ := h
  refine ⟨(reflectionMorphism k i).comp f,?_,?_⟩
  · intro a
    change (reflectionMorphism k i).onPoints (f.onPoints _) = _
    rw [hp]
    change (conjugationByMorphism _ _).toFun _ = _
    rw [conjugationByMorphism_apply,inv_inv,simpleNormalizer_rootPoint_conjugation]
  · intro a
    change (reflectionMorphism k i).onPoints (f.onPoints _) = _
    rw [hm]
    change (conjugationByMorphism _ _).toFun _ = _
    rw [conjugationByMorphism_apply,inv_inv,simpleNormalizer_rootPoint_conjugation,
      reflection_negativeRoot]

private theorem adjacent_reflection (i j : Fin 4)
    (h : (i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=1 ∧ j=3)) :
    (typeDRootPairing 2).reflectionPerm (simpleRoot i)
      ((typeDRootPairing 2).reflectionPerm (simpleRoot j) (simpleRoot i)) = simpleRoot j := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · conv_lhs => arg 2; arg 2; rw [PointGeneration.simpleRoot_eq_rootAt]
    rw [PointGeneration.reflection_rootAt,PointGeneration.reflection_rootAt]
    rfl
  · conv_lhs => arg 2; arg 2; rw [PointGeneration.simpleRoot_eq_rootAt]
    rw [PointGeneration.reflection_rootAt,PointGeneration.reflection_rootAt]
    rfl
  · conv_lhs => arg 2; arg 2; rw [PointGeneration.simpleRoot_eq_rootAt]
    rw [PointGeneration.reflection_rootAt,PointGeneration.reflection_rootAt]
    rfl

theorem hasRootMap_simple (i : Fin 4) : HasRootMap k (simpleRoot i) := by
  have h0 := hasRootMap_zero k
  have h1 := hasRootMap_reflection k 0 (hasRootMap_reflection k 1 h0)
  rw [adjacent_reflection 0 1 (Or.inl ⟨rfl,rfl⟩)] at h1
  fin_cases i
  · exact h0
  · exact h1
  · have h2 := hasRootMap_reflection k 1 (hasRootMap_reflection k 2 h1)
    rw [adjacent_reflection 1 2 (Or.inr (Or.inl ⟨rfl,rfl⟩))] at h2
    exact h2
  · have h3 := hasRootMap_reflection k 1 (hasRootMap_reflection k 3 h1)
    rw [adjacent_reflection 1 3 (Or.inr (Or.inr ⟨rfl,rfl⟩))] at h3
    exact h3

theorem rootMap_coroot {r : RootIndex}
    (f : Morphism (slVariety k 2) (groupVariety k))
    (hp : ∀ a, f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint a)) = rootPoint k r a)
    (hm : ∀ a, f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint a)) =
      rootPoint k (negativeRoot r) a) (t : Variety.Point (KMult k)) :
    f.onPoints (binarySL2Coroot.onPoints t) = corootWord k r (dPointEquiv 1 t 0) := by
  change f.onPoints ((binarySL2Coroot (k := k)).toVariety.toFun t) = _
  rw [binarySL2Coroot_toVariety,binaryCorootWord_apply]
  simp only [map_mul,map_inv]
  have hp' (a : k) : f.onPoints (standardSL2UpperMorphism.toVariety.toFun (kPlusPoint a)) =
      rootPoint k r a := hp a
  have hm' (a : k) : f.onPoints (standardSL2LowerMorphism.toVariety.toFun (kPlusPoint a)) =
      rootPoint k (negativeRoot r) a := hm a
  simp only [hp',hm']
  simp only [corootWord,normalizerWord,Units.val_one,inv_one,CharTwo.neg_eq]

end
end Triality.SimplyConnected.Pinning.RankOne
