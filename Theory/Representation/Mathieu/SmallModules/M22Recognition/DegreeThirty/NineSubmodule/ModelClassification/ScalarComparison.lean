module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.ModelClassification.Absolute
public import Theory.Representation.SL3.BinaryDefiningFactors.SmallPatterns


/-!
# The Hermitian models after scalar extension

Map a Hermitian matrix into matrices over any characteristic-two coefficient
field containing GF(4), then use the coordinates of the twisted tensor.
This is a nonzero intertwiner. The tensor-word simplicity theorem makes it
surjective; both dimensions are nine, so it is an equivalence. The canonical
dual pairing gives the comparison for the contragredient model as well.

The statement uses the literal central quotient and the actions in `Models`.
Its consumer is `exists_point_model_equiv` in the parent module.
Source: Aschbacher–Smith H.4.2–4, printed pp.380–381; GLS III, 2.8.6 and
2.8.10(c) for tensor-word simplicity.
-/

@[expose] public section

open Representation
open scoped TensorProduct
open Representation.SL3.BinaryDefiningFactors
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.ModelClassification
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] [CharP K 2]
local instance : Algebra (ZMod 2) K := ZMod.algebra K 2

private def twistedTensor (ι : Matrix.PSL3Four.F →+* K) :=
  (natural ι).tprod (natural ((frobenius K 2).comp ι))

private def naturalWordEquiv (ι : Matrix.PSL3Four.F →+* K) :
    (wordRep ι (modelWord false)).Equiv (twistedTensor ι) :=
  tensorRightEquiv (Representation.TensorProduct.rid K
    (natural ((frobenius K 2).comp ι)))

private def matrixCoordinates :
    ((Fin 3 → K) ⊗[K] (Fin 3 → K)) ≃ₗ[K] Matrix (Fin 3) (Fin 3) K :=
  (_root_.TensorProduct.comm K _ _).trans (TensorProduct.piScalarRight K K (Fin 3 → K) (Fin 3))

omit [CharP K 2] in
private lemma matrixCoordinates_tmul (x y : Fin 3 → K) :
    matrixCoordinates (x ⊗ₜ[K] y) = Matrix.vecMulVec x y := by
  ext i j
  change (TensorProduct.piScalarRight K K (Fin 3 → K) (Fin 3))
    (y ⊗ₜ[K] x) i j = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

private lemma matrixCoordinates_action (ι : Matrix.PSL3Four.F →+* K)
    (g : Matrix.PSL3Four.SL) (u : (Fin 3 → K) ⊗[K] (Fin 3 → K)) :
    matrixCoordinates (twistedTensor ι g u) =
      g.val.map ι * matrixCoordinates u *
        (g.val.map ((frobenius K 2).comp ι)).transpose := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, Matrix.mul_add, Matrix.add_mul]
  | tmul x y =>
    change matrixCoordinates (natural ι g x ⊗ₜ[K] natural ((frobenius K 2).comp ι) g y) = _
    rw [matrixCoordinates_tmul, matrixCoordinates_tmul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    congr 1
    exact (Matrix.vecMul_transpose _ y).symm

private def hermitianToMatrix (ι : Matrix.PSL3Four.F →+* K) :
    Models.HermitianSpace →ₗ[ZMod 2] Matrix (Fin 3) (Fin 3) K :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun X := X.val.map ι
    map_zero' := by ext i j; exact map_zero ι
    map_add' X Y := by ext i j; exact map_add ι _ _ }

private lemma hermitianToMatrix_action (ι : Matrix.PSL3Four.F →+* K)
    (g : Matrix.PSL3Four.SL) (X : Models.HermitianSpace) :
    hermitianToMatrix ι (HermitianTensorThree.binaryAction 1 g X) =
      g.val.map ι * hermitianToMatrix ι X *
        (g.val.map ((frobenius K 2).comp ι)).transpose := by
  change (g.val * X.val * HermitianTensorThree.adjoint 1 g.val).map ι = _
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 1
  ext i j
  exact map_pow ι (g.val j i) 2

private def hermitianTensorMap (ι : Matrix.PSL3Four.F →+* K) :
    (extendScalars K (HermitianTensorThree.binaryAction 1)).IntertwiningMap
      (twistedTensor ι) where
  toLinearMap := LinearMap.liftBaseChange K
    (((matrixCoordinates (K := K)).symm.restrictScalars (ZMod 2)).toLinearMap.comp
      (hermitianToMatrix ι))
  isIntertwining' g := by
    ext X
    change (1 : K) • matrixCoordinates.symm
      (hermitianToMatrix ι (HermitianTensorThree.binaryAction 1 g X)) =
        twistedTensor ι g ((1 : K) • matrixCoordinates.symm (hermitianToMatrix ι X))
    simp only [one_smul]
    apply (matrixCoordinates (K := K)).injective
    rw [LinearEquiv.apply_symm_apply, matrixCoordinates_action, LinearEquiv.apply_symm_apply]
    exact hermitianToMatrix_action ι g X

private theorem tensor_irreducible (ι : Matrix.PSL3Four.F →+* K) :
    IsIrreducible (twistedTensor ι) := by
  let e := (naturalWordEquiv ι).symm
  let f := IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mpr ((irreducible_iff_isSimpleModule_asModule _).mp
    (wordRep_isIrreducible ι 2 (by simpa using Matrix.PSL3Four.card_F) _ rfl))

private theorem hermitianTensorMap_ne_zero (ι : Matrix.PSL3Four.F →+* K) :
    hermitianTensorMap ι ≠ 0 := by
  intro h
  let X : Models.HermitianSpace := ⟨1, HermitianTensorThree.adjoint_one 1⟩
  have he := congrArg (fun f : (extendScalars K (HermitianTensorThree.binaryAction 1)).IntertwiningMap
      (twistedTensor ι) => matrixCoordinates (f ((1 : K) ⊗ₜ[ZMod 2] X))) h
  have hv := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) he
  simp [hermitianTensorMap, hermitianToMatrix, X] at hv

private def hermitianNaturalEquiv (ι : Matrix.PSL3Four.F →+* K) :
    (extendScalars K (HermitianTensorThree.binaryAction 1)).Equiv
      (wordRep ι (modelWord false)) := by
  letI : IsIrreducible (twistedTensor ι) := tensor_irreducible ι
  have hs : Function.Surjective (hermitianTensorMap ι) :=
    (IsIrreducible.surjective_or_eq_zero (hermitianTensorMap ι)).resolve_right
      (hermitianTensorMap_ne_zero ι)
  have hd : Module.finrank K (K ⊗[ZMod 2] Models.HermitianSpace) =
      Module.finrank K ((Fin 3 → K) ⊗[K] (Fin 3 → K)) := by
    rw [Module.finrank_baseChange, HermitianTensorThree.finrank_binary]
    simp [Module.finrank_tensorProduct]
  exact (IntertwiningMap.ofBijective (hermitianTensorMap ι)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs, hs⟩).trans
      (naturalWordEquiv ι).symm

private def dualWordEquiv (ι : Matrix.PSL3Four.F →+* K) :
    (wordRep ι (modelWord true)).Equiv (wordRep ι (modelWord false)).dual :=
  (tensorRightEquiv (Representation.TensorProduct.rid K
    (natural ((frobenius K 2).comp ι)).dual)).trans
      ((dualTensorEquiv (natural ι) (natural ((frobenius K 2).comp ι))).trans
        (BinaryFieldDescent.dualEquiv (naturalWordEquiv ι).symm))

/-- The Hermitian model and its dual extend to their actual constant words. -/
theorem model_extension (ι : Matrix.PSL3Four.F →+* K) (b : Bool) :
    Nonempty ((extendScalars K ((Models.projective b).comp
      (QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL)))).Equiv
        (wordRep ι (modelWord b))) := by
  have he : Models.hermitian.comp (QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL)) =
      HermitianTensorThree.binaryAction 1 := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro X
    exact Models.hermitian_mk g X
  cases b
  · change Nonempty ((extendScalars K (Models.hermitian.comp _)).Equiv _)
    rw [he]
    exact ⟨hermitianNaturalEquiv ι⟩
  · have heD : Models.hermitian.dual.comp
        (QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL)) =
          (HermitianTensorThree.binaryAction 1).dual := by
      ext g f X
      change f (Models.hermitian (QuotientGroup.mk g⁻¹) X) = _
      rw [Models.hermitian_mk]
      rfl
    change Nonempty ((extendScalars K (Models.hermitian.dual.comp _)).Equiv _)
    rw [heD]
    exact ⟨(BinaryFieldDescent.dualBaseChange (HermitianTensorThree.binaryAction 1)).trans
      ((BinaryFieldDescent.dualEquiv (hermitianNaturalEquiv ι)).trans (dualWordEquiv ι).symm)⟩

end
end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.ModelClassification
