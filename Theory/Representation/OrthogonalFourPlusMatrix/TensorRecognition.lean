module
public import Theory.Representation.QuadraticFourGroup.TensorClassification
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Mathlib.GroupTheory.IsPerfect
/-!
# Recognizing the literal binary determinant action

An irreducible binary action of PSL₂(4) × PSL₂(4), with fixed-point-free
order-three elements in each factor, is the determinant action on two-by-two
matrices over the concrete field of four elements. The proved natural-tensor
classification supplies faithful two-dimensional factors. Their determinants
are one by perfectness, and finite cardinality makes their matrix maps
isomorphisms. Outer-product coordinates turn the second factor into its
inverse transpose, giving exactly M ↦ A M B⁻¹. Entrywise field transport then
retains the literal `Binary.action` used by the orthogonal calculations.

Source: Aschbacher–Smith D.3.7, printed pp.197–199; the cubic-free tensor
classification used here is GLS2 Theorem 25.14, Step 5. Deriving cubic
fixed-point-freeness from the original cubic-ratio bound is a separate input.
-/

@[expose] public noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix Representation
namespace ClassicalOrthogonal.FourPlusMatrix.TensorRecognition
variable {F J : Type*} [Field F] [Group J] [Group.IsPerfect J]

private def matrixHom (τ : Representation F J (Fin 2 → F)) :
    J →* Matrix (Fin 2) (Fin 2) F :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp τ

private theorem matrixHom_det (τ : Representation F J (Fin 2 → F)) (g : J) :
    (matrixHom τ g).det = 1 := by
  let d := (Matrix.detMonoidHom.comp (matrixHom τ)).toHomUnits
  let : Group.IsPerfect d.range := Group.IsPerfect.range d
  have h : d.rangeRestrict g = 1 := Subsingleton.elim _ _
  exact congrArg (fun z : d.range => (z.val : F)) h

private def toSL (τ : Representation F J (Fin 2 → F)) : J →* SL(2,F) where
  toFun g := ⟨matrixHom τ g, matrixHom_det τ g⟩
  map_one' := Subtype.ext (matrixHom τ).map_one
  map_mul' g h := Subtype.ext ((matrixHom τ).map_mul g h)

private theorem toSL_mulVec (τ : Representation F J (Fin 2 → F)) (g : J) (v : Fin 2 → F) :
    (toSL τ g).val.mulVec v = τ g v := by
  exact congrArg (fun f : Module.End F (Fin 2 → F) => f v)
    (LinearMap.toMatrixAlgEquiv'.symm_apply_apply (τ g))

private def factorEquiv [Finite J] (e : J ≃* SL(2,F))
    (τ : Representation F J (Fin 2 → F)) (hτ : Function.Injective τ) : J ≃* SL(2,F) := by
  have hi : Function.Injective (toSL τ) := by
    intro g h hh
    apply hτ
    apply LinearMap.toMatrixAlgEquiv'.injective
    exact congrArg Subtype.val hh
  have hs : Function.Surjective (toSL τ) := by
    let : Finite SL(2,F) := Finite.of_equiv J e.toEquiv
    have h := Finite.surjective_of_injective (hi.comp e.symm.injective)
    exact fun g => by obtain ⟨x,hx⟩ := h g; exact ⟨e.symm x,hx⟩
  exact MulEquiv.ofBijective (toSL τ) ⟨hi,hs⟩

private def dual : SL(2,F) ≃* SL(2,F) where
  toFun g := g⁻¹.transpose
  invFun g := g⁻¹.transpose
  left_inv g := by
    apply Subtype.ext
    change (g.val.adjugate.transpose).adjugate.transpose = g.val
    rw [← Matrix.adjugate_transpose, Matrix.transpose_transpose,
      Matrix.adjugate_adjugate _ (by simp), g.det_coe]
    simp
  right_inv g := by
    apply Subtype.ext
    change (g.val.adjugate.transpose).adjugate.transpose = g.val
    rw [← Matrix.adjugate_transpose, Matrix.transpose_transpose,
      Matrix.adjugate_adjugate _ (by simp), g.det_coe]
    simp
  map_mul' g h := by
    apply Subtype.ext
    change ((g*h)⁻¹).val.transpose = (g⁻¹).val.transpose * (h⁻¹).val.transpose
    rw [_root_.mul_inv_rev]
    exact Matrix.transpose_mul _ _

private theorem dual_inv_val (g : SL(2,F)) : (dual g)⁻¹.val = g.val.transpose := by
  change (g.val.adjugate.transpose).adjugate = g.val.transpose
  rw [← Matrix.adjugate_transpose, Matrix.adjugate_adjugate _ (by simp), g.det_coe]
  simp

private def tensorCoordinates : ((Fin 2 → F) ⊗[F] (Fin 2 → F)) ≃ₗ[F] Mat (F := F) :=
  (TensorProduct.comm F (Fin 2 → F) (Fin 2 → F)).trans
    (TensorProduct.piScalarRight F F (Fin 2 → F) (Fin 2))

private theorem tensorCoordinates_tmul (x y : Fin 2 → F) :
    tensorCoordinates (x ⊗ₜ[F] y) = Matrix.vecMulVec x y := by
  ext i j
  change (TensorProduct.piScalarRight F F (Fin 2 → F) (Fin 2))
    (y ⊗ₜ[F] x) i j = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

private def pairEquiv [Finite J] (e : J ≃* SL(2,F))
    (τ₁ τ₂ : Representation F J (Fin 2 → F))
    (h₁ : Function.Injective τ₁) (h₂ : Function.Injective τ₂) :
    J × J ≃* PairSL (F := F) :=
  (factorEquiv e τ₁ h₁).prodCongr ((factorEquiv e τ₂ h₂).trans dual)

private def tensorEquiv [Finite J] (e : J ≃* SL(2,F))
    (τ₁ τ₂ : Representation F J (Fin 2 → F))
    (h₁ : Function.Injective τ₁) (h₂ : Function.Injective τ₂) :
    (QuadraticFourGroup.TensorClassification.externalTensor τ₁ τ₂).Equiv
      (representation.comp (pairEquiv e τ₁ τ₂ h₁ h₂).toMonoidHom) := by
  refine Representation.Equiv.mk tensorCoordinates ?_
  intro g
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simpa only [map_add] using congrArg₂ (· + ·) hu hv
  | tmul x y =>
    change tensorCoordinates (τ₁ g.1 x ⊗ₜ[F] τ₂ g.2 y) =
      representation (pairEquiv e τ₁ τ₂ h₁ h₂ g) (tensorCoordinates (x ⊗ₜ[F] y))
    rw [tensorCoordinates_tmul, tensorCoordinates_tmul, representation_apply]
    change _ = (toSL τ₁ g.1).val * Matrix.vecMulVec x y * (dual (toSL τ₂ g.2))⁻¹.val
    rw [dual_inv_val, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [toSL_mulVec, Matrix.vecMul_transpose, toSL_mulVec]

end ClassicalOrthogonal.FourPlusMatrix.TensorRecognition

namespace ClassicalOrthogonal.FourPlusMatrix.TensorRecognition
variable {F K : Type*} [Field F] [Field K]

private def slFieldEquiv (e : F ≃+* K) : SL(2,F) ≃* SL(2,K) where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by ext i j; exact e.symm_apply_apply (g.val i j)
  right_inv g := by ext i j; exact e.apply_symm_apply (g.val i j)
  map_mul' := (SpecialLinearGroup.map e.toRingHom).map_mul

variable [Algebra (ZMod 2) F] [Algebra (ZMod 2) K]

private def binaryMatrixMap (e : F ≃+* K) : Mat (F := F) ≃ₗ[ZMod 2] Mat (F := K) :=
  let a := e.mapMatrix.toAddEquiv
  LinearEquiv.ofBijective (a.toAddMonoidHom.toZModLinearMap 2) a.bijective

private def binaryChangeFieldEquiv (e : F ≃+* K) :
    (restrictScalars (k := ZMod 2) (representation (F := F))).Equiv
      ((restrictScalars (k := ZMod 2) (representation (F := K))).comp
        ((slFieldEquiv e).prodCongr (slFieldEquiv e)).toMonoidHom) := by
  refine Representation.Equiv.mk (binaryMatrixMap e) ?_
  intro g
  apply LinearMap.ext
  intro v
  change (g.1.val * v * g.2⁻¹.val).map e =
    (slFieldEquiv e g.1).val * v.map e * (slFieldEquiv e g.2)⁻¹.val
  rw [Matrix.map_mul, Matrix.map_mul]
  change _ = g.1.val.map e * v.map e * (slFieldEquiv e g.2)⁻¹.val
  rw [← map_inv]
  rfl

variable {J : Type*} [Group J] [Group.IsPerfect J] [Finite J]

private def binaryTensorEquiv (e : J ≃* SL(2,F))
    (τ₁ τ₂ : Representation F J (Fin 2 → F))
    (h₁ : Function.Injective τ₁) (h₂ : Function.Injective τ₂) :
    (restrictScalars (k := ZMod 2)
      (QuadraticFourGroup.TensorClassification.externalTensor τ₁ τ₂)).Equiv
      ((restrictScalars (k := ZMod 2) (representation (F := F))).comp
        (pairEquiv e τ₁ τ₂ h₁ h₂).toMonoidHom) := by
  let φ := tensorEquiv e τ₁ τ₂ h₁ h₂
  refine Representation.Equiv.mk (φ.toLinearEquiv.restrictScalars (ZMod 2)) ?_
  intro g
  apply LinearMap.ext
  intro v
  exact Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v

end ClassicalOrthogonal.FourPlusMatrix.TensorRecognition

namespace ClassicalOrthogonal.FourPlusMatrix.TensorRecognition
open QuadraticFourGroup QuadraticFourGroup.TensorClassification
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Group.IsPerfect (Factor 2)]

/-- Cubic fixed-point-free factors in an irreducible binary product action
recognize the exact determinant model, with both factor markings retained. -/
theorem exists_binary_determinant_equiv
    (σ : Representation (ZMod 2) (Factor 2 × Factor 2) V) [σ.IsIrreducible]
    (h : CubicFreeOnFactors σ) :
    ∃ j₁ j₂ : Factor 2 ≃* SL(2,Binary.F),
      Nonempty (σ.Equiv (Binary.action.comp (j₁.prodCongr j₂).toMonoidHom)) := by
  obtain ⟨τ₁,τ₂,h₁,h₂,⟨a⟩⟩ :=
    isNaturalTensorAlong_of_cubicFreeOnFactors σ (by decide) h
  let e := (specialLinearEquivFactor 2).symm
  let f := Representation.SL2FourNatural.fieldEquiv.symm
  let j₁ := (factorEquiv e τ₁ h₁).trans (slFieldEquiv f)
  let j₂ := ((factorEquiv e τ₂ h₂).trans dual).trans (slFieldEquiv f)
  let b := binaryTensorEquiv e τ₁ τ₂ h₁ h₂
  let c := binaryChangeFieldEquiv f
  let d : Representation.Equiv
      ((restrictScalars (k := ZMod 2) (representation (F := GaloisField 2 2))).comp
        (pairEquiv e τ₁ τ₂ h₁ h₂).toMonoidHom)
        (Binary.action.comp (j₁.prodCongr j₂).toMonoidHom) := by
    refine Representation.Equiv.mk c.toLinearEquiv ?_
    intro g
    apply LinearMap.ext
    intro v
    exact Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap
      (pairEquiv e τ₁ τ₂ h₁ h₂ g) v
  exact ⟨j₁,j₂,⟨a.trans (b.trans d)⟩⟩

end ClassicalOrthogonal.FourPlusMatrix.TensorRecognition

