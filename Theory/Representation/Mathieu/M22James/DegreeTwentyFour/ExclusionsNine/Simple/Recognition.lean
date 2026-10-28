module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Simple.WordReduction
public import Theory.Representation.SL3.BinaryFieldDescent
public import Theory.Representation.SL3.BinaryFieldDescent.Fields
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange
public import Theory.Representation.SL3.BinaryDefiningFactors.SmallPatterns

/-!
# Binary recognition of the mixed nine-dimensional point models

Every irreducible binary representation of SL₃(4) of dimension eighteen
satisfying the central quadratic relation is equivalent to one of the two
concrete mixed tensor models. The input need not be absolutely irreducible.

The tensor coordinates send x ⊗ y to the vector with coordinate xᵢyₖ at
3*i+k. The dot-product pairing identifies inverse-transpose coordinates with
the genuine dual. These maps, together with Frobenius compatibility, identify
the scalar extension of each matrix model with its actual mixed tensor word.
The Schur degree is two, so a compatible isomorphism of the actual Schur field
with F₄ lets us descend the absolute word equivalence and restrict it to F₂.

The final theorem discharges the recognition premise of
`simplePointExtensionExclusion_of_recognition` in the parent Simple assembly.

Source: GLS III, 2.8.6, Remark 2.8.8 and 2.8.10(c); Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, pp.15–16. The point-subgroup
context is Aschbacher–Smith H.12.1, printed pp.393–394.
-/

public noncomputable section
open Representation Matrix
open scoped TensorProduct Kronecker
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3FourLocalCatalogue
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine.Simple
universe u
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

private def flattenCoordinates : (Fin 3 → Fin 3 → K) ≃ₗ[K] (Fin 9 → K) where
  toFun X r := X ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm r).1
    ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm r).2
  invFun v i j := v (finProdFinEquiv (i, j))
  left_inv X := by funext i j; simp
  right_inv v := by funext r; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def tensorCoordinates : ((Fin 3 → K) ⊗[K] (Fin 3 → K)) ≃ₗ[K] (Fin 9 → K) :=
  ((_root_.TensorProduct.comm K _ _).trans
    (TensorProduct.piScalarRight K K (Fin 3 → K) (Fin 3))).trans flattenCoordinates

private lemma tensorCoordinates_tmul (x y : Fin 3 → K) (r : Fin 9) :
    tensorCoordinates (x ⊗ₜ[K] y) r =
      x ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm r).1 *
        y ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm r).2 := by
  change (TensorProduct.piScalarRight K K (Fin 3 → K) (Fin 3))
    (y ⊗ₜ[K] x) ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm r).1
      ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm r).2 = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

private lemma tensorCoordinates_action (A B : Matrix (Fin 3) (Fin 3) K)
    (x y : Fin 3 → K) :
    tensorCoordinates (A.mulVec x ⊗ₜ[K] B.mulVec y) =
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)).mulVec
        (tensorCoordinates (x ⊗ₜ[K] y)) := by
  ext r
  rw [tensorCoordinates_tmul]
  simp only [Matrix.mulVec, dotProduct]
  rw [← (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).sum_comp]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    tensorCoordinates_tmul, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private def mappedMatrixRep {n : ℕ} (ι : F →+* K)
    (A : SL →* Matrix (Fin n) (Fin n) F) : Representation K SL (Fin n → K) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (ι.mapMatrix.toMonoidHom.comp A)

private def coordinateFactor (ι : F →+* K) (b : Bool) :=
  mappedMatrixRep ι (firstFactorMatrix b)

private def dualCoordinateEquiv (ι : F →+* K) :
    (coordinateFactor ι false).Equiv (natural ι).dual :=
  .mk (dotProductEquiv K (Fin 3)) (by
    intro g
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro v
    change (((g⁻¹).val.transpose.map ι).mulVec w) ⬝ᵥ v =
      w ⬝ᵥ ((g⁻¹).val.map ι).mulVec v
    exact (dotProduct_comm _ _).trans
      (Matrix.dotProduct_transpose_mulVec ((g⁻¹).val.map ι) v w))

private def naturalCoordinateEquiv (ι : F →+* K) :
    (coordinateFactor ι true).Equiv (natural ι) :=
  .mk (LinearEquiv.refl _ _) (by intro g; rfl)

private def tensorCoordinateEquiv (ι : F →+* K) (b : Bool) :
    ((mappedMatrixRep ι (firstFactorMatrix b)).tprod
      (mappedMatrixRep ι (secondFactorMatrix b))).Equiv
      (mappedMatrixRep ι (mixedMatrix b)) :=
  .mk tensorCoordinates (by
    intro g
    apply TensorProduct.ext'
    intro x y
    change tensorCoordinates
      (((firstFactorMatrix b g).map ι).mulVec x ⊗ₜ[K]
        ((secondFactorMatrix b g).map ι).mulVec y) =
      ((mixedMatrix b g).map ι).mulVec (tensorCoordinates (x ⊗ₜ[K] y))
    rw [tensorCoordinates_action]
    congr 1
    ext r c
    simp [mixedMatrix_apply, Matrix.reindex_apply])

private def matrixBaseChange [Algebra F K] {n : ℕ}
    (A : SL →* Matrix (Fin n) (Fin n) F) :
    (extendScalars K (Matrix.toLinAlgEquiv'.toMonoidHom.comp A)).Equiv
      (mappedMatrixRep (algebraMap F K) A) :=
  .mk (TensorProduct.piScalarRight F K K (Fin n)) (by
    intro g
    ext v i
    change (TensorProduct.piScalarRight F K K (Fin n))
      ((1 : K) ⊗ₜ[F] ((A g).mulVec (Pi.single v 1))) i =
      ((A g).map (algebraMap F K)).mulVec
        (TensorProduct.piScalarRight F K K (Fin n) ((1 : K) ⊗ₜ[F] Pi.single v 1)) i
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Algebra.smul_def, mul_one]
    simp [Matrix.mulVec, dotProduct])

private def secondCoordinateEquiv [CharP K 2] (ι : F →+* K) (b : Bool) :
    (mappedMatrixRep ι (secondFactorMatrix b)).Equiv
      (coordinateFactor ((frobenius K 2).comp ι) (!b)) :=
  .mk (LinearEquiv.refl _ _) (by
    intro g
    change Matrix.toLin' ((secondFactorMatrix b g).map ι) =
      Matrix.toLin' ((firstFactorMatrix (!b) g).map ((frobenius K 2).comp ι))
    congr 1
    ext i j
    exact map_pow ι (firstFactorMatrix (!b) g i j) 2)

private def mixedWordCoordinates [CharP K 2] (ι : F →+* K) (b : Bool) :
    (mappedMatrixRep ι (mixedMatrix b)).Equiv (wordRep ι (mixedWord b)) := by
  cases b
  · exact (tensorCoordinateEquiv ι false).symm.trans
      ((BinaryFieldDescent.tensorEquiv (dualCoordinateEquiv ι)
        ((secondCoordinateEquiv ι false).trans
          (naturalCoordinateEquiv ((frobenius K 2).comp ι)))).trans
        (tensorRightEquiv (Representation.TensorProduct.rid K
          (natural ((frobenius K 2).comp ι))).symm))
  · exact (tensorCoordinateEquiv ι true).symm.trans
      ((BinaryFieldDescent.tensorEquiv (naturalCoordinateEquiv ι)
        ((secondCoordinateEquiv ι true).trans
          (dualCoordinateEquiv ((frobenius K 2).comp ι)))).trans
        (tensorRightEquiv (Representation.TensorProduct.rid K
          (natural ((frobenius K 2).comp ι)).dual).symm))

/-- Scalar extension of the literal nine-coordinate action is its mixed word. -/
def mixedBaseChange [Algebra F K] [CharP K 2] (b : Bool) :
    (extendScalars K (mixedFieldRep b)).Equiv
      (wordRep (algebraMap F K) (mixedWord b)) :=
  (matrixBaseChange (mixedMatrix b)).trans (mixedWordCoordinates (algebraMap F K) b)

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  (σ : Representation (ZMod 2) SL U) [IsIrreducible σ]

open Representation.BinaryFieldDescent
private theorem descend_absolute_mixed
    (hs : Representation.schurDegree 2 σ = 2)
    (h : ∃ (ι : F →+* SplittingField σ) (b : Bool),
      Nonempty ((extendScalars (SplittingField σ) σ.endFieldRep).Equiv
        (wordRep ι (mixedWord b)))) :
    ∃ b : Bool, Nonempty (σ.Equiv (mixedBinaryRep b)) := by
  obtain ⟨ι, b, ⟨ea⟩⟩ := h
  let : Algebra F (SplittingField σ) := ι.toAlgebra
  have hcard : Nat.card F = Nat.card (SchurField σ) := by
    let : Module.Finite (ZMod 2) (SchurField σ) := Module.Finite.of_finite
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := SchurField σ)
    change Nat.card (SchurField σ) = Nat.card (ZMod 2) ^ Representation.schurDegree 2 σ at he
    rw [he, hs, Nat.card_zmod, Nat.card_eq_fintype_card]
    decide
  obtain ⟨e, he⟩ := FiniteField.exists_compatible_equiv_of_card_eq
    (algebraMap (SchurField σ) (SplittingField σ)) ι hcard
  let := scalarModule σ e
  let : Finite U := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) U)
  let : Module.Finite F U := Module.Finite.of_finite
  let τ := scalarRep σ e
  let eS := scalarExtensionEquiv σ e he
  let eM := mixedBaseChange (K := SplittingField σ) b
  obtain ⟨ed⟩ := equiv_of_extendScalars (K := SplittingField σ) τ
    (mixedFieldRep b) ⟨eS.symm.trans (ea.trans eM.symm)⟩
  refine ⟨b, ?_⟩
  have eb := restrictBinaryEquiv ed
  simpa only [τ, restrict_scalarRep, mixedBinaryRep] using Nonempty.intro eb

/-- Every irreducible binary degree-eighteen action with the central quadratic
relation is one of the two literal mixed tensor models. -/
theorem simplePointRecognition : SimplePointRecognition.{u} := by
  intro V _ _ _ τ hq hi hd
  let : IsIrreducible τ := hi
  exact descend_absolute_mixed τ
    (PointConstituents.schurDegree_eq_two_and_finrank_cases τ hq (by omega)).1
    (exists_absolute_mixed_equiv τ hq hd)

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine.Simple
