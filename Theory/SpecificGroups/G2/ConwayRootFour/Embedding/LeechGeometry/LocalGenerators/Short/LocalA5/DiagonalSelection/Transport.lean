module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.DiagonalSelection.Relations
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.DiagonalSelection.Certificate
/-!
# Transporting the order-seventeen word to octonion coordinates

The matrix map on linear automorphisms identifies the literal octonion block
and graph actions, and the pair (upper shear, lower shear), with the checked
matrices. Mapping coefficients along any embedding of GoldenFour preserves
the word and its powers. Injectivity then gives order seventeen for the square
of the coordinate word. The parent module constructs its actual Leech lift
and applies the ambient order obstruction.

Source: Aschbacher, Sporadic Groups (1994), Lemma 49.5, p.284. This is the
ambient repair of the diagonal-selection inference, with the natural and dual
coordinate permutations preserved explicitly.
-/

open Matrix Atlas.Algebra
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.DiagonalSelection
open OctonionLocals
open PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
@[expose] public noncomputable section
variable {R : Type*} [Field R] [CharP R 2]

def matrixOf : (Six R ≃ₗ[R] Six R) →* Matrix (Fin 6) (Fin 6) R where
  toFun a := LinearMap.toMatrix' a.toLinearMap
  map_one' := LinearMap.toMatrix'_one
  map_mul' a b := LinearMap.toMatrix'_mul a.toLinearMap b.toLinearMap

omit [CharP R 2] in
theorem matrixOf_injective : Function.Injective (matrixOf (R := R)) := by
  intro a b h
  exact LinearEquiv.toLinearMap_injective (LinearMap.toMatrix'.injective h)

theorem matrixOf_block (A : SL(3,R)) :
    matrixOf (action (BlockRealization.blockHom A)) = Certificate.blockMatrix A.val := by
  ext i j
  change action (BlockRealization.blockHom A) (Pi.single j 1) i = _
  rw [action_block]
  fin_cases i <;> fin_cases j <;>
    simp [Certificate.blockMatrix, BlockRealization.cofactor,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

omit [CharP R 2] in
theorem blockMatrix_map (e : K →+* R) (A : Matrix (Fin 3) (Fin 3) K) :
    Certificate.blockMatrix (A.map e) = (Certificate.blockMatrix A).map e := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Certificate.blockMatrix, Matrix.adjugate_fin_three, Matrix.map_apply]

omit [CharP R 2] in
theorem matrixOf_bad (e : K →+* R) :
    matrixOf (pairRepresentation (shear, lowerShear)) = Certificate.bad.map e := by
  ext i j
  change pairAction (shear, lowerShear) (Pi.single j 1) i = _
  fin_cases i <;> fin_cases j <;>
    simp [pairAction, shear, lowerShear, Certificate.bad, Matrix.map_apply]

theorem matrixOf_graph (e : K →+* R) :
    matrixOf (action (graph : Model R)) = Certificate.graphMatrix.map e := by
  ext i j
  change action graph (Pi.single j 1) i = _
  rw [action_graph]
  fin_cases i <;> fin_cases j <;>
    simp [Certificate.graphMatrix, Matrix.map_apply]

def coordinateWord (e : K →+* R) : Six R ≃ₗ[R] Six R :=
  let b := pairRepresentation (shear, lowerShear)
  let g := action (graph : Model R)
  let block (A : SL(3,K)) := action (BlockRealization.blockHom
    (Matrix.SpecialLinearGroup.map e A))
  (b*g*block Certificate.A0) * (b*g*block Certificate.A1) *
    (b*g*block Certificate.A2) * (b*g*block Certificate.A3)

theorem coordinateWord_matrix (e : K →+* R) :
    matrixOf (coordinateWord e) = Certificate.word.map e := by
  unfold coordinateWord
  simp only [map_mul, matrixOf_bad e, matrixOf_graph e, matrixOf_block]
  change (Certificate.bad.map e * Certificate.graphMatrix.map e *
      Certificate.blockMatrix (Certificate.A0.val.map e)) *
    (Certificate.bad.map e * Certificate.graphMatrix.map e *
      Certificate.blockMatrix (Certificate.A1.val.map e)) *
    (Certificate.bad.map e * Certificate.graphMatrix.map e *
      Certificate.blockMatrix (Certificate.A2.val.map e)) *
    (Certificate.bad.map e * Certificate.graphMatrix.map e *
      Certificate.blockMatrix (Certificate.A3.val.map e)) = _
  rw [blockMatrix_map, blockMatrix_map, blockMatrix_map, blockMatrix_map,
    Certificate.block0, Certificate.block1, Certificate.block2, Certificate.block3]
  simp only [Certificate.word, Matrix.map_mul]

theorem coordinateWord_square_matrix (e : K →+* R) :
    matrixOf (coordinateWord e ^ 2) = Certificate.Q.map e := by
  rw [map_pow, coordinateWord_matrix]
  exact (map_pow (e.mapMatrix : Matrix (Fin 6) (Fin 6) K →+* Matrix (Fin 6) (Fin 6) R)
    Certificate.word 2).symm.trans (congrArg (Matrix.map · e) Certificate.word_square)

theorem coordinateWord_order (e : K →+* R) : orderOf (coordinateWord e ^ 2) = 17 := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply matrixOf_injective
    rw [map_pow, map_one, coordinateWord_square_matrix]
    change (e.mapMatrix Certificate.Q) ^ 17 = 1
    rw [← map_pow, Certificate.Q_pow, map_one]
  · intro h
    have hm := congrArg matrixOf h
    rw [coordinateWord_square_matrix, map_one] at hm
    apply Certificate.nonidentity
    apply Matrix.ext
    intro i j
    apply e.injective
    have hh := congrFun (congrFun hm i) j
    simpa only [Matrix.map_apply, Matrix.one_apply, apply_ite, map_one, map_zero] using hh
end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.DiagonalSelection
