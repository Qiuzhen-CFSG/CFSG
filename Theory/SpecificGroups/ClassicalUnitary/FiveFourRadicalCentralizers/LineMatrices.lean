module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers.Reduction

/-!
# Matrix commutant of the unitary-five line radical

Over a field of characteristic two with a supplied trace-one scalar, every
matrix commuting with the concrete line radical is a scalar matrix plus a
multiple of its central rank-one nilpotent.

In the Witt basis, commutation with the coordinate `(0,1)` first controls the
first column and last row. Lifts of the three coordinate vectors force the
middle block to be scalar. Comparing these lifts with their trace-one scalar
multiples kills the remaining first-row and last-column entries. Conjugating
back gives exactly `lineCentralMatrix`.

This is the elementary linear algebra input to the unitary parabolic
calculation underlying Aschbacher--Smith, *The Classification of Quasithin
Groups*, F.1.12(7), printed pp.263--264 of `refs/quasithin.pdf`.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.RadicalCentralizers
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

private def upperCentralMatrix (a b : F) : Matrix (Fin 5) (Fin 5) F :=
  !![a,0,0,0,b; 0,a,0,0,0; 0,0,a,0,0; 0,0,0,a,0; 0,0,0,0,a]

private theorem upper_shape (c : F) (hc : c + J.conj c = 1)
    (B : Matrix (Fin 5) (Fin 5) F)
    (hcomm : ∀ u : LineCore.Coord J,
      B * LineCore.unipotentMatrix J u = LineCore.unipotentMatrix J u * B) :
    ∃ a b : F, B = upperCentralMatrix a b := by
  -- The central transvection leaves only an upper block triangular shape.
  let z : LineCore.Coord J := ⟨0, 1, by simpa using (CharTwo.add_self_eq_zero (1 : F))⟩
  have hz (i j : Fin 5) := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j) (hcomm z)
  have h10 : B 1 0 = 0 := by
    have h := hz 1 4
    simp [LineCore.unipotentMatrix, z, Matrix.mul_apply, Fin.sum_univ_succ] at h
    linear_combination h
  have h20 : B 2 0 = 0 := by
    have h := hz 2 4
    simp [LineCore.unipotentMatrix, z, Matrix.mul_apply, Fin.sum_univ_succ] at h
    linear_combination h
  have h30 : B 3 0 = 0 := by
    have h := hz 3 4
    simp [LineCore.unipotentMatrix, z, Matrix.mul_apply, Fin.sum_univ_succ] at h
    linear_combination h
  have h40 : B 4 0 = 0 := by
    have h := hz 0 0
    simp [LineCore.unipotentMatrix, z, Matrix.mul_apply, Fin.sum_univ_succ] at h
    exact h
  have h41 : B 4 1 = 0 := by
    have h := hz 0 1
    simp [LineCore.unipotentMatrix, z, Matrix.mul_apply, Fin.sum_univ_succ] at h
    exact h
  have h42 : B 4 2 = 0 := by
    have h := hz 0 2
    simp [LineCore.unipotentMatrix, z, Matrix.mul_apply, Fin.sum_univ_succ] at h
    exact h
  have h43 : B 4 3 = 0 := by
    have h := hz 0 3
    simp [LineCore.unipotentMatrix, z, Matrix.mul_apply, Fin.sum_univ_succ] at h
    exact h
  have h44 : B 0 0 = B 4 4 := by
    have h := hz 0 4
    simp [LineCore.unipotentMatrix, z, Matrix.mul_apply, Fin.sum_univ_succ] at h
    linear_combination h
  -- Unit coordinate vectors determine all nine entries of the middle block.
  let u (k : Fin 3) (t : F) := LineCore.Coord.liftVector c hc (Pi.single k t)
  have hu (k : Fin 3) (t : F) (i j : Fin 5) :=
    congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j) (hcomm (u k t))
  have h11 : B 1 1 = B 4 4 := by
    have h := hu 0 1 1 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ, h10] at h
    linear_combination h
  have h21 : B 2 1 = 0 := by
    have h := hu 0 1 2 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ, h20] at h
    linear_combination h
  have h31 : B 3 1 = 0 := by
    have h := hu 0 1 3 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ, h30] at h
    linear_combination h
  have h12 : B 1 2 = 0 := by
    have h := hu 1 1 1 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ, h10] at h
    linear_combination h
  have h22 : B 2 2 = B 4 4 := by
    have h := hu 1 1 2 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ, h20] at h
    linear_combination h
  have h32 : B 3 2 = 0 := by
    have h := hu 1 1 3 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ, h30] at h
    linear_combination h
  have h13 : B 1 3 = 0 := by
    have h := hu 2 1 1 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ, h10] at h
    linear_combination h
  have h23 : B 2 3 = 0 := by
    have h := hu 2 1 2 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ, h20] at h
    linear_combination h
  have h33 : B 3 3 = B 4 4 := by
    have h := hu 2 1 3 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ, h30] at h
    linear_combination h
  -- The vectors eᵢ and c eᵢ, together with trace(c) = 1, kill the two wings.
  have h01 : B 0 1 = B 1 4 := by
    have h := hu 0 1 0 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ] at h
    linear_combination h - c * h44
  have h01zero : B 0 1 = 0 := by
    have h := hu 0 c 0 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ] at h
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h - (c * (J.conj c * c)) * h44 - J.conj c * h01 -
      B 0 1 * hc + (J.conj c * B 0 1) * htwo
  have h14 : B 1 4 = 0 := h01.symm.trans h01zero
  have h02 : B 0 2 = B 2 4 := by
    have h := hu 1 1 0 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ] at h
    linear_combination h - c * h44
  have h02zero : B 0 2 = 0 := by
    have h := hu 1 c 0 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ] at h
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h - (c * (J.conj c * c)) * h44 - J.conj c * h02 -
      B 0 2 * hc + (J.conj c * B 0 2) * htwo
  have h24 : B 2 4 = 0 := h02.symm.trans h02zero
  have h03 : B 0 3 = B 3 4 := by
    have h := hu 2 1 0 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ] at h
    linear_combination h - c * h44
  have h03zero : B 0 3 = 0 := by
    have h := hu 2 c 0 4
    simp [u, LineCore.Coord.liftVector, LineCore.unipotentMatrix,
      LineCore.pairing, Matrix.mul_apply, Fin.sum_univ_succ] at h
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h - (c * (J.conj c * c)) * h44 - J.conj c * h03 -
      B 0 3 * hc + (J.conj c * B 0 3) * htwo
  have h34 : B 3 4 = 0 := h03.symm.trans h03zero
  refine ⟨B 0 0, B 0 4, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperCentralMatrix, h10, h20, h30, h40, h41, h42, h43, h44,
      h11, h21, h31, h12, h22, h32, h13, h23, h33,
      h01zero, h02zero, h03zero, h14, h24, h34]

/-- The matrix commutant of the line radical is spanned by the identity and
its central rank-one nilpotent. -/
theorem line_matrix_shape (c : F) (hc : c + J.conj c = 1)
    (A : Matrix (Fin 5) (Fin 5) F)
    (hA : ∀ v : LineCore.Coord J,
      A * LineCore.Parabolic.ambientMatrix J v =
        LineCore.Parabolic.ambientMatrix J v * A) :
    ∃ a b : F, A = lineCentralMatrix a b := by
  let W := LineCore.wittBasisMatrix (0 : F)
  let Wi := LineCore.wittBasisInverse (0 : F)
  let B := Wi * A * W
  have hWiW : Wi * W = 1 := LineCore.wittBasis_inverse_mul 0
  have hWWi : W * Wi = 1 := LineCore.wittBasis_mul_inverse 0
  have hW (u : LineCore.Coord J) :
      W * LineCore.unipotentMatrix J u =
        LineCore.Parabolic.ambientMatrix J u * W := by
    calc
      W * LineCore.unipotentMatrix J u =
          W * LineCore.unipotentMatrix J u * (Wi * W) := by rw [hWiW, mul_one]
      _ = (W * LineCore.unipotentMatrix J u * Wi) * W := by
            simp only [Matrix.mul_assoc]
      _ = LineCore.Parabolic.ambientMatrix J u * W := by
            rw [← LineCore.Parabolic.ambientMatrix_eq J 0 u]
  have hcomm (u : LineCore.Coord J) :
      B * LineCore.unipotentMatrix J u =
        LineCore.unipotentMatrix J u * B := by
    calc
      B * LineCore.unipotentMatrix J u =
          Wi * A * (W * LineCore.unipotentMatrix J u) := by
            dsimp [B]
            simp only [Matrix.mul_assoc]
      _ = Wi * (A * LineCore.Parabolic.ambientMatrix J u) * W := by
            rw [hW u]
            simp only [Matrix.mul_assoc]
      _ = Wi * (LineCore.Parabolic.ambientMatrix J u * A) * W := by rw [hA u]
      _ = LineCore.unipotentMatrix J u * B := by
            rw [LineCore.Parabolic.ambientMatrix_eq J 0 u]
            dsimp [B]
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc, hWiW, one_mul]
  obtain ⟨a, b, hB⟩ := upper_shape J c hc B hcomm
  refine ⟨a, b, ?_⟩
  calc
    A = (W * Wi) * A * (W * Wi) := by rw [hWWi, one_mul, mul_one]
    _ = W * B * Wi := by dsimp [B]; simp only [Matrix.mul_assoc]
    _ = W * upperCentralMatrix a b * Wi := by rw [hB]
    _ = lineCentralMatrix a b := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [W, Wi, upperCentralMatrix, LineCore.wittBasisMatrix,
          LineCore.wittBasisInverse, lineCentralMatrix, Matrix.mul_apply,
          Fin.sum_univ_succ]
      all_goals ring_nf
      all_goals simp [CharTwo.two_eq_zero]

end Theory.SpecificGroups.UnitaryFive.RadicalCentralizers
