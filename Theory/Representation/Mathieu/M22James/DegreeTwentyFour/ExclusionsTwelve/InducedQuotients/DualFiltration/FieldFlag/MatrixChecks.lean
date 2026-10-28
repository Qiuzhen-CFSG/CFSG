module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.Action
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.FieldFlag.Certificates
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.FieldFlag.Blocks

/-!
# Certified adapted basis for the dual induced action

Kernel-checked packed column identities prove that B is invertible and
B times each adapted action equals the actual ambient action times B.
Bounds on the packed columns certify the invariant prefixes of dimensions
45 and 51. The three diagonal blocks are compared with the published
factor matrices, retaining all off-diagonal blocks.
Source context: Guralnick–Malle I, Proposition 5.1, pp.15–16 and
Theorem 6.6/Table 6.7. See `../source/README.md` for the candidate data.
-/

@[expose] public noncomputable section


namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FieldFlag
open Packed
lemma basis_mul_inverse : basisMatrix * basisInverse = 1 := by
  apply Matrix.ext
  intro i j
  have h := congrArg (fun r => decode r i) (packed_inverse j)
  rw [decode_combine, decode_single] at h
  simpa only [basis_decode, inverse_decode, Matrix.mul_apply, Matrix.one_apply, Fin.val_inj] using h
lemma inverse_mul_basis : basisInverse * basisMatrix = 1 :=
  (mul_eq_one_comm (a := basisMatrix) (b := basisInverse)).mp basis_mul_inverse
lemma basis_mul_adapted (a : Fin 2) : basisMatrix * adaptedMatrix a = ambientMatrix a * basisMatrix := by
  apply Matrix.ext
  intro i j
  have h := congrArg (fun r => decode r i) (packed_action a j)
  simp only [decode_combine, basis_decode, adapted_decode, ambient_decode] at h
  exact h
/-- Adapt the actual slot coordinates by the certified inverse matrix. -/
def basisCoordinates : Space ≃ₗ[F] (Fin 66 → F) :=
  flatten.trans {
    (basisInverse).mulVecLin with
    invFun := (basisMatrix).mulVec
    left_inv := fun v => by
      change basisMatrix.mulVec (basisInverse.mulVec v) = v
      rw [Matrix.mulVec_mulVec, basis_mul_inverse, Matrix.one_mulVec]
    right_inv := fun v => by
      change basisInverse.mulVec (basisMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, inverse_mul_basis, Matrix.one_mulVec] }
lemma flatten_basisCoordinates_symm (v : Fin 66 → F) :
    flatten (basisCoordinates.symm v) = basisMatrix.mulVec v := by
  simp only [basisCoordinates, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  exact flatten.apply_symm_apply _
lemma basisCoordinates_generator (a : Fin 2) (v : Space) :
    basisCoordinates (fieldRepresentation .dual (Uniqueness.PointRestriction.PointModel.ambientGenerator a) v) =
      (adaptedMatrix a).mulVec (basisCoordinates v) := by
  have h : basisMatrix.mulVec (basisCoordinates v) = flatten v := by
    change basisMatrix.mulVec (basisInverse.mulVec (flatten v)) = flatten v
    rw [Matrix.mulVec_mulVec, basis_mul_inverse, Matrix.one_mulVec]
  have hinj : Function.Injective basisMatrix.mulVec := by
    intro x y hxy
    have heq := congrArg basisInverse.mulVec hxy
    simpa only [Matrix.mulVec_mulVec, inverse_mul_basis, Matrix.one_mulVec] using heq
  apply hinj
  change basisMatrix.mulVec (basisInverse.mulVec (flatten
      (fieldRepresentation .dual (Uniqueness.PointRestriction.PointModel.ambientGenerator a) v))) = _
  rw [Matrix.mulVec_mulVec, basis_mul_inverse, Matrix.one_mulVec,
      generator_coordinates, Matrix.mulVec_mulVec, basis_mul_adapted,
      ← Matrix.mulVec_mulVec, h]
lemma upper (m : ℕ) (a : Fin 2) (i j : Fin 66)
    (hi : cut m ≤ i.val) (hj : j.val < cut m) : adaptedMatrix a i j = 0 := by
  by_cases hm : m < 3
  · have h : adaptedColumns a j < 2^(2*cut m) := packed_upper ⟨m,hm⟩ a j hj
    have h₀ : adaptedColumns a j < 2^(2*i.val) :=
      h.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have h₁ : adaptedColumns a j < 2^(2*i.val+1) :=
      h.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    change entry (adaptedColumns a j) i = 0
    simp only [entry, Nat.testBit_lt_two_pow h₀, Nat.testBit_lt_two_pow h₁,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  · have hc : cut m = 66 := by
      match m with
      | 0 | 1 | 2 => omega
      | n+3 => rfl
    rw [hc] at hi
    omega
end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FieldFlag
