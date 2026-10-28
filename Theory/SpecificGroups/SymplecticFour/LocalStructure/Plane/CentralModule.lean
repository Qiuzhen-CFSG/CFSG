module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The central quotient of the symplectic plane radical

The radical of the actual determinant-one plane stabilizer has symmetric
matrix coordinates. In characteristic two its intersection with the center
of the local group consists exactly of the alternating matrices
`!![0, z; z, 0]`. Congruence by every determinant-one matrix fixes these
coordinates; conversely, the two elementary SL₂ lifts force both diagonal
entries of a fixed symmetric matrix to vanish.

Over a finite field, applying inverse Frobenius to the two diagonal entries
gives a surjective homomorphism with exactly this central kernel. Its induced
quotient equivalence intertwines conjugation by every local element with the
untwisted natural SL₂ action. The square-root correction is essential because
the raw diagonal entries transform by the squares of the matrix entries.

This is the central-module calculation for the plane-local factor in
Aschbacher--Smith, F.1.12(I)(2), printed pp.262--264 of the combined manuscript
of 1 March 2004. Identification of the radical with the two-core and the
residual/perfectness assertions belong to the surrounding local assembly.
-/

@[expose] public section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour.Plane
noncomputable section
variable {F : Type*} [Field F] [CharP F 2]

/-- Raw diagonal coordinates transform by the Frobenius twist of the natural action. -/
theorem congruence_diagonal (A : SpecialLinearGroup (Fin 2) F)
    (B : symmetricMatrices F) (i : Fin 2) :
    (congruence A B).val i i = A.val i 0 ^ 2 * B.val 0 0 + A.val i 1 ^ 2 * B.val 1 1 := by
  have hs : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
  simp only [congruence, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  rw [hs]
  ring_nf
  simp [CharTwo.two_eq_zero]

private theorem congruence_fixed_of_diagonal_zero (B : symmetricMatrices F)
    (hB : ∀ i, B.val i i = 0) (A : SpecialLinearGroup (Fin 2) F) :
    congruence A B = B := by
  have hs : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
  have hd := A.property
  rw [Matrix.det_fin_two, CharTwo.sub_eq_add] at hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · rw [congruence_diagonal, hB, hB, hB]; simp
  · change (A.val * B.val * A.valᵀ) 0 1 = B.val 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      hB, hs, mul_zero, zero_add, add_zero]
    calc
      _ = (A.val 0 0 * A.val 1 1 + A.val 0 1 * A.val 1 0) * B.val 0 1 := by ring
      _ = _ := by rw [hd, one_mul]
  · change (A.val * B.val * A.valᵀ) 1 0 = B.val 1 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      hB, hs, mul_zero, zero_add, add_zero]
    calc
      _ = (A.val 0 0 * A.val 1 1 + A.val 0 1 * A.val 1 0) * B.val 0 1 := by ring
      _ = _ := by rw [hd, one_mul]
  · rw [congruence_diagonal, hB, hB, hB]; simp

private theorem diagonal_zero_of_congruence_fixed (B : symmetricMatrices F)
    (hB : ∀ A, congruence A B = B) : ∀ i, B.val i i = 0 := by
  let U : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp⟩
  let D : SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp⟩
  have hu := congrArg (fun C : symmetricMatrices F => C.val 0 0) (hB U)
  have hd := congrArg (fun C : symmetricMatrices F => C.val 1 1) (hB D)
  rw [congruence_diagonal] at hu hd
  have h1 : B.val 1 1 = 0 := by simpa [U] using hu
  have h0 : B.val 0 0 = 0 := by simpa [D] using hd
  intro i
  fin_cases i <;> assumption

/-- Centrality in the whole local group is equivalent to zero radical diagonal. -/
theorem mem_center_subgroupOf_iff_diagonal_zero (q : radical (F := F)) :
    q ∈ (Subgroup.center (planeLocal (F := F))).subgroupOf radical ↔
      ∀ i, (radicalEquiv q).toAdd.val i i = 0 := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · intro h
    apply diagonal_zero_of_congruence_fixed
    intro A
    rw [← quotientMap_levi A, ← radicalEquiv_conjugate]
    have hc : conjugate (levi A) q = q := by
      apply Subtype.ext
      change levi A * q.val * (levi A)⁻¹ = q.val
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hc]
  · intro h g
    have hc : conjugate g q = q := by
      apply radicalEquiv.injective
      apply Multiplicative.toAdd.injective
      rw [radicalEquiv_conjugate]
      exact congruence_fixed_of_diagonal_zero _ h _
    have hv := congrArg Subtype.val hc
    change g * q.val * g⁻¹ = q.val at hv
    exact (mul_inv_eq_iff_eq_mul).mp hv

/-- The central radical coordinates are precisely the alternating two by two matrices. -/
theorem mem_center_subgroupOf_iff_alternating (q : radical (F := F)) :
    q ∈ (Subgroup.center (planeLocal (F := F))).subgroupOf radical ↔
      ∃ z : F, (radicalEquiv q).toAdd.val = !![0, z; z, 0] := by
  rw [mem_center_subgroupOf_iff_diagonal_zero]
  constructor
  · intro h
    let B := (radicalEquiv q).toAdd
    have hs : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
    refine ⟨B.val 0 1, ?_⟩
    change B.val = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, h, hs]
  · rintro ⟨z, hz⟩ i
    rw [hz]
    fin_cases i <;> rfl

variable [Finite F]

/-- Inverse Frobenius on the diagonal of a symmetric matrix. -/
def untwistedDiagonal : symmetricMatrices F →+ (Fin 2 → F) where
  toFun B i := (frobeniusEquiv F 2).symm (B.val i i)
  map_zero' := by ext i; exact map_zero _
  map_add' B C := by ext i; exact map_add _ _ _

theorem untwistedDiagonal_surjective : Function.Surjective (untwistedDiagonal (F := F)) := by
  intro v
  refine ⟨⟨Matrix.diagonal (fun i => v i ^ 2), Matrix.isSymm_diagonal _⟩, ?_⟩
  ext i
  simp [untwistedDiagonal, frobeniusEquiv_symm_pow]

theorem untwistedDiagonal_congruence (A : SpecialLinearGroup (Fin 2) F)
    (B : symmetricMatrices F) :
    untwistedDiagonal (congruence A B) = A.val *ᵥ untwistedDiagonal B := by
  ext i
  change (frobeniusEquiv F 2).symm ((congruence A B).val i i) = _
  rw [congruence_diagonal, map_add, map_mul, map_mul,
    frobeniusEquiv_symm_pow, frobeniusEquiv_symm_pow]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, untwistedDiagonal]

/-- The natural two-dimensional coordinates on the actual radical. -/
def naturalCoordinates : radical (F := F) →* Multiplicative (Fin 2 → F) :=
  untwistedDiagonal.toMultiplicative.comp radicalEquiv.toMonoidHom

@[simp] theorem naturalCoordinates_apply (q : radical (F := F)) (i : Fin 2) :
    (naturalCoordinates q).toAdd i =
      (frobeniusEquiv F 2).symm ((radicalEquiv q).toAdd.val i i) := rfl

theorem naturalCoordinates_surjective : Function.Surjective (naturalCoordinates (F := F)) := by
  intro v
  obtain ⟨B, hB⟩ := untwistedDiagonal_surjective v.toAdd
  refine ⟨radicalEquiv.symm (Multiplicative.ofAdd B), ?_⟩
  change Multiplicative.ofAdd (untwistedDiagonal
    (radicalEquiv (radicalEquiv.symm (Multiplicative.ofAdd B))).toAdd) = v
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd (untwistedDiagonal B) = v
  rw [hB]
  rfl

theorem naturalCoordinates_ker : (naturalCoordinates (F := F)).ker =
    (Subgroup.center (planeLocal (F := F))).subgroupOf radical := by
  ext q
  rw [MonoidHom.mem_ker, mem_center_subgroupOf_iff_diagonal_zero]
  constructor
  · intro h i
    have hi := congrArg (fun v : Multiplicative (Fin 2 → F) => v.toAdd i) h
    change (frobeniusEquiv F 2).symm ((radicalEquiv q).toAdd.val i i) = 0 at hi
    exact (map_eq_zero_iff (frobeniusEquiv F 2).symm (frobeniusEquiv F 2).symm.injective).mp hi
  · intro h
    apply Multiplicative.toAdd.injective
    ext i
    change (frobeniusEquiv F 2).symm ((radicalEquiv q).toAdd.val i i) = 0
    rw [h, map_zero]

/-- The central quotient of the plane radical is the untwisted natural module. -/
def centralQuotientEquiv :
    (radical (F := F) ⧸ (Subgroup.center (planeLocal (F := F))).subgroupOf radical) ≃*
      Multiplicative (Fin 2 → F) :=
  (QuotientGroup.quotientMulEquivOfEq (naturalCoordinates_ker (F := F)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (naturalCoordinates (F := F))
      naturalCoordinates_surjective)

@[simp] theorem centralQuotientEquiv_mk (q : radical (F := F)) :
    centralQuotientEquiv (QuotientGroup.mk q) = naturalCoordinates q := rfl

/-- The quotient coordinates are square roots of the raw diagonal entries. -/
theorem centralQuotientEquiv_coordinates (q : radical (F := F)) (i : Fin 2) :
    (centralQuotientEquiv (QuotientGroup.mk q)).toAdd i =
      (frobeniusEquiv F 2).symm ((radicalEquiv q).toAdd.val i i) := rfl

/-- Conjugation by every actual local element induces the natural SL₂ action. -/
theorem centralQuotientEquiv_conjugate (g : planeLocal (F := F)) (q : radical (F := F)) :
    centralQuotientEquiv (QuotientGroup.mk (conjugate g q)) =
      Multiplicative.ofAdd ((quotientMap g).val *ᵥ
        (centralQuotientEquiv (QuotientGroup.mk q)).toAdd) := by
  simp only [centralQuotientEquiv_mk]
  apply Multiplicative.toAdd.injective
  change untwistedDiagonal (radicalEquiv (conjugate g q)).toAdd =
    (quotientMap g).val *ᵥ untwistedDiagonal (radicalEquiv q).toAdd
  rw [radicalEquiv_conjugate, untwistedDiagonal_congruence]

end
end Theory.SpecificGroups.SymplecticFour.Plane
