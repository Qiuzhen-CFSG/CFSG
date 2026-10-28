module

public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv.MatrixCoordinates
import Mathlib.Tactic.LinearCombination

/-!
# The deleted permutation representation in the ternary Ree group

The augmentation subspace of the nine-point permutation module over F₃
contains the constant line. Its quotient is seven-dimensional. The maps
`E(v) = (v, -∑ v, 0)` and `R(u) = (u₀-u₈, …, u₆-u₈)` give coordinates:
for sum-zero `u`, `E(R(u)) = u-u₈·ones`, since nine vanishes in F₃.
Consequently `deletedMatrix p = R P(p) E` is multiplicative for the action
`P(p)u = u ∘ p.symm`.

The checked generator intertwining identities identify its conjugate by
`basisChange` with the literal Ree matrices `gamma 0 1` and `upsilon`.
The generated subgroup therefore maps into the original Ree model. This
constructs the matrix-homomorphism input to GLS III §2.2's exceptional
isomorphism A₁(8) ≅ ²G₂(3)′; the projective comparison and identification
of the image with the derived subgroup belong to the assembly module.
-/

public section

open Matrix
open scoped BigOperators

namespace Atlas.ReeG2.TernaryDerived

private def inclusion (v : Fin 7 → ZMod 3) : Fin 9 → ZMod 3 :=
  deletedInclusion *ᵥ v

private def reduction (u : Fin 9 → ZMod 3) : Fin 7 → ZMod 3 :=
  fun i => u (i.castLE (by decide)) - u 8

private theorem inclusion_first (v : Fin 7 → ZMod 3) (i : Fin 7) :
    inclusion v (i.castLE (by decide)) = v i := by
  have hi : i.castLE (by decide : 7 ≤ 9) ≠ (7 : Fin 9) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega
  simp [inclusion, Matrix.mulVec, dotProduct, deletedInclusion, hi]

private theorem inclusion_seven (v : Fin 7 → ZMod 3) :
    inclusion v 7 = -∑ j, v j := by
  have hj (j : Fin 7) : (7 : Fin 9) ≠ j.castLE (by decide) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega
  simp [inclusion, Matrix.mulVec, dotProduct, deletedInclusion, hj]

private theorem inclusion_eight (v : Fin 7 → ZMod 3) : inclusion v 8 = 0 := by
  have hj (j : Fin 7) : (8 : Fin 9) ≠ j.castLE (by decide) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega
  simp [inclusion, Matrix.mulVec, dotProduct, deletedInclusion, hj]

private theorem sum_nine (u : Fin 9 → ZMod 3) :
    ∑ i, u i = (∑ i : Fin 7, u (i.castLE (by decide))) + u 7 + u 8 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  rfl

private theorem inclusion_sum (v : Fin 7 → ZMod 3) : ∑ i, inclusion v i = 0 := by
  rw [sum_nine]
  simp [inclusion_first, inclusion_seven, inclusion_eight]

private theorem inclusion_reduction (u : Fin 9 → ZMod 3) (hu : ∑ i, u i = 0) :
    inclusion (reduction u) = fun i => u i - u 8 := by
  funext i
  by_cases hi : i.val < 7
  · exact inclusion_first (reduction u) ⟨i.val, hi⟩
  · have h78 : i = 7 ∨ i = 8 := by
      have := i.isLt
      rcases (show i.val = 7 ∨ i.val = 8 by omega) with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    rcases h78 with rfl | rfl
    · rw [inclusion_seven]
      simp only [reduction, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [sum_nine] at hu
      linear_combination (norm := ring_nf) -hu
      simp only [show (9 : ZMod 3) = 0 by decide, mul_zero]
    · simp [inclusion_eight]

private theorem deletedMatrix_mulVec (p : Equiv.Perm (Fin 9)) (v : Fin 7 → ZMod 3) :
    deletedMatrix p *ᵥ v = reduction (fun i => inclusion v (p.symm i)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, deletedMatrix, reduction, inclusion,
    sub_mul, Finset.sum_sub_distrib]

/-- The identity permutation acts by the identity matrix. -/
theorem deletedMatrix_one : deletedMatrix 1 = 1 := by
  apply Matrix.mulVec_injective
  funext v
  rw [deletedMatrix_mulVec, Matrix.one_mulVec]
  ext i
  change inclusion v (i.castLE (by decide)) - inclusion v 8 = v i
  simp [inclusion_first, inclusion_eight]

/-- The deleted coordinate formula respects the left permutation multiplication. -/
theorem deletedMatrix_mul (p q : Equiv.Perm (Fin 9)) :
    deletedMatrix (p * q) = deletedMatrix p * deletedMatrix q := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec]
  simp only [deletedMatrix_mulVec]
  have hsum : ∑ i, inclusion v (q.symm i) = 0 :=
    (Equiv.sum_comp q.symm _).trans (inclusion_sum v)
  rw [inclusion_reduction _ hsum]
  ext i
  simp only [reduction, sub_sub_sub_cancel_right]
  rfl

/-- The seven-dimensional deleted permutation representation over the ternary field. -/
def deletedRepresentation : Equiv.Perm (Fin 9) →* Ambient (ZMod 3) where
  toFun p :=
    { val := deletedMatrix p
      inv := deletedMatrix p⁻¹
      val_inv := by rw [← deletedMatrix_mul, mul_inv_cancel, deletedMatrix_one]
      inv_val := by rw [← deletedMatrix_mul, inv_mul_cancel, deletedMatrix_one] }
  map_one' := Units.ext deletedMatrix_one
  map_mul' p q := Units.ext (deletedMatrix_mul p q)

@[simp] theorem deletedRepresentation_val (p : Equiv.Perm (Fin 9)) :
    (deletedRepresentation p).val = deletedMatrix p := by rfl

private def matrixRepresentation : Equiv.Perm (Fin 9) →* Ambient (ZMod 3) :=
  (MulAut.conj basisChange).toMonoidHom.comp deletedRepresentation

private theorem matrixRepresentation_gamma :
    matrixRepresentation gammaPerm = gamma (F := ZMod 3) 0 1 := by
  apply Units.ext
  change basisMatrix * deletedMatrix gammaPerm * basisInverse = gammaMatrix 0 1
  rw [← gamma_intertwine, mul_assoc, basisMatrix_mul_inverse, mul_one]

private theorem matrixRepresentation_weyl :
    matrixRepresentation weylPerm = (upsilon : Ambient (ZMod 3)) := by
  apply Units.ext
  change basisMatrix * deletedMatrix weylPerm * basisInverse = upsilonMatrix
  rw [← weyl_intertwine, mul_assoc, basisMatrix_mul_inverse, mul_one]

private theorem matrixRepresentation_mem (p : PermutationModel) :
    matrixRepresentation p.val ∈ generated (ZMod 3) 0 := by
  have h : permutationSubgroup ≤ (generated (ZMod 3) 0).comap matrixRepresentation := by
    apply (Subgroup.closure_le _).mpr
    intro p hp
    change matrixRepresentation p ∈ generated (ZMod 3) 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · rw [matrixRepresentation_gamma]
      exact reeGamma.property
    · rw [matrixRepresentation_weyl]
      exact reeWeyl.property
  exact h p.property

/-- The marked permutation group maps into the original generated Ree matrix group,
by conjugating its deleted permutation representation by `basisChange`. -/
def toRee : PermutationModel →* Model (ZMod 3) 0 :=
  (matrixRepresentation.comp permutationSubgroup.subtype).codRestrict
    (generated (ZMod 3) 0) matrixRepresentation_mem

/-- The map uses precisely the checked coordinate change. -/
theorem toRee_val (p : PermutationModel) :
    (toRee p).val.val = basisMatrix * deletedMatrix p.val * basisInverse := by rfl

@[simp] theorem toRee_gamma : toRee gammaGenerator = reeGamma :=
  Subtype.ext matrixRepresentation_gamma

@[simp] theorem toRee_weyl : toRee weylGenerator = reeWeyl :=
  Subtype.ext matrixRepresentation_weyl

/-- This supplies the nontriviality input to the exceptional-isomorphism assembly. -/
theorem toRee_ne_one : toRee ≠ 1 := hom_ne_one_of_weyl toRee toRee_weyl

end Atlas.ReeG2.TernaryDerived
