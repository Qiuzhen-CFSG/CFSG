import Submission.ZStar.NagaoTrace
import Mathlib.LinearAlgebra.Determinant

/-!
Finite-algebra form of the Jacobson-radical correction over a local base.

An element whose left-multiplication matrix has all entries in the maximal
ideal has `1 - r` invertible.  This is the concrete matrix statement needed
for corners of finite group-algebra endomorphism rings.
-/

noncomputable section

open Module

namespace Submission.ZStar
namespace JacobsonFiniteAlgebra

universe u v

attribute [local instance] Fintype.ofFinite

theorem isUnit_one_sub_of_mulLeft_matrix_mem_maximalIdeal_of_basis
    {R A ι : Type*} [CommRing R] [IsLocalRing R]
    [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι R A) (r : A)
    (hr : ∀ i j : ι,
      Algebra.leftMulMatrix b r i j ∈
        IsLocalRing.maximalIdeal R) :
    IsUnit (1 - r) := by
  classical
  let L : A →ₗ[R] A := Algebra.lmul R A (1 - r)
  let M : Matrix ι ι R := LinearMap.toMatrix b b L
  have hL : L = LinearMap.id - Algebra.lmul R A r := by
    ext x
    simp [L]
  have hMres : M.map (IsLocalRing.residue R) = 1 := by
    ext i j
    change IsLocalRing.residue R
        ((LinearMap.toMatrix b b L) i j) =
      (1 : Matrix ι ι (IsLocalRing.ResidueField R)) i j
    rw [hL, map_sub, ← Module.End.one_eq_id, LinearMap.toMatrix_one]
    change IsLocalRing.residue R
        ((1 : Matrix ι ι R) i j -
          ((LinearMap.toMatrix b b) (LinearMap.mulLeft R r)) i j) =
      (1 : Matrix ι ι (IsLocalRing.ResidueField R)) i j
    have hmul : Algebra.lmul R A r = LinearMap.mulLeft R r := by
      ext x
      rfl
    have hz : IsLocalRing.residue R
        ((LinearMap.toMatrix b b) (LinearMap.mulLeft R r) i j) = 0 :=
      (IsLocalRing.residue_eq_zero_iff
        ((LinearMap.toMatrix b b) (LinearMap.mulLeft R r) i j)).2 (by
          rw [← hmul]
          exact hr i j)
    rw [map_sub, hz, sub_zero]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  have hdetres : IsLocalRing.residue R M.det = 1 := by
    rw [(IsLocalRing.residue R).map_det]
    change (M.map (IsLocalRing.residue R)).det = 1
    rw [hMres, Matrix.det_one]
  have hdetunit : IsUnit M.det := by
    apply isUnit_of_map_unit (IsLocalRing.residue R)
    rw [hdetres]
    exact isUnit_one
  have hLunit : IsUnit L := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    rw [← LinearMap.det_toMatrix b L]
    exact hdetunit
  have hLbij : Function.Bijective L :=
    (Module.End.isUnit_iff L).mp hLunit
  apply IsUnit.isUnit_iff_mulLeft_bijective.mpr
  change Function.Bijective (fun x : A => (1 - r) * x) at hLbij
  exact hLbij

theorem isUnit_one_sub_of_mulLeft_matrix_mem_maximalIdeal
    {R A : Type*} [CommRing R] [IsLocalRing R]
    [Ring A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (r : A)
    (hr : ∀ i j : Module.Free.ChooseBasisIndex R A,
      (LinearMap.toMatrix (Module.Free.chooseBasis R A)
        (Module.Free.chooseBasis R A) (LinearMap.mulLeft R r)) i j ∈
          IsLocalRing.maximalIdeal R) :
    IsUnit (1 - r) := by
  exact isUnit_one_sub_of_mulLeft_matrix_mem_maximalIdeal_of_basis
    (Module.Free.chooseBasis R A) r (by
      intro i j
      have hmul : LinearMap.mulLeft R r = Algebra.lmul R A r := by
        ext x
        rfl
      simpa only [Algebra.leftMulMatrix_apply, ← hmul] using hr i j)

/-- In a finite group algebra, coefficientwise membership in the maximal
ideal is enough to invert `1 - r`. -/
theorem groupAlgebra_isUnit_one_sub_of_coeff_mem_maximalIdeal
    {R G : Type*} [CommRing R] [IsLocalRing R] [Group G] [Finite G]
    (r : MonoidAlgebra R G)
    (hr : ∀ x : G, r x ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (1 - r) := by
  classical
  apply isUnit_one_sub_of_mulLeft_matrix_mem_maximalIdeal_of_basis
    (Finsupp.basisSingleOne : Basis G R (MonoidAlgebra R G)) r
  intro i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change ((r * MonoidAlgebra.single j (1 : R) : MonoidAlgebra R G) i) ∈
    IsLocalRing.maximalIdeal R
  rw [MonoidAlgebra.mul_single_apply]
  simpa using hr (i * j⁻¹)

end JacobsonFiniteAlgebra
end Submission.ZStar
