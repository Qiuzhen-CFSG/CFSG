module
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Determinant

/-!
# Inverting maximal-ideal errors in a finite algebra

In a finite free algebra over a commutative local ring, `1 - r` is a unit
when every entry of the left-multiplication matrix of `r` belongs to the
maximal ideal. For a finite group algebra it suffices that every coefficient
of `r` belongs to that ideal. This is the Jacobson correction used to turn
a relative-trace congruence into an exact relative trace.

The matrix of multiplication by `1 - r` reduces to the identity in the
residue field. Its determinant therefore reduces to one and is a unit in
the local ring. Multiplication by `1 - r` is consequently bijective, which
makes `1 - r` a unit. In the group basis, the required matrix entries are
just translated coefficients of `r`.

Ported from `Submission/ZStar/JacobsonFiniteAlgebra.lean` at revision
`c3503435` of `public/lean-eval/glauberman_zStar`. The generic basis lemmas
and group-algebra specialization retain the historical statements. Their
proofs need only Mathlib's matrix, local-ring, and group-algebra APIs.
-/

open Module

namespace ModularBlock.JacobsonFiniteAlgebra

attribute [local instance] Fintype.ofFinite

/-- A maximal-ideal left-multiplication matrix makes `1 - r` a unit. -/
public theorem isUnit_one_sub_of_mulLeft_matrix_mem_maximalIdeal_of_basis
    {R A ι : Type*} [CommRing R] [IsLocalRing R]
    [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι R A) (r : A)
    (hr : ∀ i j : ι,
      Algebra.leftMulMatrix b r i j ∈ IsLocalRing.maximalIdeal R) :
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
  have hLbij : Function.Bijective L := (Module.End.isUnit_iff L).mp hLunit
  apply IsUnit.isUnit_iff_mulLeft_bijective.mpr
  change Function.Bijective (fun x : A => (1 - r) * x) at hLbij
  exact hLbij

/-- The matrix criterion stated in the chosen basis of a finite free algebra. -/
public theorem isUnit_one_sub_of_mulLeft_matrix_mem_maximalIdeal
    {R A : Type*} [CommRing R] [IsLocalRing R]
    [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
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

/-- Coefficientwise membership in the maximal ideal suffices to invert `1 - r`. -/
public theorem groupAlgebra_isUnit_one_sub_of_coeff_mem_maximalIdeal
    {R G : Type*} [CommRing R] [IsLocalRing R] [Group G] [Finite G]
    (r : MonoidAlgebra R G)
    (hr : ∀ x : G, r.coeff x ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (1 - r) := by
  classical
  apply isUnit_one_sub_of_mulLeft_matrix_mem_maximalIdeal_of_basis
    (MonoidAlgebra.basis G R) r
  intro i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change (r * MonoidAlgebra.single j (1 : R)).coeff i ∈ IsLocalRing.maximalIdeal R
  rw [MonoidAlgebra.coeff_mul_single_apply]
  simpa using hr (i * j⁻¹)

end ModularBlock.JacobsonFiniteAlgebra
