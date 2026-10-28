module

public import Theory.SpecificGroups.SU3.EvenSemilinear.Geometry
public import Theory.SpecificGroups.SU3.EvenSemilinear.Torus
public import Theory.SpecificGroups.SU3.EvenSemilinear.Field
public import Theory.SpecificGroups.SU3.EvenSemilinear.Opposite
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage

/-!
# Unconditional characteristic-two PSU₃ semilinear coverage

Every automorphism of the simple projective special unitary group on the
antidiagonal Hermitian model over a field of order `(2^n)^2`, with `n ≥ 2`
and conjugation `x ↦ x^(2^n)`, has a genuine unitary-semilinear form.

The binary root Sylow subgroup and the action on isotropic points normalize
the two opposite root groups. Their normalizers recover the torus and the
Weyl coset. The torus weights recover the field automorphism; the binary
Heisenberg square and norm-one torus arguments eliminate central shears.
The Bruhat relation identifies the same unitary representative on the
opposite root, and simplicity supplies root-group generation.

All normalization and rigidity inputs are discharged. Simplicity is retained
as an input, and no independent order or simplicity certification is needed.
Source: Steinberg, Theorem 36, steps (1)–(7),
`refs/KGroup/GLS3/Chapter2St1.tex`, and GLS3, Theorem 2.5.12 and §2.7.
-/

public section
open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- Opposite-root preservation forces compatible genuine unitary-semilinear
formulas in characteristic two. No torus or coordinate premise remains. -/
theorem root_formulas_of_opposite_root_preserving [CharP E 2]
    {q : ℕ} (hq : 2 < q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hV : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ) :
    ∃ (σ : E ≃+* E) (u : J.unitarySubgroup),
      (∀ z : hermitianUnipotentCoord J,
        (b (root J hJ z)).val = ProjGenLinGroup.mk u.val *
          ProjGenLinGroup.map σ.toRingHom (root J hJ z).val *
          (ProjGenLinGroup.mk u.val)⁻¹) ∧
      (∀ z : hermitianUnipotentCoord J,
        (b (oppositeRoot J hJ z)).val = ProjGenLinGroup.mk u.val *
          ProjGenLinGroup.map σ.toRingHom (oppositeRoot J hJ z).val *
          (ProjGenLinGroup.mk u.val)⁻¹) := by
  have hfirst : ∃ z : hermitianUnipotentCoord J, z.val.1 = 1 :=
    coord_first_surjective J hcard hfixed 1
  have hT := rootTorus_map_eq J hJ hfirst b hU hV
  have hw := exists_torus_mul_weyl_of_root_preserving J hJ hfirst b hU hV
  obtain ⟨σ, t, hcoord⟩ := first_field_of_torus_intertwining J hq hcard hfixed
    (rootCoordinateAut J hJ b hU) (rootCoordinateAut_torus_intertwining J hJ b hU hT)
  exact ⟨σ, diagonalUnitary J hJ t,
    root_formulas_of_first_normalization J hJ hcard hfixed hq b hU hV hT hw σ t hcoord⟩

include hJ in
/-- Every automorphism of the simple binary projective SU₃ image has a
unitary-semilinear form, with an actual unitary matrix and a field automorphism.
The stated field size and conjugation supply all characteristic and fixed-field
hypotheses; no semilinear coverage, torus or rigidity premise is assumed. -/
theorem semilinear_coverage
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn)
  exact semilinear_coverage_of_root_geometry J hJ
    (rootGroup_sup_oppositeRootGroup J hJ (by omega : 1 < 2 ^ n) hcard hfixed) a
    (exists_root_pair_normalization J hJ (by omega : 0 < n) hcard hfixed a)
    (root_formulas_of_opposite_root_preserving J hJ hq hcard hfixed)

end BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
