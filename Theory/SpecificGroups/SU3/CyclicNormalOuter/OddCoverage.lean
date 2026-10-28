module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage

/-!
# Arbitrary-automorphism coverage for PSU₃ over every odd prime

Normalize an automorphism to preserve the opposite root groups. Their
normalizer intersection recovers the torus; its unique involution and the
Weyl coset then recover compatible field formulas on both root groups.
Root-group generation extends those formulas to the whole projective group.

The existing specialized coverage wrapper assumes p ≡ 3 modulo eight.
Its underlying torus, Weyl and coordinate lemmas need only odd characteristic.
Using those lemmas directly proves coverage for every odd prime, including
p = 3, without altering the specialized wrapper or certifying simplicity.

Source: Steinberg, Theorem 36, proof steps (1)–(7),
`refs/KGroup/GLS3/Chapter2St1.tex`, and GLS3, Theorem 2.5.12 and §2.7.
-/

public section
open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
include hJ in
/-- Every automorphism of the actual projective SU₃ image over a prime-square
matrix field has a unitary-semilinear formula. The prime is only required to
be odd; no involution hypothesis or congruence modulo eight is imposed. -/
theorem semilinear_coverage_odd
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ := by
  apply semilinear_coverage_of_root_geometry J hJ
    (rootGroup_sup_oppositeRootGroup J hJ hp.one_lt hcard hfixed) a
    (exists_root_pair_normalization J hJ hp hcard hfixed a)
  intro b hU hV
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  have h2 := two_ne_zero_of_prime_square hp hp3 hcard
  have hT := rootTorus_map_eq J hJ h2 b hU hV
  have ht := torus_neg_fixed_of_rootTorus_map_eq J hJ h2 b hT
  have hw := exists_torus_mul_weyl_of_root_preserving J hJ h2 b hU hV
  obtain ⟨σ, t, hfirstU⟩ := root_first_field_of_torus_preserving J hJ hp hp3 hcard b hU hT
  have hfirstV := opposite_first_of_root_first J hJ h2 b hU hV hT ht hw σ t hfirstU
  exact ⟨σ, diagonalUnitary J hJ t,
    root_formulas_of_first_coordinate_normalization J hJ h2 b hU hV ht σ t hfirstU hfirstV⟩
end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage

