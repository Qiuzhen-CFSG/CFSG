module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Semilinear
public import Theory.SpecificGroups.SU3.BinaryTorusField
public import Theory.SpecificGroups.SU3.EvenSemilinear.Geometry
public import Theory.SpecificGroups.SU3.EvenSemilinear.Torus
public import Theory.SpecificGroups.SU3.EvenSemilinear.Opposite
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage
public import BenderSuzuki.External.Huppert.II.theorem_10_13

/-!+# Arbitrary-automorphism coverage for binary projective SU₃

Every automorphism of the actual projective special unitary image over a
field of order `(2^n)^2`, with fixed field of order `2^n` and `n ≥ 2`, is
entrywise application of a field automorphism followed by conjugation by an
actual unitary matrix.

Sylow conjugacy and the isotropic-point action normalize the two root groups.
Their common normalizer recovers the torus. `BinaryTorusField` supplies the
field automorphism on the first coordinate; binary coordinate rigidity and
the Bruhat relation supply the second coordinate and the compatible opposite
root formula. Huppert II.10.13 supplies simplicity, hence root generation,
and an actual special-unitary lift absorbs the initial inner automorphism.
All these premises are discharged from the stated two cardinalities.

Source: Steinberg, Theorem 36, steps (1)–(7),
`refs/KGroup/GLS3/Chapter2St1.tex`; GLS3, Theorem 2.5.12(a,d,f) and §2.7,
which identifies inner-diagonal automorphisms with PGU and field automorphisms
with entrywise maps. The matrix conventions are those of Huppert II.10.12.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.External
open OddPrimeSylow.NormalizedOuter.Coverage

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- Every automorphism of the binary projective SU₃ image admits a concrete
unitary-semilinear formula. No simplicity, root-preservation, coordinate, or
Frobenius-form premise is required in addition to the two field cardinalities. -/
public theorem semilinear_coverage
    (n : ℕ) (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ n) hq hcard hfixed
  refine semilinear_coverage_of_root_geometry J hJ
    (rootGroup_sup_oppositeRootGroup J hJ (by omega : 1 < 2 ^ n) hcard hfixed) a
    (EvenSemilinear.exists_root_pair_normalization J hJ (by omega : 0 < n)
      hcard hfixed a) ?_
  intro b hU hV
  have hfirst := EvenSemilinear.coord_first_surjective J hcard hfixed 1
  have hT := EvenSemilinear.rootTorus_map_eq J hJ hfirst b hU hV
  have hw := EvenSemilinear.exists_torus_mul_weyl_of_root_preserving J hJ hfirst b hU hV
  obtain ⟨σ, t, hcoord⟩ := BinaryTorusField.root_first_field_of_torus_preserving
    J hcard hfixed hJ hq b hU hT
  exact ⟨σ, diagonalUnitary J hJ t,
    EvenSemilinear.root_formulas_of_first_normalization J hJ hcard hfixed hq
      b hU hV hT hw σ t hcoord⟩

end BenderSuzuki.MatrixGroups.HermitianForm
