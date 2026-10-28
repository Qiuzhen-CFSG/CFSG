module

public import Theory.SpecificGroups.SU3.OddRootFixers.TriangularConjugacy
public import Theory.SpecificGroups.SU3.OddRootFixers

/-!
# A marked PSL₂ fixed by an odd triangular unitary actor

The triangular normal form retains the specified Sylow subgroup. Conjugating
its odd-order actor to the diagonal complement now supplies the graph-fixed
PSL₂ block and transports its Sylow-center containment back to the original
coordinates, both in SU₃ and in its literal projective image.

This discharges the triangular-to-diagonal step of GLS4, Chapter 4,
Lemma 3.6(c,d), as used in Chapter 2, Lemma 13.2. The triangular form remains
an explicit premise produced by field elimination; the intrinsic root-fixer
assembly is responsible for discharging it.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

include hn hcard hfixed in
/-- An odd triangular actor on SU₃ fixes a marked actual PSL₂ subgroup. -/
theorem special_fixed_linear_of_triangular_form
    (P : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    (hodd : Odd (orderOf a))
    (hform : HasSpecialRootForm J hJ (IsRootTriangular J) P a) :
    ∃ I : Subgroup J.specialSubgroup, Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧
      (center P).map (P : Subgroup J.specialSubgroup).subtype ≤ I ∧
      ∀ x ∈ I, a x = x :=
  special_fixed_linear_of_diagonal_form J hJ hn hcard hfixed P a
    (special_diagonal_form_of_triangular J hJ hcard hfixed P a hodd hform)

include hn hcard hfixed in
/-- The marked fixed PSL₂ construction in the literal projective special unitary image. -/
theorem projective_fixed_linear_of_triangular_form
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hodd : Odd (orderOf a))
    (hform : HasProjectiveRootForm J hJ (IsRootTriangular J) P a) :
    ∃ I : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧
      (center P).map (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype ≤ I ∧
      ∀ x ∈ I, a x = x :=
  projective_fixed_linear_of_diagonal_form J hJ hn hcard hfixed P a
    (projective_diagonal_form_of_triangular J hJ hcard hfixed P a hodd hform)

end BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
