module

public import Theory.SpecificGroups.SU3.OddRootFixers.FieldElimination
public import Theory.SpecificGroups.SU3.OddRootFixers

/-!
# From field elimination to a marked fixed PSL₂

Field elimination gives a triangular unitary representative with equal outer
diagonal entries. This consumer keeps the subsequent triangular-to-diagonal
conversion explicit, and applies the existing fixed-block construction after
that conversion. Its conclusions contain the literal mapped center of the
specified Sylow subgroup. The conversion, and hence the unconditional fixed
subgroup theorem, belongs to the triangular-conjugacy and final assembly owners.

Source: GLS4, Chapter 4, Lemma 3.6(c,d), used in Chapter 2, Lemma 13.2.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

include hn hcard hfixed in
/-- The special-unitary application of field elimination to the marked fixed block.
Only the further diagonalization step remains explicit. -/
theorem special_fixed_linear_of_triangular_conversion
    (P : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    (ha : Odd (orderOf a))
    (hfix : ∀ x ∈ (center P).map (P : Subgroup J.specialSubgroup).subtype, a x = x)
    (hdiagonal : HasSpecialRootForm J hJ (IsRootTriangular J) P a →
      HasSpecialRootForm J hJ (IsRootDiagonal J) P a) :
    ∃ I : Subgroup J.specialSubgroup, Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧
      (center P).map (P : Subgroup J.specialSubgroup).subtype ≤ I ∧
      ∀ x ∈ I, a x = x :=
  special_fixed_linear_of_diagonal_form J hJ hn hcard hfixed P a
    (hdiagonal (special_triangular_form J hJ hn hcard hfixed P a ha hfix))

include hn hcard hfixed in
/-- The projective application uses the same actual quotient conventions. -/
theorem projective_fixed_linear_of_triangular_conversion
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : Odd (orderOf a))
    (hfix : ∀ x ∈ (center P).map
      (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype, a x = x)
    (hdiagonal : HasProjectiveRootForm J hJ (IsRootTriangular J) P a →
      HasProjectiveRootForm J hJ (IsRootDiagonal J) P a) :
    ∃ I : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧
      (center P).map (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype ≤ I ∧
      ∀ x ∈ I, a x = x :=
  projective_fixed_linear_of_diagonal_form J hJ hn hcard hfixed P a
    (hdiagonal (projective_triangular_form J hJ hn hcard hfixed P a ha hfix))

end BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
