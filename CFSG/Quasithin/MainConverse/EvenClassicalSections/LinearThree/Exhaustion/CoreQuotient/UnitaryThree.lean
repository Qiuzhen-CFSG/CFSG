module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.Structure
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Binary
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.SU3.OuterSolvable

/-!
# The unitary degree-three core's outer quotient

This conditional adapter takes global unitary-semilinear coverage for the
standard form with fixed-field order `2^n`, `n ≥ 2`. The arbitrary Hermitian
form in `ClassicalGroup.IsPSU` is transported to that standard form, preserving
the stored Frobenius involution. Its fixed-field cardinality follows from the
matrix-field cardinality and the specified involution.

The exceptional parameter `m = 1` contradicts nonsolvability, since the actual
`PSU₃(2)` model is solvable. For `m ≥ 2`, the unitary diagonal quotient and
abelian field automorphisms make the outer quotient solvable. Transport along
the actual model isomorphism then gives the outer quotient of the original
simple group. The parent core-quotient assembly discharges coverage separately.

Source: GLS3, Theorem 2.5.12 and Section 2.7, as used in the extension argument
of Theorem 6.5.3 (`refs/KGroup/GLS3/chapter2.tex`, `chapter6.tex`).
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary

/-- Solvability of the actual outer quotient for every nonsolvable simple
`PSU₃(2^m)` carrier, conditional only on the specified global coverage theorem. -/
public theorem unitaryThree_outer_isSolvable_of_semilinear_coverage
    (hcoverage : ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E)
      (n : ℕ), 2 ≤ n → J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
      Nat.card E = (2 ^ n) ^ 2 → Nat.card {z : E // J.conj z = z} = 2 ^ n →
      ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
        ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ)
    (S : Type) [Group S] [IsSimpleGroup S] (hns : ¬ Group.IsSolvable S)
    (m : ℕ) (hm : 0 < m) (hS : ClassicalGroup.IsPSU S 3 (2 ^ m)) :
    Group.IsSolvable (MulAut.Outer S) := by
  by_cases hm1 : m = 1
  · subst m
    exact (hns (UnitaryThreeSections.psu3_two_isSolvable (by simpa using hS))).elim
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩ := hS
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J m hm hcard hconj
  have hfixed : Nat.card {z : E // (FormTransport.standardForm J).conj z = z} = 2 ^ m :=
    fixed_card J m hm hcard hconj
  let : Group.IsSolvable (MulAut.Outer
      (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J))) :=
    (FormTransport.standardForm J).outer_isSolvable_of_semilinear_coverage rfl
      (hcoverage E (FormTransport.standardForm J) m (by omega) rfl hcard hfixed)
  exact MulAut.isSolvable_outer_of_mulEquiv
    (e.trans (FormTransport.projectiveEquiv J C hC))

end CFSG.Quasithin.MainConverse.LinearThreeSections
