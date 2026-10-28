module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.Structure
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.PSL2.OuterSolvable
public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable

/-!
# PSL₂ outer quotients for recognized simple cores

`IsPSL` supplies an actual quotient matrix model over an arbitrary finite
field. In characteristic two, transport to GF(2ⁿ), exclusion of the solvable
two-element case, and the supplied binary coverage finish the argument.
For odd characteristic the nonsolvability hypothesis excludes cardinality
three. Inner-diagonal-field coverage then gives a surjection from a solvable
parameter group onto the actual outer quotient. Cardinality nine is included.

The odd-field coverage theorem is proved directly on the central quotient
using root groups. Thus `linearTwo_outer_isSolvable_of_binary_coverage` needs
only the specified binary coverage input.

Source: GLS3, Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`;
Theorem 6.5.3, `refs/KGroup/GLS3/chapter6.tex`, uses this outer quotient in
extension control. No K-group hypothesis, section classification, or
splitting of the diagonal extension is used.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open Theory.PSL2.OuterSolvable

/-- Assembly from binary inner-field coverage and a concrete odd-field
automorphism calculation. The one-input theorem below discharges the odd-field
premise using the proved root-group calculation. -/
public theorem linearTwo_outer_isSolvable_of_binary_coverage_and_odd_coverage
    (hcoverage : ∀ n : ℕ, 2 ≤ n → ∀ a : MulAut (Theory.PSL2.BinaryGroup n),
      ∃ (g : Theory.PSL2.BinaryGroup n)
        (σ : Theory.PSL2.BinaryField n ≃+* Theory.PSL2.BinaryField n),
        a = MulAut.conj g * Theory.PSL2.fieldAut σ)
    (hodd : ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 → 3 < Nat.card K →
      ∀ a : MulAut (Theory.PSL2.Group K),
        ∃ (g : Theory.PSL2.Group K) (u : Kˣ) (σ : K ≃+* K),
          a = MulAut.conj g * diagonalAutHom u * projectiveFieldAutHom σ)
    (S : Type) [Group S] [IsSimpleGroup S]
    (hns : ¬ Group.IsSolvable S) (q : ℕ) (hS : ClassicalGroup.IsPSL S 2 q) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨K, hK, hfin, _hq, ⟨e⟩⟩ := hS
  let : Field K := hK
  let : Finite K := hfin
  let : Fintype K := Fintype.ofFinite K
  have hnsK : ¬ Group.IsSolvable (Theory.PSL2.Group K) := by
    intro h
    let := h
    exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  have houter : Group.IsSolvable (MulAut.Outer (Theory.PSL2.Group K)) := by
    by_cases hchar : ringChar K = 2
    · let : CharP K 2 := ringChar.of_eq hchar
      exact charTwo_outer_isSolvable_of_binary_coverage hcoverage hnsK
    · have hoddcard : Odd (Nat.card K) := by
        rw [Nat.card_eq_fintype_card, Nat.odd_iff]
        exact FiniteField.odd_card_of_char_ne_two hchar
      have hthree := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
        hoddcard hnsK
      exact outer_isSolvable_of_semilinear_coverage (hodd K hchar hthree)
  let := houter
  exact MulAut.isSolvable_outer_of_mulEquiv e

/-- Every nonsolvable simple PSL₂ model has solvable actual outer quotient,
assuming binary inner-field coverage for exponents at least two. Odd-field
coverage, including cardinality nine, is supplied by the proved matrix and
root-group calculation; the small parameters are excluded by nonsolvability. -/
public theorem linearTwo_outer_isSolvable_of_binary_coverage
    (hcoverage : ∀ n : ℕ, 2 ≤ n → ∀ a : MulAut (Theory.PSL2.BinaryGroup n),
      ∃ (g : Theory.PSL2.BinaryGroup n)
        (σ : Theory.PSL2.BinaryField n ≃+* Theory.PSL2.BinaryField n),
        a = MulAut.conj g * Theory.PSL2.fieldAut σ)
    (S : Type) [Group S] [IsSimpleGroup S]
    (hns : ¬ Group.IsSolvable S) (q : ℕ) (hS : ClassicalGroup.IsPSL S 2 q) :
    Group.IsSolvable (MulAut.Outer S) :=
  linearTwo_outer_isSolvable_of_binary_coverage_and_odd_coverage hcoverage
    (fun K _ _ hchar hcard a => odd_semilinear_coverage (K := K) hchar hcard a) S hns q hS

end CFSG.Quasithin.MainConverse.LinearThreeSections
