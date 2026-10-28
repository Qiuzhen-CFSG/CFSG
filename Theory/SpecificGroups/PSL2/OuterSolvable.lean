module

public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import Theory.SpecificGroups.PSL2.OuterSolvable.Semilinear

/-!
# The binary PSL₂ outer quotient from automorphism coverage

The semilinear parameter calculation proves solvability over each binary
model from inner-field coverage. Actual field and group isomorphisms then
transport the result to every finite field of characteristic two. The
nonsolvability hypothesis excludes the two-element field, so only the
specified coverage for exponents at least two is used.

This is the binary A₁ case of the outer-quotient reduction from GLS3,
Theorem 2.5.12 (`refs/KGroup/GLS3/chapter2.tex`). The coverage theorem is an
explicit input, owned separately from this quotient calculation.
-/

namespace Theory.PSL2.OuterSolvable

/-- Solvability of the outer group of a binary model, given actual inner-field coverage. -/
public theorem binary_outer_isSolvable_of_coverage (n : ℕ)
    (hcoverage : ∀ a : MulAut (BinaryGroup n),
      ∃ (g : BinaryGroup n) (σ : BinaryField n ≃+* BinaryField n),
        a = MulAut.conj g * fieldAut σ) :
    Group.IsSolvable (MulAut.Outer (BinaryGroup n)) :=
  outer_isSolvable_of_field_coverage hcoverage

/-- Binary coverage for exponents at least two suffices for every nonsolvable
finite-field PSL₂ in characteristic two. -/
public theorem charTwo_outer_isSolvable_of_binary_coverage
    (hcoverage : ∀ n : ℕ, 2 ≤ n → ∀ a : MulAut (BinaryGroup n),
      ∃ (g : BinaryGroup n) (σ : BinaryField n ≃+* BinaryField n),
        a = MulAut.conj g * fieldAut σ)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hns : ¬ Group.IsSolvable (Group K)) :
    Group.IsSolvable (MulAut.Outer (Group K)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := binary_model_of_not_isSolvable hns
  let : Group.IsSolvable (MulAut.Outer (BinaryGroup n)) :=
    binary_outer_isSolvable_of_coverage n (hcoverage n hn)
  exact MulAut.isSolvable_outer_of_mulEquiv e

end Theory.PSL2.OuterSolvable
