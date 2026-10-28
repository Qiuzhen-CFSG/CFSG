module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.OuterReduction

/-!
# Conjugacy normal forms from explicit symplectic descent

The outer-quotient reduction is proved in `OuterReduction`. This module
assembles it with two still-explicit matrix descent inputs: the even-degree
field cocycle and the odd-degree exceptional graph cocycle. Each coboundary
produces a genuine conjugating inner automorphism, so the resulting
alternatives assert conjugacy in Aut(Sp₄(F)), not just outer-coset membership.

The displayed cocycle premises must be discharged before this gives the
source's nonbinary involution classification. The binary derived-carrier
classification is a separate remaining obligation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Notation
16.1.3 and Lemma 16.1.4, printed pp.1170–1173 of `refs/quasithin.pdf`.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
open ExceptionalGraph
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Conditional assembly of actual conjugacy normal forms. Both matrix
coboundary premises, in addition to semilinear coverage, remain explicit. -/
theorem involution_normalForms_of_coboundaries {n : ℕ}
    (hcard : Nat.card F = 2^n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (hfield : Even n → ∀ g : Sp F,
      g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1 →
      ∃ h : Sp F, g = h * (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) h)⁻¹)
    (hgraph : Odd n → ∀ g : Sp F,
      g * (graphAut ^ n) g = 1 → ∃ h : Sp F, g = h * ((graphAut ^ n) h)⁻¹)
    (a : MulAut (Sp F)) (ha : orderOf a = 2) :
    (∃ g : Sp F, orderOf g = 2 ∧ a = MulAut.conj g) ∨
      (Even n ∧ IsConj a (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)))) ∨
      (Odd n ∧ IsConj a (graphAut ^ n)) := by
  rcases involution_inner_or_twist hcard hn hclass a ha with hi | ⟨g, he, hg⟩
  · exact Or.inl hi
  · rcases Nat.even_or_odd n with hnEven | hnOdd
    · rw [graph_pow_eq_field_of_even hnEven] at he hg
      obtain ⟨h, hh⟩ := hfield hnEven g hg
      refine Or.inr (Or.inl ⟨hnEven, ?_⟩)
      rw [he]
      exact (inner_twist_isConj _ g h hh).symm
    · obtain ⟨h, hh⟩ := hgraph hnOdd g hg
      refine Or.inr (Or.inr ⟨hnOdd, ?_⟩)
      rw [he]
      exact (inner_twist_isConj _ g h hh).symm

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
