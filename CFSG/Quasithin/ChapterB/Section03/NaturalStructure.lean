module

public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# The natural module and chief series in B.3.1

The alternating group is irreducible on the actual natural section. In even
degree, the full permutation module has the unique chief series
`0 < constants < core < Full`. We interpret the source's chief-series assertion
as a statement about this module. Cover relations certify that each factor is
chief, and the maximal-chain characterization certifies uniqueness.

The underlying weight-two-vector argument works in all degrees at least five,
and hence includes the section's degrees 5, 6, 7, and 8. The odd-degree splitting
and equivariant core identification are supplied by `BinaryPermutation`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), §B.3, Lemma B.3.1, printed p. 83.
-/

public section

namespace CFSG.Quasithin.ChapterB

open BinaryPermutation Module

/-- B.3.1(1): the alternating group acts irreducibly on its natural module. -/
theorem lemma_B_3_1_1 {n : ℕ} (hn : 5 ≤ n) :
    Representation.IsIrreducible (alternatingNaturalRepresentation (Ω := Fin n)) :=
  alternatingNatural_isIrreducible (by simpa using hn)

/-- The invariant-submodule classification underlying the chief-series assertion. -/
theorem lemma_B_3_1_invariant_submodules {n : ℕ} (hn : 5 ≤ n)
    (W : Subrepresentation (alternatingRepresentation (Ω := Fin n))) :
    W = ⊥ ∨ W = constantsSubrepresentation ∨ W = coreSubrepresentation ∨ W = ⊤ :=
  alternating_subrepresentation_classification (by simpa using hn) W

/-- B.3.1(3): the unique chief series of the full module and the natural dimension. -/
theorem lemma_B_3_1_3 {n : ℕ} (hn : 5 ≤ n) (heven : Even n) :
    (⊥ : Subrepresentation (alternatingRepresentation (Ω := Fin n))) ⋖
        constantsSubrepresentation ∧
    constantsSubrepresentation (Ω := Fin n) ⋖ coreSubrepresentation ∧
    coreSubrepresentation (Ω := Fin n) ⋖ ⊤ ∧
    (∀ S : Set (Subrepresentation (alternatingRepresentation (Ω := Fin n))),
      IsMaxChain (· ≤ ·) S ↔ S = {⊥, constantsSubrepresentation, coreSubrepresentation, ⊤}) ∧
    finrank (ZMod 2) (natural (Fin n)) = n - 2 := by
  have : NeZero n := ⟨by omega⟩
  have hcard : 5 ≤ Fintype.card (Fin n) := by simpa using hn
  have he : Even (Fintype.card (Fin n)) := by simpa using heven
  obtain ⟨h₀, h₁, h₂⟩ := alternating_chiefSeries_covers hcard he
  exact ⟨h₀, h₁, h₂, alternating_unique_chiefSeries hcard he,
    by simpa using finrank_natural_even (Fin n) he⟩

end CFSG.Quasithin.ChapterB
