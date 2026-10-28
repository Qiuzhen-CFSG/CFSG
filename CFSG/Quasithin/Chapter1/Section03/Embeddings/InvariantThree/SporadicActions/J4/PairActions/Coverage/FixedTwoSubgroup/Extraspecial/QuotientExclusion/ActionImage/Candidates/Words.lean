module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Conjugation

/-!
# Candidate words in the specified J₄ two-subgroup

The twenty-one words below are expressed directly in the fifteen certified
generators of `OddIndex.twoSubgroup`. Thus they belong to the actual matrix
carrier, without assuming a polycyclic presentation or its consistency.
The numbering matches the triangular polycyclic exploration retained by the
parent quotient-exclusion task. Right commutators here are written explicitly
as x⁻¹y⁻¹xy to avoid reversing the GAP convention.

These are definitions, not claims that the words form a polycyclic basis.
The candidate-coverage task must certify the needed relations and coverage.
Source for the fifteen starting words: the literal ATLAS max1 generators
and star Sylow lifts in `OddIndex.SylowCandidate`.
-/

@[expose] public section

open Janko4.OuterReduction.OddIndex

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ActionImageCandidates

/-- The certified original generators, as elements of the specified subgroup. -/
noncomputable def original : Fin 11 ⊕ Fin 4 → twoSubgroup :=
  fun i => ⟨twoGenerator i, twoGenerator_mem i⟩

/-- Explicit words matching the exploratory polycyclic numbering. -/
noncomputable def generator : Fin 21 → twoSubgroup :=
  let c₁ := original (.inl 0)
  let c₇ := original (.inl 1)
  let c₂ := original (.inr 1)
  let c₃ := original (.inr 3)
  let c₄ := c₁⁻¹ * original (.inl 2)
  let c₁₀ := c₄⁻¹ * c₁⁻¹ * original (.inl 3)
  let c₁₂ := c₇⁻¹ * c₄⁻¹ * original (.inl 4)
  let c₁₅ := c₁₂⁻¹ * c₁₀⁻¹ * c₁⁻¹ * original (.inl 5)
  let c₁₇ := c₁₅⁻¹ * c₇⁻¹ * c₄⁻¹ * c₁⁻¹ * original (.inl 6)
  let c₂₁ := c₁₇⁻¹ * c₁₅⁻¹ * original (.inl 7)
  let c₁₈ := c₁₀⁻¹ * c₇⁻¹ * original (.inl 8)
  let c₁₉ := c₁₈⁻¹ * c₁₅⁻¹ * c₁⁻¹ * original (.inl 9)
  let c₂₀ := c₁₈⁻¹ * c₁₇⁻¹ * c₁₂⁻¹ * c₁₀⁻¹ * c₇⁻¹ * original (.inl 10)
  let c₈ := c₄⁻¹ * original (.inr 0)
  let c₆ := c₄⁻¹ * c₁⁻¹ * original (.inr 2)
  let c₅ := c₃⁻¹ * c₂⁻¹ * c₃ * c₂
  let c₉ := c₆⁻¹ * c₃⁻¹ * c₆ * c₃
  let c₁₁ := c₆⁻¹ * c₅⁻¹ * c₆ * c₅
  let c₁₃ := c₈⁻¹ * c₆⁻¹ * c₈ * c₆
  let c₁₄ := c₈⁻¹ * c₃⁻¹ * c₈ * c₃
  let c₁₆ := c₁₅⁻¹ * (c₈⁻¹ * c₂⁻¹ * c₈ * c₂)
  ![c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, c₁₀, c₁₁,
    c₁₂, c₁₃, c₁₄, c₁₅, c₁₆, c₁₇, c₁₈, c₁₉, c₂₀, c₂₁]

/-- Evaluate a bit mask in increasing generator order inside the actual subgroup. -/
noncomputable def product (mask : ℕ) : twoSubgroup :=
  (((List.finRange 21).filter (fun i => mask.testBit i.val)).map generator).prod

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ActionImageCandidates
