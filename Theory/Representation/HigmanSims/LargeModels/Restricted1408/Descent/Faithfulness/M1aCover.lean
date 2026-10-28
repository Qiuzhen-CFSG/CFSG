module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aCover.Checked
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aCover.Shape
public import Theory.GroupTheory.GeneratorCosetCoverFiniteIndex

/-!
# A proved 100-coset cover in the abstract HS presentation

The checked trace gives all four signed transitions on 100 representatives,
with multipliers in the literal source subgroup M₁ₐ. Word induction therefore
covers Universal. This establishes finite index without assuming Universal
or M₁ₐ finite, and without transporting equations from a permutation quotient.

Source: ATLAS HSG1-P1.M; reproduction and certificate conventions are retained
in `M1aCover/source/README.md`.
-/

namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness
open Subgroup.CosetWordCertificate

namespace M1aCertificate

private theorem transitions (i : Fin 100) (a : Fin 4) :
    Holds M1a traceGenerator (definitions.repr traceGenerator)
      ⟨i.val, [decode a.val], (destination (4*i.val+a.val)).val⟩ := by
  have hs := (factBEq_eq_true_iff _ _).mp (all_shapes (4*i.val+a.val) (by omega))
  have hd : (4*i.val+a.val) / 4 = i.val := by omega
  have hm : (4*i.val+a.val) % 4 = a.val := by omega
  change facts (output (4*i.val+a.val)) = _ at hs
  rw [hd, hm] at hs
  rw [← hs]
  exact all_hold _ (output_lt _)

/-- A cover by explicit representative words and actual subgroup multipliers. -/
public def cover : Subgroup.GeneratorCosetCover M1a generator (Fin 100) where
  repr i := definitions.repr traceGenerator i.val
  initial := 0
  initial_eq := definitions.repr_zero traceGenerator
  step i a := by
    cases a
    · obtain ⟨h, hh⟩ := transitions i 0
      refine ⟨h, destination (4*i.val+0), ?_⟩
      simpa [decode, traceGenerator, extendedPair] using hh
    · obtain ⟨h, hh⟩ := transitions i 2
      refine ⟨h, destination (4*i.val+2), ?_⟩
      simpa [decode, traceGenerator, extendedPair] using hh
  inv_step i a := by
    cases a
    · obtain ⟨h, hh⟩ := transitions i 1
      refine ⟨h, destination (4*i.val+1), ?_⟩
      simpa [decode, traceGenerator, extendedPair] using hh
    · obtain ⟨h, hh⟩ := transitions i 3
      refine ⟨h, destination (4*i.val+3), ?_⟩
      simpa [decode, traceGenerator, extendedPair] using hh

end M1aCertificate

/-- The literal ATLAS subgroup has finite index in the abstract presentation. -/
public theorem m1a_finiteIndex : M1a.FiniteIndex :=
  ⟨(M1aCertificate.cover.index_pos canonical_generates).ne'⟩

/-- Source index upper bound, proved before any finite-order hypothesis. -/
public theorem m1a_index_le : M1a.index ≤ 100 := by
  simpa using M1aCertificate.cover.index_le_card canonical_generates

/-- The coset certificate reduces finiteness and order to the literal subgroup. -/
public theorem finite_card_le_of_m1a [Finite M1a] :
    Finite Universal ∧ Nat.card Universal ≤ Nat.card M1a * 100 := by
  simpa using M1aCertificate.cover.finite_card_le canonical_generates

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness
