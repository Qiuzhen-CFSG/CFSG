module

public import Stellmacher.Recognition.LyonsU3Four.TableIConsecutiveResidualData
public import Stellmacher.Recognition.LyonsU3Four.TableIConsecutiveResidualCounts
public import Stellmacher.Recognition.LyonsU3Four.TableIConsecutiveResidualEnumeration

/-!
# Canonical assembly for the consecutive-difference case

The Z₄ reduction supplies four distinguished normalized rows and makes the
remaining rows periodic. Their multiplicities are encoded by 23 Galois-orbit
counts. Identifying those counts with H, J, K, or L gives an actual signed
row equivalence with the canonical matrix, retaining every repeated row and
sending the principal index to the printed principal row.

The residual coverage and count enumeration prove that these are the only
possibilities. Thus consecutive equal unit differences, in the absence of a
large difference, give a canonical pattern already in the original orientation.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 379,
Case 5(a)–(c). The canonical J uses the corrected order-four entry −2.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData

variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)

/-- Assemble one of the four explicit Case 5 count vectors into a
principal-preserving signed identification with the canonical catalogue. -/
theorem hasCanonicalTableIPattern_of_caseFiveCounts (principal : I)
    (h : d.TableIPatternHypotheses principal) (n : Fin 23 → ℕ)
    (hn : ∃ c : Fin 4, n = ConsecutiveResidual.counts c)
    (hm : ∀ r, d.tableIRowMultiplicity r = ConsecutiveResidual.multiplicity n r) :
    d.HasCanonicalTableIPattern principal := by
  obtain ⟨c, rfl⟩ := hn
  apply d.hasCanonicalTableIPattern_of_rowMultiplicity principal h
    (ConsecutiveResidual.tableCase c) (ConsecutiveResidual.tableVariant c)
  intro r
  exact (hm r).trans (ConsecutiveResidual.multiplicity_counts c r)

/-- Consecutive equal unit differences force one of the canonical Case 5
patterns H, J, K, L, retaining all rows and the principal index. -/
theorem hasCanonicalTableIPattern_of_consecutive {principal : I}
    (h : d.TableIPatternHypotheses principal) (hl : ¬ d.HasLargeDifference)
    (hc : d.HasConsecutiveUnitDifferences) :
    d.HasCanonicalTableIPattern principal := by
  obtain ⟨n, hn, hm⟩ := d.exists_consecutiveResidual_counts principal h hl
    (d.hasZ4Frame_of_consecutive principal h hl hc)
  exact d.hasCanonicalTableIPattern_of_caseFiveCounts principal h n
    (ConsecutiveResidual.count_solutions n hn) hm

/-- The consecutive-difference branch of Table I classification up to
column reflection. -/
theorem canonical_or_reflected_of_consecutive {principal : I}
    (h : d.TableIPatternHypotheses principal) (hl : ¬ d.HasLargeDifference)
    (hc : d.HasConsecutiveUnitDifferences) :
    d.HasCanonicalTableIPattern principal ∨
      d.reflectColumns.HasCanonicalTableIPattern principal :=
  Or.inl (d.hasCanonicalTableIPattern_of_consecutive h hl hc)

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
