module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentNodes

/-!
# The finite partition of the small even descent nodes

The first eleven node indices are reserved for size certificates. The
prescribed 59 survivor indices are retained verbatim. All remaining indices
require outside Frattini normalizer witnesses. This partition asserts no
mathematical properties of the nodes themselves.

Source: the fixed indices in `SmallEvenDescentNodes`.
-/

namespace ReeTwo.SylowModel

/-- Exactly the nonlarge entries that are not prescribed survivor entries. -/
@[expose] public def smallEvenWitnessIndices : Finset (Fin 600) :=
  Finset.univ.filter (fun i => 11 ≤ i.val ∧ ∀ j : Fin 59, i ≠ smallEvenCandidateNode j)

/-- The index test involves only the fixed node and candidate indices. -/
public theorem mem_smallEvenWitnessIndices (i : Fin 600) :
    i ∈ smallEvenWitnessIndices ↔ 11 ≤ i.val ∧ ∀ j : Fin 59, i ≠ smallEvenCandidateNode j := by
  simp only [smallEvenWitnessIndices, Finset.mem_filter, Finset.mem_univ, true_and]

end ReeTwo.SylowModel
