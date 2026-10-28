module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Marking
import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# The common marking lies in both Held local subgroups

The four conjugation identities proposed in `source/marking.json` hold in
the actual Held carrier. Its certified four-point base reduces each equality
to four kernel computations. Taking closures then places the marked subgroup
in both aligned ATLAS candidates. Neither their structure nor any Sylow
assertion is used.

Sources: ATLAS HeG1-max3W1 and HeG1-max4W1, translated in `LocalSubgroups`;
GLS3, Table 5.3p. Word order is unchanged from the existing inverted carrier.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The alternative second-local expressions are the actual conjugates of
the four marked generators. -/
public theorem markedGenerator_conj (i : Fin 4) :
    alignment * markedGenerator i * alignment⁻¹ =
      wordEval a (localWord true) (secondWords i) := by
  fin_cases i <;> apply eq_of_four_point_images <;> decide +kernel

/-- Both aligned literal ATLAS subgroups contain the common marking. -/
public theorem markedSubgroup_le_aligned (i : Bool) :
    markedSubgroup ≤ alignedOvergroup i := by
  cases i
  · exact markedSubgroup_le_first
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    change alignment * markedGenerator j * alignment⁻¹ ∈ localOvergroup true
    rw [markedGenerator_conj]
    exact wordEval_mem _ (a_mem_localOvergroup true)
      (localWord_mem_localOvergroup true) (secondWords j)

end Held.LocalPairs.PairCoverage.SylowOvergroups
