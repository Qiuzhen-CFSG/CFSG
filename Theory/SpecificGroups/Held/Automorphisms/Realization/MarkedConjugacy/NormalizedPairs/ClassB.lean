module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.Contracts
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.OrbitTools
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Checks
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Rejection

/-!
# The second Held involution class: certificate assembly

The family consists of actual Held conjugation words and their conjugates by
the seventeen powers of `ab`. Four-point transition checks under `a` prove
closure of the entire family under both original generators. Thus it covers
every conjugate of the literal seed `(ab³)⁴`. A failed source relator at each
representative rejects all seventeen conjugates as well.

`classCalculation_of_closure` supplies the complete rejection certificate.
The generator-closure obligation remains explicit; the proposal tables alone
do not establish it.

Source: John Bray's `Held/Model/Source/HeG1-P1.M`, together with the retained
HeG1-p2058B0 permutation files. Inversion converts their GAP right action to
the Lean left action without changing the order of letters in the words.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB

public theorem representative_zero : representative 0 = secondSeed := rfl

/-- The actual source calculation, conditional only on the two complete
finite certificates for the explicitly defined family. -/
public theorem classCalculation_of_row_checks
    (hc : ∀ i : Fin 11025, ClosedAt i)
    (hr : ∀ i : Fin 11025, RejectedAt i) : ClassCalculation secondSeed := by
  apply calculation_of_orbit_representatives representative
  · exact ⟨0, representative_zero⟩
  · intro i j
    exact closure_of_check i (hc i) j
  · intro i k hk
    exact rejection_of_check i (hr i) k hk

/-- Complete representative rejection leaves only the full closure certificate. -/
public theorem classCalculation_of_closure
    (hc : ∀ i : Fin 11025, ClosedAt i) : ClassCalculation secondSeed :=
  classCalculation_of_row_checks hc rejectedAt_all

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB
