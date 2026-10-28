module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.OrderSpectrum
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace

/-!
# Applying the native odd-order spectrum to the M₂₄ trace calculation

The proved spectrum discharges the corresponding premise in the existing square
fusion and trace-field consumers. Only mixed-order cyclic coverage remains an
explicit input, owned by the independent coverage proof and the final assembly.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 5.1, M₂₄ paragraph, manuscript p.17.
-/

public section

namespace Sporadic.Mathieu.M24OddCyclic

/-- The spectrum premise of odd square fusion is now discharged for native M₂₄. -/
theorem odd_square_conjugacy_of_mixed_order_coverage
    (hmixed : MixedOrderCyclicCoverage) (g : M24) (hg : ¬ 2 ∣ orderOf g) :
    IsConj g (g ^ 2) :=
  odd_square_conjugacy_of_calculations oddOrderSpectrum hmixed g hg

end Sporadic.Mathieu.M24OddCyclic

namespace Representation.Mathieu.M24DegreeSpectrum
open Sporadic.Mathieu.M24OddCyclic
universe v

/-- The native degree-eleven trace field now requires only mixed-order cyclic coverage. -/
theorem degreeElevenTraceField_of_mixed_order_coverage
    (hmixed : MixedOrderCyclicCoverage) : DegreeElevenTraceField.{v} :=
  degreeElevenTraceField_of_odd_order_calculations oddOrderSpectrum hmixed

end Representation.Mathieu.M24DegreeSpectrum
