module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Representatives

/-!
# Remaining native odd-order coverage for the M₂₄ trace calculation

Prime-order square fusion is proved separately by Sylow conjugacy. The two
independent remaining group-theoretic inputs are the odd-order spectrum and
coverage of the mixed orders 15 and 21 by powers of the marked generators.
These are contracts, not assertions that the classification has been proved.
They imply the trace-field result via `ElevenTrace`, whose final assembly
must discharge both contracts.

Source application: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, M₂₄ paragraph, manuscript p.17; James, The modular characters
of the Mathieu groups, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24OddCyclic

/-- The only composite odd element orders in native M₂₄ are 15 and 21. -/
def OddOrderSpectrum : Prop :=
  ∀ g : M24, ¬ 2 ∣ orderOf g →
    orderOf g = 1 ∨ (orderOf g).Prime ∨ orderOf g = 15 ∨ orderOf g = 21

/-- Both mixed orders are covered inside the two corresponding marked cyclic groups. -/
def MixedOrderCyclicCoverage : Prop :=
  ∀ g : M24, orderOf g = 15 ∨ orderOf g = 21 →
    ∃ (i : Fin 2) (n : ℕ), IsConj g (representative (i.castLE (by decide)) ^ n)

end Sporadic.Mathieu.M24OddCyclic
