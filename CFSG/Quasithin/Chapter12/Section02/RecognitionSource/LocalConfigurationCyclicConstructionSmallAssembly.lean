module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSmallOdd
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionSylowAssembly

/-!
# Completing the invariant odd-subgroup construction

The proved small odd-group alternatives discharge the last premise of the
invariant Sylow selection. This constructs the full InvariantOddLocalAnalysis
from the original chosen module, structural input, TI condition and permitted
natural analysis, retaining the literal pair, orbit, residual and actions.

The cyclic-block application now retains only the terminal binary-three
component-module contradiction of 12.2.23. Its proof and final cyclic-block
assembly remain with qt-d-12213-cyclic-block. The source-theorem owner
qt-d-12213-local-configuration discharges the earlier natural analysis.
Source: Aschbacher–Smith, 12.2.21–24, printed pp.802–804.
-/

public noncomputable section
open Subgroup

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open Theory.GroupTheory
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}

/-- Source 12.2.21–22: construct the invariant odd Sylow, its literal TI
pair and canonical elementary orbit, from the original natural analysis. -/
theorem exists_invariantOddLocalAnalysis
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hTI : IsTISubgroup V) :
    ∃ p H P U W g v, InvariantOddLocalAnalysis T L V d p H P U W g v := by
  apply invariantOddLocalAnalysis_of_small_odd_alternatives h D structural A hTI
  intro p H P U g S
  exact S.small_odd_alternatives h D A ((structural G T L h).2.2 V D).1 hTI

/-- Apply the completed invariant odd construction and numerical reduction
to the cyclic-block consumer. The terminal component-module contradiction
in 12.2.23 remains with qt-d-12213-cyclic-block. -/
theorem cyclicLocalAnalysis_of_terminal_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (terminal : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 → d = 3 → Nat.card W = 64 →
      W ≤ centralizer (H.pCoreIn 2 : Set G) →
      H ≤ normalizer (((frattini P).map P.subtype ⊔ W : Subgroup G) : Set G) →
      H ≤ normalizer ((H.pCoreIn 2 ⊓ centralizer
        (((frattini P).map P.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) →
      False) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  apply cyclicLocalAnalysis_of_small_odd_alternatives_and_terminal_core
    h D structural A hnone hTI _ terminal
  intro p H P U g S
  exact S.small_odd_alternatives h D A ((structural G T L h).2.2 V D).1 hTI

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
