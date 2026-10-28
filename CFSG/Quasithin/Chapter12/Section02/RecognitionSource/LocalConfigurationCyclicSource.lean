module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionCoreGeneration
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSmallAssembly

/-!
# The cyclic TI pair and linear block in 12.2.21–24

The invariant odd-subgroup construction, the fixed-layer exclusion, the
binary-three numerical reduction, and the terminal involution argument
prove that the original odd subgroup has prime order. The proved core
displacement then supplies the actual linear block on the original
component and its intrinsic quotient module.

Only the permitted earlier structural and natural-action inputs remain.
The last theorem discharges `cyclicStep` in the original local configuration
assembly; the natural and rigidity inputs belong to its other source owners.
Source: Aschbacher–Smith, 12.2.21–24, printed pp.802–804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}

/-- Source 12.2.23 on the original invariant odd subgroup. Both nonprime
alternatives are excluded, with no terminal extraspecial premise. -/
theorem InvariantOddLocalAnalysis.prime_order
    (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnone : NoEscape L V) : Nat.card P = p := by
  apply prime_order_of_extraspecial_terminal D A hTV S hnone
  intro he hc _ hf hp hd hW
  exact S.extraspecial_false_of_core_involutions h D A hTV he hc hf hp hd hW

/-- Construct all clauses of the cyclic TI-pair and linear-block analysis
from the original hypotheses and the permitted natural analysis. -/
theorem exists_cyclicLocalAnalysis
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  apply cyclicLocalAnalysis_of_invariant_odd_and_prime_steps h D structural A
    (exists_invariantOddLocalAnalysis h D structural A hTI)
  intro p H P U W g v S
  exact S.prime_order h D A ((structural G T L h).2.2 V D).1 hnone

/-- The original local configuration consumer with its cyclic step discharged.
Natural recognition and rigidity remain with their existing source owners. -/
theorem localConfiguration_of_natural_and_rigidity
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (naturalStep : NoEscape L V → IsTISubgroup V →
      ∃ d, NaturalLocalAnalysis T L V d)
    (rigidityStep : ∀ d H P U, NaturalLocalAnalysis T L V d →
      CyclicLocalAnalysis T L V d H P U → NoEscape L V → IsTISubgroup V →
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) :
    ∃ d, SplitLinearConfiguration L V d :=
  localConfiguration_of_source_steps D naturalStep
    (fun _ A hn ht => exists_cyclicLocalAnalysis h D structural A hn ht)
    rigidityStep hnone hTI

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
