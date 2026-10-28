module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicSource
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicBlockAt

/-!
# The cyclic TI pair and block from structure at the original G and T

The seed, small odd-group alternatives and invariant Sylow selection need
only the normalization of V supplied by local structure. Their existing
proofs construct the same H, odd subgroup, pair core and canonical orbit.
The proved prime-order exclusion and the local block adapter then give all
clauses of CyclicLocalAnalysis, including its literal residual and action.

The last theorem discharges cyclicStep in the original local configuration
consumer using only Structural1222At at its own G,T. Natural recognition
and rigidity remain with their source owners; no structure outside that
ambient group and Sylow subgroup is assumed.
Source: Aschbacher–Smith, 12.2.21–24, printed pp.802–804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}

/-- Source 12.2.21–22 with structure only at the original G,T. The canonical
orbit and the selected pair retain all the original residual and action data. -/
theorem exists_invariantOddLocalAnalysis_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (hTI : IsTISubgroup V) :
    ∃ p H P U W g v, InvariantOddLocalAnalysis T L V d p H P U W g v := by
  have hTV := ((structural L h).2.2 V D).1
  obtain ⟨p, H, P, U, g, S⟩ := exists_cyclicConstructionSeed D A hTV hTI
  obtain ⟨P', U', g', v, R⟩ := S.invariantSelection_of_alternatives D A hTV hTI
    (S.small_odd_alternatives h D A hTV hTI)
  exact ⟨p, H, P', U', componentOrbit (H.pCoreIn 2 ⊓ V) H, g', v,
    R.invariantOddLocalAnalysis D A hTV hTI⟩

/-- Construct the full cyclic TI pair and linear block from the permitted
natural analysis and the same-G,T structural input available to the consumer. -/
theorem exists_cyclicLocalAnalysis_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  apply cyclicLocalAnalysis_of_invariant_odd_and_prime_steps_at h D structural A
    (exists_invariantOddLocalAnalysis_at h D structural A hTI)
  intro p H P U W g v S
  exact S.prime_order h D A ((structural L h).2.2 V D).1 hnone

/-- The actual parent local configuration consumer with cyclicStep discharged
by the local structural theorem. Natural recognition and rigidity retain their
original contracts and their independent source owners. -/
theorem localConfiguration_of_natural_and_rigidity_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (naturalStep : NoEscape L V → IsTISubgroup V →
      ∃ d, NaturalLocalAnalysis T L V d)
    (rigidityStep : ∀ d H P U, NaturalLocalAnalysis T L V d →
      CyclicLocalAnalysis T L V d H P U → NoEscape L V → IsTISubgroup V →
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) :
    ∃ d, SplitLinearConfiguration L V d :=
  localConfiguration_of_source_steps D naturalStep
    (fun _ A hn ht => exists_cyclicLocalAnalysis_at h D structural A hn ht)
    rigidityStep hnone hTI

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
