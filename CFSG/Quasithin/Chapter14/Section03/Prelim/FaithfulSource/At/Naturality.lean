module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.At.Classification
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.CommutatorInput.At
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.SourceAt

/-!
# The original chosen module after the faithful sieve

The family catalogue gives maximality of the original selected member; the
literal L₃(2) quotient gives quasisimplicity. Apply the completed guarded
12.4.2 fusion/commutator argument to the same chosen V. Its coordinates use
L → L/O₂(L), and the structural source gives T-invariance of V. This supplies
the actual higher-rank hypothesis without a separate maximality assumption.

The last theorem also connects the faithful sieve to the guarded preceding
13.1.7/13.3.2 source proof, retaining its genuine larger-linear exclusions.
The general A₅-module and Earlier1332CaseOneAt assembly remains with
qt-d-1332-source. Structural/module inputs and the rank-one exits retain their
original producers; no fixed-space or naturality premise replaces them.

Source: Aschbacher–Smith, 12.4.2, pp.812–816; 13.3.2(2–4), p.885;
14.3.4(3), p.990, and Hypothesis 12.8.1(1), pp.849–850.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter12.Section04.SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual selected member is maximal by the whole-family rigidity
argument, without presupposing maximality in Counterexample. -/
theorem faithfulMaximalLocal_of_source1332 (d : Counterexample T L)
    (source1332 : Source1332OneTwo T) : FaithfulMaximalLocal T L := by
  have hL := (faithfulLocalComponents_iff L).mp d.local_component
  exact ⟨(normal_maximal_of_source1332 d source1332 hL.1 hL.2).2, hL.2⟩

section Chosen
variable (d : Counterexample T L) (source1332 : Source1332OneTwo T)
    (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H))

include d source1332 hmany structural modules hmodel exits

/-- Clause (3) on the original chosen Irr⁺ member: T-invariance and natural
coordinates on V itself, with the literal quotient action retained. -/
theorem chosen_natural_of_sources_at :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      letI := D.elementary
      Nonempty (AmbientNaturalMarking L D.normalizes 3) := by
  have hmax := faithfulMaximalLocal_of_source1332 d source1332
  have h := (Counterexample.hypothesis1311 d).hypothesis1223 hmax
    (CaseOneSource.quotient_quasisimple hmodel)
  exact ⟨((structural L h).2.2 V D).1,
    CaseOneSource.slThreeNaturalMarking_of_counterexample_source_at
      d hmax D hmany structural modules hmodel exits⟩

/-- The literal higher-rank application with selected-member maximality
supplied by 13.3.2 and naturality supplied by the guarded 12.4.2 proof. -/
def higherRankHypothesis_of_sources_at :
    HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3 :=
  CaseOneSource.higherRankHypothesis_of_guarded_source_at d
    (faithfulMaximalLocal_of_source1332 d source1332) D hmany structural modules hmodel exits

end Chosen

/-- Connect the whole-family sieve to the actual preceding source proof at
G,T. The earlier larger-linear, unitary and ordinary/covered A₆ implications
remain explicit; the five-model catalogue and maximality are constructed. -/
theorem earlierFaithfulClassification_of_source_inputs_at (d : Counterexample T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (larger : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (Chapter1.XiQuotient I) n 2)
    (source13316 : Theorem13316At T) (source1381 : Theorem1381At T) :
    EarlierFaithfulClassification G (T : Subgroup G) :=
  earlierFaithfulClassification_of_sources_at d
    ((hypothesis1331 d).source1332OneTwo_of_source_inputs_at hmany structural modules larger)
    source13316 source1381

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
