module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.At.Naturality
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.SourceAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.OriginalBranch

/-!
# The faithful sieve in the original HS and Rudvalis branches

The whole-family classification at G,T supplies the faithful-component
premise of the completed guarded HS and Rudvalis source arguments. In the
Rudvalis branch, the actual chosen module also receives its higher-rank
hypothesis from the preceding catalogue and guarded naturality proof.
The original invariant flag, point, seed and residual alternatives are kept.

The HS branch retains the independent Earlier1332CaseOneAt assembly and
I.4.8 recognition. The Rudvalis branch retains the original uniqueness,
A₅-module, residual-alternative and alternating-recognition inputs. Their
existing owners, and the earlier structural/unitary/A₆ producers, still owe
those source proofs. These applications discharge faithful classification;
they do not assert unconditional recognition or completion of Theorem D.

Source: Aschbacher–Smith, 14.3.4, p.990; 14.3.31–33, pp.1002–1005;
14.4.14, p.1012; 14.7.52–75, pp.1065–1078, and I.4.8, p.418.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04 Chapter14.Section07.LocalStructure
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter12.Section04.SmallFusion
open Chapter13.Section03.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

section HS
variable (d : Counterexample T L) (source1332 : Source1332OneTwo T)
    (source13316 : Theorem13316At T) (source1381 : Theorem1381At T)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU ≠ F.Vi 1)
include d source1332 source13316 source1381 earlier hq chosen structural alternatives hne hZ

/-- The actual HS1--HS2 type on the same seed and point, after the faithful
sieve; both local and overgroup structures come from their guarded proofs. -/
theorem higmanSims_type_of_sources_at :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  CaseOneHS.type_of_source_at d earlier hq chosen structural alternatives F hne
    (earlierFaithfulClassification_of_sources_at d source1332 source13316 source1381) hZ

/-- Apply the independent I.4.8 recognition to the literal HS source branch. -/
theorem higmanSims_of_sources_at (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := higmanSims_type_of_sources_at d source1332 source13316 source1381
    earlier hq chosen structural alternatives F hne hZ
  exact recognition G ⟨z, V, hz⟩

/-- The faithful sieve supplies the HS row of the original D-model consumer. -/
theorem higmanSims_theoremDModel_of_sources_at (recognition : HigmanSims.Recognition.{u}) :
    ClassificationModels.IsTheoremDModel G :=
  .exceptional (.sporadic .hs (by simp)
    (higmanSims_of_sources_at d source1332 source13316 source1381
      earlier hq chosen structural alternatives F hne hZ recognition))

end HS

section Rudvalis
open CriticalFusion.Source CriticalFusion.SourceConstruction
variable (d : Counterexample T L) (source1332 : Source1332OneTwo T)
    (source13316 : Theorem13316At T) (source1381 : Theorem1381At T)
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
    (F : InvariantFlag T V 3) (hab : IsMulCommutative F.U)
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (five : OriginalAlternatingFiveModules1332At T L)
    (h52 : AlternatingResidual F ∨ G2Residual F)
    (h40 : AlternatingResidual F → NaturalRecognition F)
include d source1332 source13316 source1381 D hmany structural modules hmodel exits
  hab hunique five h52 h40

/-- Construct Data through the original residual branches and recognize the
actual Rudvalis carrier. Both faithful classification and the higher-rank
hypothesis are supplied by preceding source arguments on this same module. -/
theorem rudvalis_of_sources_at : Nonempty (G ≃* Rudvalis.Model) :=
  SourceEndgame.SourceAssembly.FullSource.source_rudvalis_of_original_branches_at d
    (higherRankHypothesis_of_sources_at d source1332 D hmany structural modules hmodel exits)
    hab hunique structural
    (earlierFaithfulClassification_of_sources_at d source1332 source13316 source1381)
    five h52 h40

/-- The literal Rudvalis row of D, with the original flag and all independent
recognition and residual source premises retained. -/
theorem rudvalis_theoremDModel_of_sources_at : ClassificationModels.IsTheoremDModel G :=
  SourceEndgame.SourceAssembly.FullSource.source_theoremDModel_of_original_branches_at d
    (higherRankHypothesis_of_sources_at d source1332 D hmany structural modules hmodel exits)
    hab hunique structural
    (earlierFaithfulClassification_of_sources_at d source1332 source13316 source1381)
    five h52 h40

end Rudvalis
end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
