module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.MSActions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.MinimalIntrinsic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.CheckedCenterSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.SourceModels
/-!
# The original binary linear-three exclusion in 13.6.22

The minimum with the same star image retains the original moving line and
has intrinsic quotient L₃(2). Its genuine MS input splits directly into an
abelian core, distance four, and larger distance. These cases supply the
natural or doubled-natural quotient of U=[Z(O₂(K)),K], together with the
literal checked-center identity [Z₀,K]=U.

The source moving line fixes the correct parabolic residual, giving equal
fixed subgroups for Lᵥ and K. Checked averaging then makes K centralize the
same marked conjugate a that original13.6.17 says it does not centralize.
The final theorem excludes the original plus quotient L₃(2), including the
minimal replacement, without assuming any C.1.34 classification output.

Only the independently preceding prescribed critical-path replacement from
MS93(4.4.4) remains explicit, at the actual large-distance MS inputs.
Source: Aschbacher--Smith 13.6.22, printed pp.932--933; MS93 sections4--7.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- Actual natural or doubled coefficient models suffice for the marked-a endgame. -/
private theorem false_of_original_source_center_models
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hmodels : (∃ m : ConjugationQuotientModel K (BinaryRankTwo.sourceU K) BinaryLinearThree.W,
        Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K) ∨
      (∃ m : ConjugationQuotientModel K (BinaryRankTwo.sourceU K)
        (BinaryLinearThree.W.prod BinaryLinearThree.W),
        Function.Surjective m.actor ∧ m.actor.ker = pCore 2 K))
    (hcenter : ⁅BinaryRankTwo.CenterPreimage.sourceZ0 K (markedV d.flag.module) hK.1.1,K⁆ =
      BinaryRankTwo.sourceU K) : False := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke
    hm standing.counterexample hfusion
  have hMS := (linearThreeMSPair_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK e).1
  have hp := (MSSourceModels.NonabelianCenters.msPair_core_hypotheses hMS).2
  obtain ⟨dL⟩ := center_sourceLineData_of_localConfiguration d c hp hK hn hLK hchar
    earlier.T_normalizes_L
  have hc : K ≤ Gv (markedA d.flag.module) := by
    rcases hmodels with ⟨m,hf,hker⟩ | ⟨m,hf,hker⟩
    · exact center_centralizes_markedA_of_localConfiguration d c hp hK hn hLK hchar
        earlier.T_normalizes_L (MSSourceModels.sourceU_elementary_of_model hp m) hcenter
        (natural_model_source_centralizer_eq dL m hf hker)
    · exact center_centralizes_markedA_of_localConfiguration d c hp hK hn hLK hchar
        earlier.T_normalizes_L (MSSourceModels.sourceU_elementary_of_model hp m) hcenter
        (doubled_model_source_centralizer_eq dL m hf hker)
  have hnc := (SourceTransferFields.noncentrality_and_field_exclusions_original_source
    d V₃ earlier standing hm hfusion hform hfailure h1332 h63 K hK hL hz
    ChapterB.QuasisimpleSource.BinaryField.two).1 c.aPoint
  have hconj : ∃ g : G, (c.aPoint : G) = MulAut.conj g (markedZ d.flag.module) := by
    obtain ⟨g,hg⟩ := c.a_conjugate
    exact ⟨g,c.aPoint_val.trans hg.symm⟩
  apply hnc hconj c.a_checked_central
  simpa only [c.aPoint_val,Gv] using hc

/-- The genuine original binary component is impossible. Every model and center
premise is discharged; prescribed critical-path replacement is the sole MS input. -/
theorem binary_false_original_source_of_replacement
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (replacement : ∀ (i : BinaryMS.Input KnownSimple.IsKnownSimple
      (K.subgroupOf (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module)))
      ((Tv (T : Subgroup G) (markedV d.flag.module)).subgroupOf
        (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module))))
      (t : BinaryMS.MS93.InputSetup i),
      BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : BinaryMS.MS93.DistanceEight.PathCentrality.CriticalPath
        t.reduction.radical t.geometry a a'),
      BinaryMS.MS93.DistanceEight.PathCentrality.HasTurnConjugators _ p →
      BinaryMS.MS93.DistanceEight.PathCentrality.PrescribedReplacement _ p) : False := by
  have hMS := (linearThreeMSPair_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK e).1
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  let i := MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization.inputOfProductOddIndex
    hMS e
    (MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization.joinProduct_of_normalizes hn)
    (MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization.oddIndex_of_sylow
      hMS hK.1.2.2.1)
  have hmodels := source_models_of_replacement i (replacement i)
  apply false_of_original_source_center_models d V₃ earlier standing hm hfusion hform
    hfailure h1332 h63 hK hLK hL hz e
  · rcases hmodels with hnatural | hdouble
    · exact Or.inl (MSSourceModels.source_model_of_join K
        (Tv (T : Subgroup G) (markedV d.flag.module)) hnatural)
    · exact Or.inr (MSSourceModels.source_model_of_join K
        (Tv (T : Subgroup G) (markedV d.flag.module)) hdouble)
  · have hv : markedV d.flag.module ^ 2 = 1 := by
      rw [← (marked_orders d.flag.module).2]
      exact pow_orderOf_eq_one _
    exact checked_commutator_of_replacement hK hv hn hMS e (replacement i)

/-- The original 13.6.22 binary linear-three exclusion, including its genuine
minimal equal-star replacement. Only prescribed MS replacement remains. -/
theorem not_plus_linearThree_original_source_of_replacement
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (replacement : ∀ (K₀ : Subgroup G), K₀ ≤ K →
      K₀ ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) →
      ∀ (i : BinaryMS.Input KnownSimple.IsKnownSimple
        (K₀.subgroupOf (K₀ ⊔ Tv (T : Subgroup G) (markedV d.flag.module)))
        ((Tv (T : Subgroup G) (markedV d.flag.module)).subgroupOf
          (K₀ ⊔ Tv (T : Subgroup G) (markedV d.flag.module))))
        (t : BinaryMS.MS93.InputSetup i),
        BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry →
        4 < t.geometry.b t.reduction.radical → ∀ {a a'}
        (p : BinaryMS.MS93.DistanceEight.PathCentrality.CriticalPath
          t.reduction.radical t.geometry a a'),
        BinaryMS.MS93.DistanceEight.PathCentrality.HasTurnConjugators _ p →
        BinaryMS.MS93.DistanceEight.PathCentrality.PrescribedReplacement _ p) :
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* BinaryLinearThree.Group) := by
  rintro ⟨e⟩
  obtain ⟨K₀,hle,hY,_hW,hLK,⟨e₀⟩,_hMS,_hprod⟩ :=
    exists_intrinsic_model_and_msPair_original_source d V₃ earlier standing hm hfusion
      h1332 h63 hK hL hz e
  exact binary_false_original_source_of_replacement d V₃ earlier standing hm hfusion hform
    hfailure h1332 h63 hY hLK hL hz e₀ (replacement K₀ hle hY)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
