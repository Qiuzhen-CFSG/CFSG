module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.MSActions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSOriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.Assembly
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniPairing

/-!
# The surviving original linear-three source alternative

Original 13.6.6 and 13.6.14–16 construct the MS pair. The first three
C.1.34 alternatives centralize the marked conjugate a, while the fifth
is excluded by the source central involution. Thus only case four remains.
If its Frattini centralizer D is nonabelian, the proved center-control and
large-Frattini-commutator results supply the literal checked-center identity.
The same marked-a argument then contradicts original 13.6.17.

Consequently the original configuration and the full C.1.34 alternatives
force case four with [D,D]=1. The final source assembly must supply the
intrinsic quotient marking, C.1.34 exhaustiveness and the opposing
nonabelianness theorem. No block recognition or action-placement premise
is added here; all MS, geometric and checked-action inputs are constructed.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, C.1.34,
printed pp.136–137, and 13.6.22, printed pp.932–933.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open ComponentSelection A5Module ComponentReduction InitialSieve
open SourceContainment
open MSSourceModels.NonabelianCenters MSSourceModels.NonabelianCenters.CaseFourQuotient
universe u
variable {G : Type u} [_root_.Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- Nonabelianness supplies the last checked-center identity in the fourth alternative. -/
theorem caseFour_centralizes_markedA_of_localConfiguration
    {M S : Subgroup G} {κ : GroupClass.{u}}
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hMS : LinearThreeMSPair κ K (Tv (T : Subgroup G) (markedV d.flag.module)) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : CaseFour K (Tv (T : Subgroup G) (markedV d.flag.module)) S e)
    (hne : let Q := msQ K (Tv (T : Subgroup G) (markedV d.flag.module))
      let D := Q ⊓ centralizer (frattiniIn Q : Set G)
      ⁅D,D⁆ ≠ ⊥) :
    K ≤ Gv (markedA d.flag.module) := by
  have hv : markedV d.flag.module ^ 2 = 1 := by
    rw [← (marked_orders d.flag.module).2]
    exact pow_orderOf_eq_one _
  have hp := (msPair_core_hypotheses hMS).2
  have hcenter := FrattiniCentralizer.CenterRadical.caseFour_checked_commutator_of_nonabelian
    (T : Subgroup G) (markedV d.flag.module) hK.1.1 hv hMS e h hne
    (caseFour_frattiniCommutatorLarge hMS e h)
  apply natural_section_centralizes_markedA_of_localConfiguration d c hp hK hn hLK hchar hTL e _ hcenter
  change HasSectionModel K (MSSourceModels.sourceU K) ⊥ (linearThreeActor e) BinaryLinearThree.W
  rw [caseFour_sourceU (msPair_core_hypotheses hMS).1 hp e h]
  exact h.2.2.2.2.2.1

theorem caseFour_of_original_source_msAlternatives
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
    (model : RankTwo.ReducedModel (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K)) :
    ∀ (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group),
      MSModuleAlternatives K (Tv (T : Subgroup G) (markedV d.flag.module))
        (Tv (T : Subgroup G) (markedV d.flag.module)) 1 (ZMod 2) e →
      MSSourceModels.NonabelianCenters.CaseFour K
        (Tv (T : Subgroup G) (markedV d.flag.module))
        (Tv (T : Subgroup G) (markedV d.flag.module)) e := by
  intro e hmodel
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke
    hm standing.counterexample hfusion
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz model).1
  have hMS := (linearThreeMSPair_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK e).1
  have hp := (MSSourceModels.NonabelianCenters.msPair_core_hypotheses hMS).2
  rcases msModule_centralizes_markedA_or_caseFour d c hp hK hn hLK hchar
      earlier.T_normalizes_L hK.1.2.2.1 le_rfl e hmodel with hc | hfour
  · exfalso
    have hnc := (SourceTransferFields.noncentrality_and_field_exclusions_original_source
      d V₃ earlier standing hm hfusion hform hfailure h1332 h63 K hK hL hz
      ChapterB.QuasisimpleSource.BinaryField.two).1 c.aPoint
    have hconj : ∃ g : G, (c.aPoint : G) = MulAut.conj g (markedZ d.flag.module) := by
      obtain ⟨g, hg⟩ := c.a_conjugate
      exact ⟨g, c.aPoint_val.trans hg.symm⟩
    apply hnc hconj c.a_checked_central
    simpa only [c.aPoint_val, Gv] using hc
  · exact hfour

/-- The original source hypotheses eliminate the nonabelian fourth alternative. -/
theorem caseFour_frattiniCentralizer_abelian_original_source
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
    (model : RankTwo.ReducedModel (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : CaseFour K (Tv (T : Subgroup G) (markedV d.flag.module))
      (Tv (T : Subgroup G) (markedV d.flag.module)) e) :
    let Q := msQ K (Tv (T : Subgroup G) (markedV d.flag.module))
    let D := Q ⊓ centralizer (frattiniIn Q : Set G)
    ⁅D,D⁆ = ⊥ := by
  by_contra hne
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke
    hm standing.counterexample hfusion
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz model).1
  have hMS := (linearThreeMSPair_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK e).1
  have hc := caseFour_centralizes_markedA_of_localConfiguration d c hK hn hLK hchar
    earlier.T_normalizes_L hMS e h hne
  have hnc := (SourceTransferFields.noncentrality_and_field_exclusions_original_source
    d V₃ earlier standing hm hfusion hform hfailure h1332 h63 K hK hL hz
    ChapterB.QuasisimpleSource.BinaryField.two).1 c.aPoint
  have hconj : ∃ g : G, (c.aPoint : G) = MulAut.conj g (markedZ d.flag.module) := by
    obtain ⟨g, hg⟩ := c.a_conjugate
    exact ⟨g, c.aPoint_val.trans hg.symm⟩
  apply hnc hconj c.a_checked_central
  simpa only [c.aPoint_val, Gv] using hc


/-- The exact surviving source case: the fourth MS alternative with abelian
Frattini centralizer. Its nonabelianness is the remaining independent source input. -/
theorem msAlternatives_original_source_reduction
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
    (model : RankTwo.ReducedModel (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K)) :
    ∀ (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group),
      MSModuleAlternatives K (Tv (T : Subgroup G) (markedV d.flag.module))
        (Tv (T : Subgroup G) (markedV d.flag.module)) 1 (ZMod 2) e →
      MSSourceModels.NonabelianCenters.CaseFour K
        (Tv (T : Subgroup G) (markedV d.flag.module))
        (Tv (T : Subgroup G) (markedV d.flag.module)) e ∧
      (let Q := msQ K (Tv (T : Subgroup G) (markedV d.flag.module))
       let D := Q ⊓ centralizer (frattiniIn Q : Set G)
       ⁅D,D⁆ = ⊥) := by
  intro e hmodel
  have hfour := caseFour_of_original_source_msAlternatives d V₃ earlier standing hm hfusion
    hform hfailure h1332 h63 hK hL hz model e hmodel
  exact ⟨hfour, caseFour_frattiniCentralizer_abelian_original_source d V₃ earlier standing hm
    hfusion hform hfailure h1332 h63 hK hL hz model e hfour⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
