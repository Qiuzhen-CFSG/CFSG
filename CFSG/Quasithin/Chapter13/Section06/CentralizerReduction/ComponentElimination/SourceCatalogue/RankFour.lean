module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue.ReducedSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SevenExclusion
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.OriginalContradiction

/-!
# The original centralizer endgame with its group catalogue discharged

The complete offender classification constructs the selected component's
seven-model list. The original A₇ quotient exclusion removes that row.
The four remaining small-quotient exclusions leave exactly SL₄(2) or SL₅(2),
so the proved orthogonal endgame yields nonsingular centralizer containment.

The four small rows are precisely the independent 13.6.22 reconstruction
obligations. This assembly removes the model catalogue premise and the
already proved A₇ exclusion; it does not assert those four inputs.
Source: Aschbacher–Smith 13.6.20–23 and the concluding paragraph, pp.931–933.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

private theorem linear_four_or_five_of_reduced {Q : Type*} [Group Q]
    (h : RankTwo.ReducedModel Q)
    (h3 : ¬ Nonempty (Q ≃* SL(3,ZMod 2)))
    (h6 : ¬ Nonempty (Q ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
    (hg : ¬ Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2))))
    (hc : ¬ Nonempty (Q ≃* Atlas.Codes.HexEvenAutomorphisms))
    (h7 : ¬ Nonempty (Q ≃* alternatingGroup (Fin 7))) :
    Nonempty (Q ≃* SL(4,ZMod 2)) ∨ Nonempty (Q ≃* SL(5,ZMod 2)) := by
  cases h with
  | linear n hn e =>
    have he := e.map fun e => e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega))
    have hn' : n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn' with rfl | rfl | rfl
    · exact (h3 he).elim
    · exact Or.inl he
    · exact Or.inr he
  | symplectic e => exact (h6 e).elim
  | g2 e => exact (hg e).elim
  | ahat6 e => exact (hc e).elim
  | a7 e => exact (h7 e).elim

/-- The literal centralizer conclusion now requires only the four remaining
small quotient exclusions, with both B.5 and the original A₇ branch supplied. -/
theorem centralizer_le_normalizer_of_four_small_exclusions
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      RankTwo.LocalApplication.SourceHypothesis S I →
        omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (hsmall : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G) →
      ∀ K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module),
      let Q := plusImage K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz K
      (¬ Nonempty (Q ≃* SL(3,ZMod 2))) ∧
      (¬ Nonempty (Q ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) ∧
      (¬ Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2)))) ∧
      (¬ Nonempty (Q ≃* Atlas.Codes.HexEvenAutomorphisms))) :
    Gv (markedV d.flag.module) ≤ normalizer (V : Set G) := by
  by_contra hfailure
  apply hfailure
  apply SourceOrthogonal.centralizer_le_normalizer_of_original_reduced_models
    d V₃ earlier standing hm hfusion hform h1332 h63 hL hz
  intro K hK
  obtain ⟨h3,h6,hg,hc⟩ := hsmall hfailure K hK
  exact linear_four_or_five_of_reduced
    (reduced_model_original_source d V₃ earlier standing hm hfusion hform hfailure
      h1332 h63 K hK hL hz) h3 h6 hg hc
    (SourceSmallModels.not_alternating_plus_original_source d V₃ earlier standing hm
      hfusion hform hfailure h1332 h63 hK hL hz)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
