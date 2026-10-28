module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredRecognition
public import CFSG.Quasithin.Chapter13.Section05.Preparation.NaturalSix

/-!
# Applying fixed-core recognition to original 13.5 preparation

The original counterexample excludes Sp₆(2). The completed fixed-module
recognition implication therefore makes C_V(L) trivial, and the existing
natural-quotient constructor produces the same V and its invariant flag.
T-invariance is obtained from the retained structural theorem. Neither
hfixed nor a marked natural setup is a premise of this application.

The named earlier source inputs remain explicit; the 13.5 assembly owner
retains their discharge. Existing preparation APIs are unchanged.
Source: Aschbacher--Smith 13.4.1 and 13.5.2(3), pp.896,915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original counterexample has no fixed part in any selected module,
once the named preceding source inputs are supplied. -/
theorem original_fixed_space_eq_bot_of_earlier_sources
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Counterexample T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hfixed
  exact h₀.no_symplectic_six (fixed_module_recognition_of_earlier_sources hl (hypothesis1331 h₀)
    D hfixed structural modules earlier h1332 fixed five covered h13316)

/-- Apply the completed fixed-space exclusion to the original 13.5 natural-six
preparation. The fixed-space and T-invariance premises are discharged. -/
theorem exists_six_setup_of_earlier_sources
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Counterexample T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6))
    (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (ha : ∀ (l : L) v, a (D.chosenCentralAction l v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (e (QuotientGroup.mk' (centralCore L) l)) (a v)) :
    ∃ V₁ V₂ V₃ : Subgroup G,
      Nonempty (Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃
        (normalizer (L : Set G)) (normalizer (V₁ : Set G))) := by
  have h1 := hypothesis1331 h₀
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h1.qtke T h1332 h1.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h1.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h1.local_component |>.2⟩ (component_quotient_quasisimple h1332 h1.local_component)
  exact Section05.Preparation.exists_six_setup_of_fixed_quotient h₀ D e a ha
    ((structural G T L h).2.2 V D).1
    (original_fixed_space_eq_bot_of_earlier_sources hl h₀ D structural modules earlier
      h1332 fixed five covered h13316)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
