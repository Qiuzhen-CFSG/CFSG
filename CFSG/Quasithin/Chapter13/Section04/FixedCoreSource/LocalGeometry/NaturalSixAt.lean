module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.RecognitionAssemblyAt
public import CFSG.Quasithin.Chapter13.Section05.Preparation.NaturalSix

/-!
# The original natural-six setup after fixed-core exclusion

Apply the assembled fixed-core implication to the actual chosen module.
The source counterexample excludes Sp6(2), so its fixed subgroup vanishes.
The multiple-overgroup guard constructs 12.2.13 from the same-G,T inputs.
The preserved quotient-coordinate construction then gives the actual natural
module and its invariant flag. No fixed-space hypothesis is supplied here.
Earlier Chapter12/13.3 and natural large-distance inputs remain explicit,
with final discharge owned by the original source/preparation assembly.
Source: Aschbacher--Smith 13.4.1 and 13.5.2--3, printed pp.896,915--916.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.Preparation
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Section08.SourceCompletion
open Chapter13.Section04.FixedCoreSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct the original natural-six flag with the fixed-space premise
removed by 13.4, retaining only the genuine preceding source inputs. -/
theorem exists_six_setup_of_fixed_quotient_source_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h : Counterexample T L)
    (D : ChosenModule T L V)
    (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6))
    (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (ha : ∀ (l : L) v, a (D.chosenCentralAction l v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (e (QuotientGroup.mk' (centralCore L) l)) (a v))
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3) :
    ∃ V₁ V₂ V₃ : Subgroup G,
      Nonempty (NaturalSetup T L V V₁ V₂ V₃
        (normalizer (L : Set G)) (normalizer (V₁ : Set G))) := by
  have h₀ := hypothesis1331 h
  have hfixed : V ⊓ centralizer (L : Set G) = ⊥ := by
    by_contra hf
    exact h.no_symplectic_six (LocalGeometry.isPSp_of_original_fixed_core_of_many_at
      hl h₀ D hf hmany structural modules h1332 fixed five covered h13316)
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
      h₀.local_component |>.2⟩ (Nonsolvable.component_quotient_quasisimple h1332 h₀.local_component)
  exact exists_six_setup_of_fixed_quotient h D e a ha ((structural L h12).2.2 V D).1 hfixed

end CFSG.Quasithin.Chapter13.Section05.Preparation
