module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryLocalAssembly
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OmegaIndex

/-!
# The original fixed-module premise in ordinary recognition

The preceding fixed-module clause 13.3.2 supplies the actual faithful
augmentation action on the chosen V. Its quotient is transported through
the literal central core to construct CoreMarking, preserving V and its
conjugation action. The source omega calculation gives the initial fixed
index two. Thus neither a marking nor an omega index is an extra input
to the ordinary recognition branch.

The remaining local inputs are N_G(L)=LT and normalizer fusion at applicable
cores; the earlier Chapter 12/13.3 and natural large-distance inputs also
remain explicit. The covered row and full source assembly remain separate
obligations in this task.
Source: Aschbacher--Smith 13.3.2(3), 13.4.1 and 13.4.3, pp.885,896--897.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct the literal five-dimensional marking from the original earlier fixed-module theorem. -/
theorem coreMarking_of_original_fixed
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) : Nonempty (CoreMarking D) := by
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  exact coreMarking_of_faithful_core_action D h.quasisimple a

/-- The conditional ordinary branch starts from the original nonzero fixed part, with its marking and omega index constructed. -/
theorem ordinary_recognition_of_fixed_module_sources
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hfusion : ∀ (A W : Subgroup G) (DA : ChosenModule T A W),
      CoreMarking DA → Hypothesis1331 T A →
      ∀ v : W, v ≠ 1 → ∀ w ∈ W, IsConj v.val w →
        ∃ n ∈ normalizer (W : Set G), MulAut.conj n v.val = w)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ClassicalGroup.IsPSp G 3 2 := by
  obtain ⟨m⟩ := coreMarking_of_original_fixed h₀ h D fixed hfixed
  exact ordinary_recognition_of_local_sources hl h₀ h structural modules D m h1332 fixed five
    covered h13316 (original_omega_fixed_index h₀ h structural D m earlier) hM hfusion eL earlier

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
