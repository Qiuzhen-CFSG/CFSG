module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications
public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.MaximalReduction

/-!
# Same-ambient applications of the structural source theorem

The original faithful member is identified with its maximal overgroup before
applying the local structural theorem. Thus 13.3.2 receives normalization of
every actual faithful member, and 13.1.2 receives an actual invariant chosen
module, its separate seven-case classification and an escaping centralizer.
The Chapter14 section-action kernel uses the same original chosen module.

Normalization, FSU, module classification and recognition remain independent
source inputs. No universal implication is manufactured from local data.
Source: Aschbacher--Smith, 12.2.6, 13.1.2, 13.3.2 and 14.7.70.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

namespace Structural1222At
variable (structural : Structural1222At KnownSimple.IsKnownSimple T)
  {L V : Subgroup G} (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
include structural h

/-- The original N(L) is the unique maximal two-local over LT, using full A/C. -/
theorem maximal_unique :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
    ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) :=
  h.toHypothesis1221.sylow_normalized_maximal_unique (structural L h).1
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)

/-- The full ambient normalizer of the same V lies in N(L). -/
theorem chosen_normalizer_le (D : ChosenModule T L V) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  let := D.elementary
  exact normalizer_le_of_unique_maximalTwoLocal (structural.maximal_unique h).2
    (IsElementaryAbelian.isPGroup 2 V) D.ne_bot
    (sup_le D.normalizes ((structural L h).2.2 V D).1)

/-- Original 12.2.6 for each nonzero subgroup of this chosen V. -/
theorem intersection_normalizer (D : ChosenModule T L V)
    {U H : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V)
    (hH : H ≤ normalizer (U : Set G)) :
    H ⊓ normalizer (L : Set G) = H ⊓ normalizer (V : Set G) :=
  inf_eq_inf_normalizer_of_trivial_intersections ((structural L h).2.2 V D).2.2.1
    (structural.chosen_normalizer_le h D) hU hUV hH

end Structural1222At

namespace SourceAssembly.At
open Chapter13.Section01 Chapter13.Section03.SourceClassification
open Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

/-- The genuine 13.3.2(1--2) consumer only needs source structure at G,T.
The refined five-model catalogue and quasisimplicity remain separate inputs. -/
theorem source1332OneTwo_of_maximal_models
    (h : Hypothesis1311 T)
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (models : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I))
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    Source1332OneTwo T := by
  intro K hK
  obtain ⟨hk, hm⟩ := faithful_hypothesis1223_of_maximal_models h quasisimple models hK
  exact ⟨(structural K hk).1, hm⟩

/-- The actual starred-family placement consumes the local catalogue. -/
theorem XiF_subset_XiStarF
    (h : Hypothesis1311 T)
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (models : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I))
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    Chapter1.XiF G (T : Subgroup G) ⊆ Chapter1.XiStarF G (T : Subgroup G) :=
  source_XiF_subset_XiStarF h.simpleQTKE T
    (source1332OneTwo_of_maximal_models h quasisimple models structural)

/-- Source 13.1.2 eliminates all three global recognition alternatives
using the original ambient exclusions, without changing L or V. -/
theorem centralizer_escape (recognition : Theorem12213At KnownSimple.IsKnownSimple T)
    (h : Hypothesis1311 T) {L V : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (D : ChosenModule T L V) :
    ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  rcases recognition L V (h.hypothesis1223 hL hq) D with
    hv | ⟨d, hd, _, he⟩ | ⟨_, he⟩ | ⟨_, he⟩
  · exact hv
  · exact (h.no_linear (d + 1) (by rcases hd with rfl | rfl <;> omega) he).elim
  · exact (h.no_A9 he).elim
  · exact (h.no_M24 he).elim

/-- A classified invariant module and escape for the original Chapter13
member. Each of the three distinct Chapter12 implications is used. -/
theorem exists_classified_chosen_escape
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (recognition : Theorem12213At KnownSimple.IsKnownSimple T)
    (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    ∃ (V : Subgroup G) (D : ChosenModule T L V),
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      ModuleAlternatives1222 D ∧
      ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  have hs := h.hypothesis1223 hL hq
  obtain ⟨V, ⟨D⟩⟩ := (structural L hs).2.1
  exact ⟨(structural L hs).1, V, D, ((structural L hs).2.2 V D).1,
    modules L V hs D, centralizer_escape recognition h hL hq D⟩

/-- The literal section-action kernel in 14.7.70, from the ambient-local
structural input. The action, section, and two-core maps are unchanged. -/
theorem sectionCentralizer
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {L V : Subgroup G} {F : Section08.InvariantFlag T V 3} {W : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    (d : Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data T L V F W) :
    d.SectionCentralizer :=
  sectionCentralizer_of_sylow_invariance d
    ((structural L d.natural.source).2.2 V d.natural.chosen).1

end SourceAssembly.At
end CFSG.Quasithin.Chapter12.Section02
