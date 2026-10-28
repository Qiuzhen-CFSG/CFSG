module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.AugmentationSelectionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryFusionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedReciprocity

/-!
# The original ordinary-or-covered reduction with source consequences

The two-row augmentation argument constructs an actual escaping component
from nonsolvability of C_G(z). Apply the completed selected-component
classification at that K, with all original guards. Its linear-three or
ordinary-six geometry forces the original L/O2(L) to be ordinary A6.
Thus an original triple-cover quotient can only have solvable escaping
centralizers. No normalizer supplement, ordinary quotient or component
witness is supplied to this deduction.

Starting from the original chosen module with nonzero fixed part, the
final theorem constructs applicability and its augmentation marking.
It either supplies the ordinary quotient together with the Sylow-normalizer
and full ambient module-fusion clauses, or retains the triple cover and
constructs a solvable escaping omega centralizer. This is an actual source
reduction for the remaining normalizer and recognition assembly.

The initial geometry and fusion use same-G,T At inputs. The existing
selected-component model consumers still require universal Structural1222;
that premise is retained explicitly. The earlier 13.3.2/16 and independent
natural large-distance inputs also retain their producers. This theorem
does not prove full 13.4.1 or remove the final-D fixed-space premise.

Source: Aschbacher--Smith 13.4.4--6 and 13.4.10,
printed pp.897--898,907--909. The completed nonsolvable owner APIs are reused
without modification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Select an actual escaping component in either initial row. The completed
component geometries force the original quotient to be ordinary A6. -/
theorem ordinary_initial_quotient_of_nonsolvable_escape
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G))) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨K,hK,hfK,_,hHN,_,hKM,_⟩ := augmentation_exists_escaping_component_at
    h₀ h (structural G T) m h1332 hzT (fun he => hzL (he ▸ one_mem _)) hout hnonsolv
  have hindex := original_omega_fixed_index_at h₀ h (structural G T) D m earlier
  rcases selected_component_ordinary_or_linear hl h₀ h structural D m h1332
      fixed five covered h13316 hindex z hzT hzL hK hHN hKM hfK with hlin | hsix
  · obtain ⟨eK⟩ := hlin
    obtain ⟨_,_,hL,_⟩ := linear_component_geometry hl h₀ h structural modules
      D m h1332 fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
    exact hL
  · obtain ⟨eK⟩ := hsix
    obtain ⟨_,_,_,hL,_⟩ := ordinary_six_component_geometry h₀ h structural modules
      D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
    exact hL

/-- Original fixed-module source reduction: either the literal quotient by
O2(L) is A6 with full module-normalizer fusion, or it is the triple cover
and a constructed escaping omega
centralizer is solvable. No marking, index, selected component or ordinary
quotient is assumed. The universal structural premise is still needed by
the completed component-model consumers. -/
theorem fixed_module_ordinary_fusion_or_solvable_cover
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3) :
    (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      normalizer (T : Set G) ≤ normalizer (L : Set G) ∧
      ∀ (v : V) (w : G), w ∈ V → IsConj v.val w →
        ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w) ∨
      (Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
        ∃ z : V, z ≠ 1 ∧ z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
          z.val ∉ centralizer (L : Set G) ∧
          ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) ∧
          Group.IsSolvable (centralizer ({z.val} : Set G))) := by
  classical
  by_cases he : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
  · obtain ⟨eL⟩ := he
    exact Or.inl ⟨⟨eL⟩,ordinary_fixed_module_fusion_at hl h₀ D hfixed
      (structural G T) earlier h1332 fixed eL⟩
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  have hc := (original_quotient_rows D m h.quasisimple).resolve_left he
  obtain ⟨z,hz1,hzT,hzL,hout⟩ :=
    exists_nonfixed_omega_escape_at h₀ h (structural G T) D m earlier
  refine Or.inr ⟨hc,z,hz1,hzT,hzL,hout,?_⟩
  by_contra hnonsolv
  exact he (ordinary_initial_quotient_of_nonsolvable_escape hl h₀ h structural modules D m
    earlier h1332 fixed five covered h13316 z hzT hzL hout hnonsolv)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
