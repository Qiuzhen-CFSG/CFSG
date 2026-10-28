module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SelectedOutside
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableNormalizerSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryFusionAssembly

/-!
# Ordinary fixed-core recognition with the normalizer supplement discharged

The selected-component source calculation makes the actual normalizer
residual a {2,3}-group. The ordinary action kernel is three-free, so the
residual is a two-group. Its two-perfectness makes it trivial and yields
N_G(L) = LT. The solvable branch supplies the same equality from its
constructed local product. Thus the ordinary recognition consumer no
longer assumes a normalizer supplement. Its established terminal argument
uses nonsolvability at every escaping weight under negated recognition.

Starting with the original chosen module and nonzero fixed part, the final
theorem reduces 13.4.1 to recognition or the actual triple-cover quotient
with a constructed solvable escaping centralizer. The covered recognition
and remaining earlier-source discharge are still required for full 13.4.1.
The universal structural and recognition inputs are retained where the
existing transitive consumers still require them; they are not inferred
from At inputs. Existing public APIs remain unchanged.
Source: Aschbacher--Smith 13.4.6(4), 13.4.8--17, pp.898,904--915.
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

/-- The selected-component prime-set control and the ordinary three-free
kernel force the literal normalizer residual to vanish. -/
theorem ordinary_nonsolvable_normalizer_residual_eq_bot
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
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G))) :
    normalizerActionResidual L V = ⊥ := by
  have h23 := nonsolvable_normalizer_residual_twoThree hl h₀ h structural modules D m earlier
    h1332 fixed five covered h13316 z hzT hzL hout hnonsolv
  have hR : normalizerActionResidual L V ≤
      normalizer (L : Set G) ⊓ centralizer (V : Set G) := map_subtype_le _
  have h3 : ¬ 3 ∣ Nat.card (normalizerActionResidual L V) := by
    intro hd
    exact ordinary_normalizer_kernel_three_free_at h (structural G T) D m eL
      (hd.trans (card_dvd_of_le hR))
  have htwo := isPGroup_two_of_isPiGroup_twoThree h23 h3
  have hp := (normalizer_action_residual_at h (structural G T) D m).2.2.2.1
  have hid := hp.hom_eq_one_of_isPGroup htwo (MonoidHom.id (normalizerActionResidual L V))
  apply le_bot_iff.mp
  intro x hx
  exact mem_bot.mpr (congrArg (fun a : normalizerActionResidual L V => a.val)
    (DFunLike.congr_fun hid ⟨x,hx⟩))

/-- Both original branches now prove M=LT. The nonsolvable case uses the
selected component's own action, before any full-centralizer identification. -/
theorem ordinary_normalizer_supplement_of_sources
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) := by
  classical
  obtain ⟨z,_,hzT,hzL,hout⟩ := exists_nonfixed_omega_escape_at h₀ h (structural G T) D m
    (earlier G T)
  by_cases hs : Group.IsSolvable (centralizer ({z.val} : Set G))
  · have hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
        ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w :=
      fun v _ w hw hc => ordinary_core_normalizer_fusion_at hl h₀ h (structural G T)
        D m (earlier G T) eL v w hw hc
    exact ordinary_solvable_normalizer_supplement hl h₀ h structural D m eL z hzT hzL hout
      hfusion hs (original_omega_fixed_index_at h₀ h (structural G T) D m (earlier G T))
  · have hb := ordinary_nonsolvable_normalizer_residual_eq_bot hl h₀ h structural modules D m
      (earlier G T) h1332 fixed five covered h13316 eL z hzT hzL hout hs
    have hm := (normalizer_action_residual_at h (structural G T) D m).1
    simpa only [hb,sup_bot_eq] using hm

/-- Ordinary 13.4.1 recognition with the normalizer supplement proved from
preceding source inputs. The existing terminal consumer uses nonsolvability
at every escaping weight under negated recognition. -/
theorem ordinary_recognition_without_normalizer_supplement
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ClassicalGroup.IsPSp G 3 2 := by
  have hM := ordinary_normalizer_supplement_of_sources hl h₀ h structural modules D m h1332
    fixed five covered h13316 eL earlier
  exact ordinary_recognition_of_fusion_sources hl h₀ h structural modules D m h1332
    fixed five covered h13316 (original_omega_fixed_index_at h₀ h (structural G T) D m
      (earlier G T)) hM eL earlier

/-- The original nonzero fixed part now gives either recognition or an
actual covered quotient and solvable escaping omega centralizer. The ordinary
branch has no remaining local normalizer, fusion or amalgam premise. -/
theorem fixed_module_recognition_or_solvable_cover
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3) :
    ClassicalGroup.IsPSp G 3 2 ∨
      (Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
        ∃ z : V, z ≠ 1 ∧ z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
          z.val ∉ centralizer (L : Set G) ∧
          ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) ∧
          Group.IsSolvable (centralizer ({z.val} : Set G))) := by
  rcases fixed_module_ordinary_fusion_or_solvable_cover hl h₀ D hfixed structural modules
      (earlier G T) h1332 fixed five covered h13316 with ⟨⟨eL⟩,_,_⟩ | hc
  · have hstar := Section03.Noncentrality.source1332_faithful_maximal
      h₀.qtke T h1332 h₀.local_component
    have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
      h₀.hypothesis1311.hypothesis1223
        ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
          h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
    obtain ⟨m⟩ := coreMarking_of_original_fixed h₀ h D fixed hfixed
    exact Or.inl (ordinary_recognition_without_normalizer_supplement hl h₀ h structural
      modules D m h1332 fixed five covered h13316 eL earlier)
  · exact Or.inr hc

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
