module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Generation
public import CFSG.Quasithin.ChapterE.Section06.Defs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Setup

/-!
# The doubled weak-closure setup

The full original normalizer orbit is normal in M. Its Sylow centralizer is
the intersection of O₂(LT) with its ambient centralizer, so LT normalizes it.
The original maximal-overgroup uniqueness then supplies every clause of E.6.1,
with V_M in place of V. No weak-closure escape or parameter bound is assumed.

Source: Aschbacher--Smith, 11.3.6, first paragraph, printed p.772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

omit [Finite G] in
theorem seed_le_fullModule : V ≤ fullModule L V := by
  rw [fullModule, Source.conjugateSpan, ← conjugateSpanBy_eq_iSup_conj]
  exact le_conjugateSpanBy _ _

include D in
omit [Finite G] in
theorem fullModule_ne_bot : fullModule L V ≠ ⊥ :=
  fun he => D.ne_bot (le_bot_iff.mp (seed_le_fullModule.trans he.le))

include D S in
theorem fullModule_sylow_centralizer_eq :
    (T : Subgroup G) ⊓ centralizer (fullModule L V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (fullModule L V : Set G) := by
  rw [← LocalGeometry.WeakClosure.seed_sylow_centralizer D S]
  exact le_antisymm
    (fun _ hx => ⟨⟨hx.1,centralizer_le seed_le_fullModule hx.2⟩,hx.2⟩)
    (fun _ hx => ⟨hx.1.1,hx.2⟩)

include D S in
theorem local_join_normalizes_fullModule_centralizer :
    L ⊔ (T : Subgroup G) ≤
      normalizer ((T : Subgroup G) ⊓ centralizer (fullModule L V : Set G) : Set G) := by
  change L ⊔ (T : Subgroup G) ≤ normalizer
    (((T : Subgroup G) ⊓ centralizer (fullModule L V : Set G) : Subgroup G) : Set G)
  rw [fullModule_sylow_centralizer_eq (D := D) (S := S)]
  apply le_trans _ Subgroup.inf_normalizer_le_normalizer_inf
  refine le_inf ?_ ?_
  · exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  · exact (sup_le L.le_normalizer D.sylow_normalizes_component).trans
      (normalizes_fullModule.trans (normalizer_le_normalizer_centralizer _))

theorem doubled_hypothesisE61 (d : Coordinates D S) :
    ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (fullModule L V) := by
  have hWM : fullModule L V ≤ (T : Subgroup G) := fullModule_le_sylow d
  refine ⟨S.source.simpleQTKE,LocalGeometry.Preliminary.normalizer_maximal D S,
    D.sylow_normalizes_component,fullModule_ne_bot (D := D),fullModule_elementary d,
    hWM,normal_subgroupOf_of_le_normalizer
      (D.sylow_normalizes_component.trans normalizes_fullModule),?_,?_⟩
  · intro g hg
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (normalizes_fullModule hg))
  · intro N hN hle
    have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
      S.source.simpleQTKE T S.source.maximal_faithful.1
    have hLT : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
      sup_le L.le_normalizer D.sylow_normalizes_component
    have hh := hu.normalizer_unique N hN
    have he : componentOrbit L (T : Subgroup G) = L :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
        D.sylow_normalizes_component) (le_componentOrbit L T)
    rw [he] at hh
    apply hh
    apply le_trans ?_ hle
    exact le_inf (le_inf hLT (hLT.trans normalizes_fullModule))
      (local_join_normalizes_fullModule_centralizer (D := D) (S := S))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
