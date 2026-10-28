module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Contracts
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.Geometry

/-!
# Consequences of the literal half-Sylow uniqueness theorem

Uniqueness for L₀N_T(L) controls both N_G(L) and N_G([V,L]). The first
normalizer has nontrivial two-core, and the second normalizes a nontrivial
elementary subgroup. The same uniqueness controls every nonidentity vector
fixed by L₀N_T(L), without requiring it to be fixed by all of T.

These implications supply the normalizer and fixed-vector steps of
10.2.9 from precisely the earlier 10.2.6(1) premise. They do not prove that
premise. Source: Aschbacher--Smith, 10.2.6 and 10.2.9, pp.748--750.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The half-join lies in the stabilizer of both the original component
and its full moved module. -/
theorem halfJoin_le_stabilizer
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    halfJoin T L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  sup_le (le_inf (localOrbit T L).le_normalizer
    (source_nonnormal_orbit_le_normalizer D hn))
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right)

/-- Source 10.2.6(1) supplies the component-normalizer clause of (2). -/
theorem component_normalizer_le_of_halfSylowUnique
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hhalf : HalfSylowUnique D) : normalizer (L : Set G) ≤ D.maximalLocal := by
  obtain ⟨M,hM,hNM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (normalizer (L : Set G)) (source_component_normalizer_core_ne_bot D)
  exact (hhalf M hM (((halfJoin_le_stabilizer D hn).trans inf_le_right).trans hNM)) ▸ hNM

/-- Source 10.2.6(1) supplies the moved-normalizer clause of (2), without
a point-centralizer assumption or an A₅ marking. -/
theorem moved_normalizer_le_of_halfSylowUnique
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hhalf : HalfSylowUnique D) :
    normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal :=
  normalizer_le_of_unique_maximalTwoLocal hhalf
    (source_original_full_moved_elementary D).isPGroup (source_full_moved_ne_bot D)
    ((halfJoin_le_stabilizer D hn).trans (source_moved_normalizer_local_containment D))

/-- The fixed-vector case used at the start of 10.2.9: fixation by the
half-join suffices; fixation by the entire Sylow group is unnecessary. -/
theorem fixed_element_centralizer_le_of_halfSylowUnique
    (hhalf : HalfSylowUnique D) {v : G}
    (hv : v ∈ D.fullModule) (hvne : v ≠ 1)
    (hfix : v ∈ centralizer (halfJoin T L : Set G)) :
    centralizer ({v} : Set G) ≤ D.maximalLocal := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hp : IsPGroup 2 (zpowers v) :=
    (D.fullModule_elementary hu).isPGroup.to_le (zpowers_le.mpr hv)
  have hne : zpowers v ≠ ⊥ := fun he => hvne (mem_bot.mp (he ▸ mem_zpowers v))
  have hc : halfJoin T L ≤ centralizer (zpowers v : Set G) :=
    le_centralizer_iff.mpr (zpowers_le.mpr hfix)
  rw [show centralizer ({v} : Set G) = centralizer (zpowers v : Set G) by
    rw [zpowers_eq_closure,centralizer_closure]]
  exact (Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_of_unique_maximalTwoLocal hhalf hp hne
      (hc.trans (Subgroup.centralizer_le_normalizer _)))

/-- The opposite factor is a subgroup of the same original full module. -/
theorem partner_le_fullModule {t : G} (ht : t ∈ (T : Subgroup G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ D.fullModule := by
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have he : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht))
  exact (map_mono hWV).trans_eq he

end CFSG.Quasithin.Chapter10.PointControl
