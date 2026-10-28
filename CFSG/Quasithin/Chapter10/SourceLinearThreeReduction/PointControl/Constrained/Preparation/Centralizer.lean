module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Action
public import Theory.GroupTheory.TwoFixedLinesIrreducible

/-!
# Centralizer control for both constrained orbit alternatives

A nonzero L₀-fixed layer of W=[V,L] is normalized by T₁=N_T(L).
The two-group fixed-point theorem produces a nonidentity vector fixed by
L₀T₁. Half-Sylow uniqueness controls its centralizer, and that vector
belongs to the literal seed C_W(C_T(v)), hence to VI. This proves the
ambient centralizer bound without assuming W≤VI or choosing coordinates.
The full-span alternative follows from the original moved normalizer bound.

Source: Aschbacher--Smith, 10.2.9, printed p.751, using 10.2.6(1).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The fixed-layer centralizer argument uses a nonzero vector fixed by the
half-Sylow, so it does not need the full moved module in the orbit. -/
theorem Context.centralizer_le_of_fixed_layer (c : Context D t v I)
    (hfixed : ⁅D.fullModule,L⁆ ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let F := ⁅D.fullModule,L⁆ ⊓ centralizer (localOrbit T L : Set G)
  have hRW : R ≤ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right).trans
      (source_moved_normalizer_local_containment D)
  have hRF : R ≤ normalizer (F : Set G) :=
    (le_inf hRW (inf_le_left.trans ((le_normalizer_componentOrbit L T).trans
      (normalizer_le_normalizer_centralizer _)))).trans inf_normalizer_le_normalizer_inf
  have hpF : IsPGroup 2 F := (source_original_full_moved_elementary D).isPGroup.to_le inf_le_left
  have hne := inf_centralizer_ne_bot_of_pGroups R F (T.isPGroup'.to_le inf_le_left) hpF hRF hfixed
  obtain ⟨w,hwne⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hwV : (w : G) ∈ D.fullModule :=
    (le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)) w.property.1.1
  have hwfix : (w : G) ∈ centralizer (halfJoin T L : Set G) := by
    have h : halfJoin T L ≤ centralizer ({(w : G)} : Set G) := by
      apply sup_le
      · intro x hx
        exact mem_centralizer_singleton_iff.mpr (w.property.1.2 x hx)
      · intro x hx
        exact mem_centralizer_singleton_iff.mpr (w.property.2 x hx)
    intro x hx
    exact mem_centralizer_singleton_iff.mp (h hx)
  have hwU : (w : G) ∈ orbitModule D v I := by
    apply le_conjugateSpanBy _ _
    refine ⟨w.property.1.1,?_⟩
    exact centralizer_le (le_inf inf_le_left c.escaping.sylow_normalizes) w.property.2
  exact (centralizer_le (Set.singleton_subset_iff.mpr hwU)).trans
    (fixed_element_centralizer_le_of_halfSylowUnique D c.escaping.half_unique hwV
      (fun h => hwne (Subtype.ext h)) hwfix)

/-- The full-span alternative of the same source centralizer argument. -/
theorem Context.centralizer_le_of_moved_le (c : Context D t v I)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal :=
  (centralizer_le hspan).trans
    ((Subgroup.centralizer_le_normalizer _).trans c.escaping.moved_normalizer)

/-- The two source alternatives suffice on the literal orbit module. -/
theorem Context.centralizer_le_of_orbit_alternative (c : Context D t v I)
    (ha : ⁅D.fullModule,L⁆ ≤ orbitModule D v I ∨
      ⁅D.fullModule,L⁆ ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal := by
  rcases ha with hspan | hfixed
  · exact c.centralizer_le_of_moved_le hspan
  · exact c.centralizer_le_of_fixed_layer hfixed

end CFSG.Quasithin.Chapter10.PointControl.Constrained
