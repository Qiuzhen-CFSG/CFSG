module
public import CFSG.Quasithin.Chapter10.SourceA5ProperSeedPassage
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.Completion
public import CFSG.Quasithin.Chapter10.SourceA5ConjugateIntersection
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureEndgame

/-!
# Point control and weak closure in the original proper-seed branch

The proper-seed passage supplies irreducibility and crossed centralization
on the original moved module. The all-vector Sylow theorem then discharges
point Sylow promotion. The resulting point-centralizer control feeds the
original trivial-intersection and weak-closure arguments.

The actual local cubic bound, proper-seed branch, earlier Baumann normalizer
containment and marked component inspection remain with their independent
source producers. No separate full cubic, full/local, irreducibility,
cross-centralization, fixed-kernel or Sylow-promotion premise is required.

Source: Aschbacher--Smith D.3.5--9 and 10.2.9--12,
printed pp.195--201 and 750--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
  (hD : D.IsMinimalFullModule)
  (hproper : D.seed ≠ D.moduleSubgroup)
  (hlocal : SourceLocalModuleCubicBound D)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  (h1021 : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
  (hinspect : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v)

include D e hn ht htn hD hproper hlocal hmany h1021 hinspect

/-- Original point-centralizer control with the proper-seed and all-vector
Sylow arguments assembled on the same fundamental setup. -/
theorem source_a5_proper_seed_point_centralizers :
    ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal := by
  obtain ⟨_,hi,hcross,_⟩ :=
    source_a5_original_proper_seed_control D e hn ht htn hD hproper hlocal hmany
  exact source_a5_moved_point_centralizers_of_irreducible_inspection
    D e hi h1021 ht htn hcross hinspect

/-- The original moved module intersects each outside conjugate trivially. -/
theorem source_a5_proper_seed_inf_conjugate_eq_bot
    {g : G} (hg : g ∉ D.maximalLocal) :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ := by
  obtain ⟨_,_,hcross,_⟩ :=
    source_a5_original_proper_seed_control D e hn ht htn hD hproper hlocal hmany
  exact source_a5_moved_inf_conjugate_eq_bot D e hn t ht hcross
    (source_a5_proper_seed_point_centralizers D e hn ht htn hD hproper hlocal
      hmany h1021 hinspect)
    (source_a5_component_normalizer_le D e hn) hg

/-- The actual weak-closure lower bound no longer has independent module
irreducibility, crossed action or point-centralizer premises in this branch. -/
theorem source_a5_proper_seed_globalW_gt_one :
    1 < globalW D.fullModule (T : Subgroup G) := by
  obtain ⟨_,hi,hcross,_⟩ :=
    source_a5_original_proper_seed_control D e hn ht htn hD hproper hlocal hmany
  exact source_a5_globalW_gt_one D e hi hn ht htn hcross
    (source_a5_proper_seed_point_centralizers D e hn ht htn hD hproper hlocal
      hmany h1021 hinspect)

end CFSG.Quasithin.Chapter10
