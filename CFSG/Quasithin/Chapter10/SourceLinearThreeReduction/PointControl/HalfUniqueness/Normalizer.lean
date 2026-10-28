module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Definitions
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.PushingInput

/-!
# Two source routes to the half-Sylow normalizer bound

The core O₂(L₀T) lies in T₁=N_T(L). Thus when J(T) centralizes the
original full module, it lies in T₁ and 3.2.10(8) controls N_G(T₁).
Alternatively, when L₀T is a minimal parabolic over T, the completed
common-normal theorem gives the same bound. These statements use no
A₅ quotient and impose no classification on an arbitrary seed.

The remaining linear-three branch of 10.2.5 must still establish the
bound without either additional premise.
Source: Aschbacher--Smith, 10.2.5, printed pp.747--748, using 3.2.10(8)
and the common-normal argument of 10.2.1.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D
private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The literal core used in C.2.3 lies in the half-Sylow, with no
nonnormality or module-classification assumption. -/
theorem join_core_le_stabilizer :
    (localJoin T L).pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  refine le_inf ?_ (source_join_core_le_component_normalizer D)
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (localJoin T L) (T.subtype le_sup_right)

/-- The first branch of 10.2.5, with J(T) contained in T₁ proved from
the actual local-module centralizer identity. -/
theorem stabilizer_normalizer_of_thompson_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal := by
  have hJcore : elementaryAbelianMaxJ (T : Subgroup G) ≤ (localJoin T L).pCoreIn 2 := by
    rw [← D.sylow_centralizer_module (uniqueness D)]
    exact le_inf (sSup_le fun _ hA => hA.1)
      (hJ.trans (centralizer_le (le_componentOrbit D.moduleSubgroup D.maximalLocal)))
  exact (source_two_overgroup_normalizer_le_of_centralizes D hJ _
    (T.isPGroup'.to_le inf_le_left) (hJcore.trans (join_core_le_stabilizer D))).2

/-- The common-normal route to 10.2.5 retains only the actual
minimal-parabolic premise, not an A₅ marking. -/
theorem stabilizer_normalizer_of_uniqueMaximalOver
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hP : Order.HasUniqueMaximalOver (T : Subgroup G) (localJoin T L)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hT0 : (T : Subgroup G) ⊓ localOrbit T L ≤ R :=
    inf_le_inf_left _ (source_nonnormal_orbit_le_normalizer D hn)
  have hne : R ≠ ⊥ := by
    intro he
    exact D.module_ne_bot (bot_unique
      (((le_inf D.module_le_sylow D.module_le_orbit).trans hT0).trans_eq he))
  have he : R.subgroupOf (T : Subgroup G) =
      (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
    ext x
    exact and_iff_right x.property
  have hnormal : (R.subgroupOf (T : Subgroup G)).Normal := by
    rw [he]
    exact normal_of_index_eq_two
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
  exact source_normalizer_le_of_orbit_sylow D hP R hne inf_le_left
    ((normal_subgroupOf_iff_le_normalizer inf_le_left).mp hnormal)
    (source_orbit_sylow_of_intersection_le R inf_le_left hT0)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
