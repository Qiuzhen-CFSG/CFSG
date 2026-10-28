module
public import CFSG.Quasithin.Chapter10.SourceA5MinimalParabolic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Normalizers above the original orbit intersection

Any subgroup of T containing T ∩ L₀ is Sylow in its join with L₀:
normal restriction supplies the prescribed Sylow of L₀, and the normal
supplement index criterion applies. The original A₅ minimal parabolic
therefore puts N_G(R) in M for every such T-invariant subgroup R.

In the nonnormal source case N_T(L) has index two. The corresponding
normalizer in L₀T has two-group quotient, so it contains O²(L₀T)=L₀.
Thus T₁=N_T(L) contains T ∩ L₀ and satisfies the preceding bound.
These are the early common-normal deductions of 10.2.1; the full/local
module equality and the subsequent symmetric-five argument are unnecessary.
Source: Aschbacher–Smith, 10.2.1, printed pp.742–743, with T₀=T ∩ L₀
as defined on printed p.741.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Containing the original orbit intersection discharges the relative
Sylow premise in the common-normal argument. -/
theorem source_orbit_sylow_of_intersection_le
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hR : (T : Subgroup G) ⊓ localOrbit T L ≤ R) :
    Chapter1.IsSylowIn 2 R (localOrbit T L ⊔ R) := by
  let H := localJoin T L
  have hnormal : ((localOrbit T L).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer
      (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype (show (T : Subgroup G) ≤ H from le_sup_right),
      map_subgroupOf_eq_of_le le_sup_right⟩
  obtain ⟨P, hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs
    (show localOrbit T L ≤ H from le_sup_left) hnormal.isSubnormal
  exact IsPGroup.exists_sylow_sup_of_coprime_index (localOrbit T L) R
    (T.isPGroup'.to_le hRT) (hRT.trans (le_normalizer_componentOrbit L T))
    P P.not_dvd_index (hP ▸ hR)

/-- Every T-invariant subgroup above T ∩ L₀ has its ambient normalizer
in M in the original nonnormal A₅ branch. -/
theorem source_a5_normalizer_le_of_orbit_intersection_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hT0 : (T : Subgroup G) ⊓ localOrbit T L ≤ R) :
    normalizer (R : Set G) ≤ D.maximalLocal := by
  apply source_a5_normalizer_le_of_orbit_sylow D e hn R _ hRT hR
    (source_orbit_sylow_of_intersection_le R hRT hT0)
  intro he
  exact D.module_ne_bot (bot_unique
    (((le_inf D.module_le_sylow D.module_le_orbit).trans hT0).trans_eq he))

include D in
/-- The index-two component normalizer contains the whole two-residual L₀. -/
theorem source_nonnormal_orbit_le_normalizer
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    localOrbit T L ≤ normalizer (L : Set G) := by
  let H := localJoin T L
  let N := normalizer (L.subgroupOf H : Set H)
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hi : N.index = 2 := by
    change (normalizer (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔
      (T : Subgroup G)) : Set (componentOrbit L (T : Subgroup G) ⊔
      (T : Subgroup G) : Subgroup G))).index = 2
    rw [componentOrbit_sup]
    exact source_nonnormal_normalizer_index D.simpleQTKE D.maximal.1 hn
  let : N.Normal := normal_of_index_eq_two hi
  have hquot : IsPGroup 2 (H ⧸ N) :=
    IsPGroup.of_card (n := 1) (by simpa only [N.index_eq_card, pow_one] using hi)
  have hres := (pResidual_le_iff_isPGroup_quotient 2 N).mpr hquot
  have hm := map_mono (f := H.subtype) hres
  rw [source_join_residual D] at hm
  apply hm.trans
  rw [show N = (normalizer (L : Set G)).subgroupOf H from
    (subgroupOf_normalizer_eq hLH).symm, subgroupOf_map_subtype]
  exact inf_le_left

/-- The source stabilizer T₁=N_T(L) has its full ambient normalizer in M,
before any full-module equality or marked-module classification. -/
theorem source_a5_sylow_stabilizer_normalizer_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hi : ((normalizer (L : Set G)).subgroupOf (T : Subgroup G)).index = 2 :=
    source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  have he : R.subgroupOf (T : Subgroup G) =
      (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
    ext x
    exact and_iff_right x.property
  have hnormal : (R.subgroupOf (T : Subgroup G)).Normal :=
    he ▸ normal_of_index_eq_two hi
  exact source_a5_normalizer_le_of_orbit_intersection_le D e hn R inf_le_left
    ((normal_subgroupOf_iff_le_normalizer (show R ≤ (T : Subgroup G) from
      inf_le_left)).mp hnormal)
    (inf_le_inf_left _ (source_nonnormal_orbit_le_normalizer D hn))

end CFSG.Quasithin.Chapter10
