module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Contracts
public import CFSG.Quasithin.Chapter10.SourceA5OffenderFixedGeometry
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureCommutation
public import CFSG.Quasithin.ChapterE.Section03.Parameters.RankKernel

/-!
# Excluding the large rows from their actual automizer bounds

The fixed-space geometry gives moduleA≥m-2 whenever a small intersection
acts nontrivially. The strict opposite bound therefore makes that intersection
centralize the moved factor. A nonfixed normalizing element puts the original
factor in the conjugate local normalizer. The local two-rank bound supplies a
nontrivial action kernel, so point-centralizer control places the entire
conjugate factor in M. The four-conjugator argument then gives [V,Vᵍ]=1.

This proves the numerical/geometric exclusion with explicit independent inputs;
it does not construct the source module markings or the fixed-space geometry.
The reused theorems in A₅-named files have model-free statements here.
Source: Aschbacher--Smith, 10.2.12, printed pp.754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- Every large row has enough fixed-quotient size for the normalizing element. -/
theorem LargeModuleBounds.fixed_size_gt_eight (b : LargeModuleBounds D) :
    8 < (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ := by
  have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) b.dimension_gt
  exact lt_of_lt_of_le hp b.fixed_size

/-- A centralizing intersection places the whole conjugate factor in M,
using only the actual local two-rank and fixed-quotient bounds. -/
theorem conjugate_moved_le_of_intersection_centralizes
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal)
    (hsize : 8 < (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆)
    {r : ℕ} (hr : primeRank 2 (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal) ≤ r)
    (hcard : 2 ^ r < Nat.card (⁅D.fullModule,L⁆ : Subgroup G))
    {g : G}
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2)
    (hcentral : (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤ D.maximalLocal := by
  let W := ⁅D.fullModule,L⁆
  let := source_full_moved_elementary D
  obtain ⟨b,hb,hbM,_,hbn⟩ := exists_nonfixed_normalizing_element D hn hsize hsmall
  have hWb : W ≤ centralizer ({b} : Set G) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr ((hcentral ⟨hb,hbM⟩) w hw)
  have hWlocal := hWb.trans
    (source_nonnormal_conjugate_point_centralizer_normalizes D hn ht htn hcross hcent hb hbn)
  obtain ⟨w,hw,hwne,hwc⟩ := exists_nontrivial_centralizer_of_local_rank_map
    W W D.maximalLocal (MulAut.conj g) hWlocal hr hcard
  apply le_trans _ (hcent w hw hwne)
  intro p hp
  exact mem_centralizer_singleton_iff.mpr (hwc p hp)

/-- The fixed-space identity and numerical bound force each small
intersection to centralize the literal moved factor. -/
theorem LargeModuleBounds.intersection_centralizes (b : LargeModuleBounds D)
    (hgeometry : FixedSpaceGeometry D) {x : G} (hx : x ∉ D.maximalLocal)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj x).toMonoidHom)
      (D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) ≤ 2) :
    (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  by_contra hactive
  obtain ⟨hAN,hfix⟩ := hgeometry x hx hsmall
  have hlo := offender_moduleA_lower D (show 2 < b.dimension by have := b.dimension_gt; omega)
    b.fixed_size hsmall hAN hactive hfix
  exact (not_lt_of_ge hlo) b.parameter_small

/-- The large-row bounds and fixed-space geometry contradict an actual
small noncommuting offender. This is the numerical end of 10.2.12. -/
theorem LargeModuleBounds.false_of_configuration (b : LargeModuleBounds D)
    {g : G} (c : Configuration T D g) (hgeometry : FixedSpaceGeometry D) : False := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  apply c.noncommuting
  apply source_a5_small_conjugates_commute_of_moved_factor D c.nonnormal ht
    (b.crossed t ht htn) 2 ?_ g c.small
  intro x hx hsmall
  have hc := b.intersection_centralizes hgeometry hx hsmall
  have hm := conjugate_moved_le_of_intersection_centralizes D c.nonnormal ht htn
    (b.crossed t ht htn) c.pointCentralizers b.fixed_size_gt_eight
    b.automizer_rank b.rank_small hsmall hc
  exact ⟨hm, by rwa [inf_eq_left.mpr hm] at hc⟩

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
