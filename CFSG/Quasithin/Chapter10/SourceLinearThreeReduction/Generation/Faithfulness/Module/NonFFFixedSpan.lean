module
public import CFSG.Quasithin.Chapter10.SourceThompsonControl
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.QuotientFixation

/-!
# The non-FF Hall kernel fixes the original Sylow-fixed orbit

The source 3.1.8 movement theorem forces each H-star subgroup to centralize
Omega-one of the Sylow center when the chosen local module is not FF. The
literal odd Hall kernel therefore fixes the Sylow-fixed part of the full
module. The perfect-centralizer cover replaces the original orbit group by
its fixed perfect residual in generating that part; its two-core centralizes
the full module. Thus the kernel fixes the generated orbit as well.

The multiple-overgroup hypothesis also forces the full module's orbit-fixed
layer to vanish in this branch. Fixation of the whole full module still needs
fixed-space generation or a justified reselection, retained explicitly here.
Source: Aschbacher--Smith 3.1.8, 4.4.14 and 10.2.3(2), printed pp.576,
624--625 and 745 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The non-FF branch puts the actual H-star group in the centralizer of
 the original Sylow omega-center. -/
theorem source_hstar_centralizes_omega_of_nonFF
    (hnon : letI := D.module_elementary
      ¬ Representation.BinaryOffender.IsFFModule
        (ChapterD.UniqueFactor.imageRepresentation (localJoin T L) D.moduleSubgroup
          D.join_normalizes_module))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let := D.module_elementary
  have hu := D.lemma_3_2_3_uniqueness (uniqueness D)
  have hq := source_reduced_seed_qrc_hypotheses T (localOrbit T L) D.maximalLocal
    (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    D.simpleQTKE hu.1 D.internal_actor_residual D.internal_actor_cases
    D.seedSpace D.homogeneous.isIrrPlus hH
  have hz : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    by_contra hz
    have hj := hq.thompson_moves_of_noncentral_omega D.simpleQTKE hu.1 hu.2.2
      D.module_ne_bot hz
    exact hnon (D.module_isFF_of_thompson_not_centralizes hj)
  intro h hh z hz'
  obtain ⟨c,hc,rfl⟩ := hz hz'
  exact (congrArg H.subtype (mem_center_iff.mp hc ⟨h,hh⟩)).symm

/-- The original full module has zero orbit-fixed layer in the non-FF
branch under the source multiple-overgroup hypothesis. -/
theorem source_nonFF_fullModule_fixed_eq_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : letI := D.module_elementary
      ¬ Representation.BinaryOffender.IsFFModule
        (ChapterD.UniqueFactor.imageRepresentation (localJoin T L) D.moduleSubgroup
          D.join_normalizes_module)) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  by_contra hh
  exact hnon (source_full_fixed_conclusions D hmany hh).2

/-- The original section-kernel actor fixes the orbit of the Sylow-fixed
part of the full module whenever it fixes the Sylow omega-center. -/
theorem source_sectionKernel_fixes_fixed_span
    (B : Subgroup G) (hB : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B))
    (hz : B ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    B ≤ centralizer (conjugateSpanBy
      (D.fullModule ⊓ centralizer (T : Set G)) (localOrbit T L) : Set G) := by
  let X := localOrbit T L
  let V := D.fullModule
  let Z := V ⊓ centralizer (T : Set G)
  have hVT : V ≤ (T : Subgroup G) := by
    apply (D.fullModule_le_reduced (uniqueness D)).trans
    apply (map_mono (reducedPSubgroup_le_pCore 2 D.maximalLocal)).trans
    change D.maximalLocal.pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (le_normalizer_componentOrbit L T)] using
      pCoreIn_le_sylow D.maximalLocal (T.subtype (le_normalizer_componentOrbit L T))
  have hZomega : Z ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    let := D.fullModule_elementary (uniqueness D)
    intro z hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨hVT hz.1, elemPow_eq_one_of_isElementaryAbelian z hz.1,
      fun t ht => hz.2 t ht⟩
  have hZB : Z ≤ centralizer (B : Set G) :=
    hZomega.trans (le_centralizer_iff.mp hz)
  have hcore : X.pCoreIn 2 ≤ centralizer (V : Set G) := by
    apply (pCoreIn_mono_of_normalizes X.le_normalizer le_rfl).trans
    apply le_centralizer_iff.mpr
    intro v hv q hq
    obtain ⟨v',hv',rfl⟩ := D.fullModule_le_reduced (uniqueness D) hv
    obtain ⟨q',hq',rfl⟩ := hq
    exact congrArg Subtype.val
      (reducedPSubgroup_le_centralizer_pCore 2 D.maximalLocal hv' q' hq')
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect X := isPerfect_iSup_conjugates L (T : Subgroup G)
  let F := (solvableResidual (X ⊓ centralizer (B : Set G) : Subgroup G)).map
    (X ⊓ centralizer (B : Set G)).subtype
  have hF : F ≤ centralizer (B : Set G) := (map_subtype_le _).trans inf_le_right
  have hspan : ConjugateSpanLE Z X F := by
    intro x hx
    have hcover := perfect_centralizer_cover X B hB hodd
    have hx' : x ∈ (X : Set G) := hx
    rw [hcover] at hx'
    obtain ⟨f,hf,q,hq,he⟩ := hx'
    refine ⟨f,⟨((map_subtype_le _).trans inf_le_left) hf,hf⟩,
      q,⟨pCoreIn_le 2 X hq,?_⟩,he⟩
    exact (centralizer_le (conjugateSpanBy_le inf_le_left
      ((localOrbit T L).le_normalizer.trans D.maximalLocal_normalizes_fullModule)))
      (hcore hq)
  exact le_centralizer_iff.mp (hspan.span_le.trans
    (conjugateSpanBy_le hZB (hF.trans (centralizer (B : Set G)).le_normalizer)))

/-- In the non-FF branch the actual Hall kernel fixes the original
 Sylow-fixed generated orbit, with its oddness and seed fixation discharged. -/
theorem source_nonFF_hall_kernel_fixes_fixed_span
    (hnon : letI := D.module_elementary
      ¬ Representation.BinaryOffender.IsFFModule
        (ChapterD.UniqueFactor.imageRepresentation (localJoin T L) D.moduleSubgroup
          D.join_normalizes_module))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (Y : Subgroup H) (hYM : Y ≤ D.maximalLocal.subgroupOf H)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf (D.maximalLocal.subgroupOf H))) :
    Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤ centralizer
      (conjugateSpanBy (D.fullModule ⊓ centralizer (T : Set G)) (localOrbit T L) : Set G) := by
  have ho : Odd (Nat.card Y) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe hYM).toEquiv]
    exact OddHall.odd_hall_odd hY
  have hm : Odd (Nat.card (Y.map H.subtype)) := by
    rwa [card_map_of_injective H.subtype_injective]
  exact source_sectionKernel_fixes_fixed_span D _ inf_le_right
    (hm.of_dvd_nat (card_dvd_of_le inf_le_left))
    ((inf_le_left.trans (map_subtype_le Y)).trans (source_hstar_centralizes_omega_of_nonFF D hnon hH))

/-- Once the original fixed-space generation is supplied, the non-FF
 branch fixes the full original module. No irreducibility is assumed. -/
theorem source_nonFF_hall_kernel_fixes_of_fixed_generation
    (hnon : letI := D.module_elementary
      ¬ Representation.BinaryOffender.IsFFModule
        (ChapterD.UniqueFactor.imageRepresentation (localJoin T L) D.moduleSubgroup
          D.join_normalizes_module))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (Y : Subgroup H) (hYM : Y ≤ D.maximalLocal.subgroupOf H)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hgen : D.fullModule = conjugateSpanBy
      (D.fullModule ⊓ centralizer (T : Set G)) (localOrbit T L)) :
    Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G) := by
  simpa only [← hgen] using source_nonFF_hall_kernel_fixes_fixed_span D hnon hH Y hYM hY

end CFSG.Quasithin.Chapter10
