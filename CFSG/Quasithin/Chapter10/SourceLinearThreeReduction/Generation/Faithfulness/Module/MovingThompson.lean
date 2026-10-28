module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.SectionCoordinates
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.NaturalRows
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.NonFFFixedSpan
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.DoubledExclusion

/-!
# Original Hall-kernel fixation from local Thompson movement

Minimality and the proved two-factor classification give a single natural
SL₂ or binary SL₃ section on the first moved factor. Opposite-component
centralization identifies its fixed kernel with the one used by the literal
full quotient. Scalar commutants and actual Sylow conjugation therefore
fix the original Hall kernel on the whole module, without model callbacks.

If the local Thompson subgroup centralizes the module, each original H-star
subgroup centralizes Ω₁Z(T), and the Hall kernel fixes the Sylow-fixed orbit.
That branch still needs generation of the whole module or justified
reselection. The positive fixed-layer and moving-omega branches are already
covered by local Thompson movement.

Source: Aschbacher--Smith 3.1.8, 10.1.1--3 and 10.2.3(2),
printed pp.576, 741--742 and 745, using B.5.6 and D.3.21.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open PointControl.Selection PointControl.Selection.ModuleChoice

/-- Local Thompson movement supplies the actual natural marking and proves
fixation of the original Hall kernel on the whole module. -/
theorem source_hall_kernel_fixes_of_local_thompson
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (Y : Subgroup H) (hYM : Y ≤ D.maximalLocal.subgroupOf H)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf (D.maximalLocal.subgroupOf H))) :
    Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G) := by
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hsep := full_moved_centralizes_partner D hJ ht htn
  rcases moving_local_natural_of_minimal D hmin hn hna hJ with hr | hb
  · obtain ⟨n,hnn,a,⟨c⟩⟩ := hr
    let : NeZero n := ⟨by omega⟩
    let : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
    obtain ⟨e,_,he⟩ := source_moved_quotient_coordinates_of_separated_section D hpair hsep _ c
    apply source_hall_kernel_fixes_of_natural_sl2 D hn Y hYM hY a e
    intro k v
    rw [sourceMovedModelHom_apply]
    exact he k v
  · obtain ⟨a,⟨c⟩⟩ := hb
    obtain ⟨e,_,he⟩ := source_moved_quotient_coordinates_of_separated_section D hpair hsep _ c
    apply source_hall_kernel_fixes_of_natural_sl3 D hn Y hYM hY a e
    intro k v
    rw [sourceMovedModelHom_apply]
    exact he k v

/-- In the quiet local branch, source 3.1.8 forces every original H-star
member to centralize Ω₁Z(T). -/
theorem source_hstar_centralizes_omega_of_local_thompson_centralizes
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let := D.module_elementary
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hm := D.lemma_3_2_3_uniqueness hu
  have hq := source_reduced_seed_qrc_hypotheses T (localOrbit T L) D.maximalLocal
    (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    D.simpleQTKE hm.1 D.internal_actor_residual D.internal_actor_cases
    D.seedSpace D.homogeneous.isIrrPlus hH
  have hz : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      (center H).map H.subtype := by
    by_contra hz
    exact hq.thompson_moves_of_noncentral_omega D.simpleQTKE hm.1 hm.2.2
      D.module_ne_bot hz hJ
  intro h hh z hz'
  obtain ⟨c,hc,rfl⟩ := hz hz'
  exact (congrArg H.subtype (mem_center_iff.mp hc ⟨h,hh⟩)).symm

/-- The original odd Hall kernel fixes the orbit of the Sylow-fixed layer. -/
theorem source_hall_kernel_fixes_fixed_span_of_local_thompson_centralizes
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
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
    ((inf_le_left.trans (map_subtype_le Y)).trans (source_hstar_centralizes_omega_of_local_thompson_centralizes D hJ hH))

/-- The remaining module-fixation problem lies in the quiet branch with
zero full orbit-fixed layer and with the Sylow-fixed orbit already fixed. -/
theorem source_hall_kernel_fixation_or_quiet_fixed_span
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (Y : Subgroup H) (hYM : Y ≤ D.maximalLocal.subgroupOf H)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf (D.maximalLocal.subgroupOf H))) :
    (Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G)) ∨
    (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (D.moduleSubgroup : Set G) ∧
      D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ∧
      Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤ centralizer
        (conjugateSpanBy (D.fullModule ⊓ centralizer (T : Set G)) (localOrbit T L) : Set G)) := by
  by_cases hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)
  · exact Or.inr ⟨hJ,source_fullModule_fixed_eq_bot_of_many D hmany hJ,
      source_hstar_centralizes_omega_of_local_thompson_centralizes D hJ hH,source_hall_kernel_fixes_fixed_span_of_local_thompson_centralizes D hJ hH Y hYM hY⟩
  · exact Or.inl (source_hall_kernel_fixes_of_local_thompson D hmin hn hna hJ Y hYM hY)

/-- Movement of Ω₁Z(T) by the original H-star member forces full fixation
by its Hall section kernel. -/
theorem source_hall_kernel_fixes_of_hstar_moves_omega
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hz : ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (Y : Subgroup H) (hYM : Y ≤ D.maximalLocal.subgroupOf H)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf (D.maximalLocal.subgroupOf H))) :
    Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G) := by
  apply source_hall_kernel_fixes_of_local_thompson D hmin hn hna _ Y hYM hY
  intro hJ
  exact hz (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (source_hstar_centralizes_omega_of_local_thompson_centralizes D hJ hH)))

/-- A nonzero full orbit-fixed layer forces the moving branch and hence
full-module fixation. -/
theorem source_hall_kernel_fixes_of_full_fixed_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hfixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (Y : Subgroup H) (hYM : Y ≤ D.maximalLocal.subgroupOf H)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf (D.maximalLocal.subgroupOf H))) :
    Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G) :=
  source_hall_kernel_fixes_of_local_thompson D hmin hn hna
    (local_thompson_moves_of_full_fixed_ne_bot D hmany hfixed) Y hYM hY

omit D in
/-- The original module-selection contract needs fixed-space generation
only in the quiet local Thompson branch; the moving branch is discharged. -/
theorem source_nonnormalHallKernelModule_of_quiet_fixed_generation
    (hgen : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        D.IsMinimalFullModule →
        ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
        ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
        Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
          centralizer (D.moduleSubgroup : Set G) →
        D.fullModule = conjugateSpanBy
          (D.fullModule ⊓ centralizer (T : Set G)) (localOrbit T L)) :
    SourceNonnormalHallKernelModuleAt T := by
  intro hmany L D hmin hn hna H hH _ Y hYM hY _ _
  refine ⟨D,?_⟩
  by_cases hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)
  · rw [hgen hmany L D hmin hn hna hJ]
    exact source_hall_kernel_fixes_fixed_span_of_local_thompson_centralizes D hJ hH Y hYM hY
  · exact source_hall_kernel_fixes_of_local_thompson D hmin hn hna hJ Y hYM hY

end CFSG.Quasithin.Chapter10
