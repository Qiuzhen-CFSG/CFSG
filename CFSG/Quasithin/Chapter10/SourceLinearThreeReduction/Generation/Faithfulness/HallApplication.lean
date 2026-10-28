module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.Complete
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.HallConjugacy

/-!
# Hall faithfulness after the complete normalizer exclusion

The intrinsic Hall subgroup's nontrivial section kernel would supply an
escaping elementary odd actor. Full-module fixation now contradicts the
proved nonnormal normalizer theorem. In the moving-Thompson branch fixation
is proved, and Hall conjugacy gives faithfulness for every prescribed Hall
subgroup of the literal overlap. No normalizer or model premise remains.
Source: Aschbacher--Smith10.2.3(2), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Fixation of the full module discharges faithfulness of the intrinsic Hall subgroup. -/
theorem source_hstar_hall_kernel_eq_bot_of_full_fixation
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hfix : d.witness.abelianGroup.map H.subtype ⊓
      sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G)) :
    d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H = ⊥ := by
  by_contra hk
  obtain ⟨p,A,hp,ho,hA,hAe,hAY,hAC,hAT,hout⟩ :=
    source_hstar_hall_kernel_escaping_elementary D hH hlarge hP d hk
  let : Fact p.Prime := ⟨hp⟩
  exact hout (source_nonnormal_oddKernel_normalizer D hn ho A hA hAe hAC
    ((le_inf hAY hAC).trans hfix) hAT)

/-- The moving local Thompson branch proves the original arbitrary-Hall conclusion. -/
theorem source_nonnormal_hall_faithful_of_local_thompson
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ := by
  obtain ⟨hP,_,_,_,d,he,_,_⟩ :=
    source_hstar_cartan_data_of_generation_gt_one D hH hlarge
  have hfix := source_hall_kernel_fixes_of_local_thompson D hmin hn hna hJ
    d.witness.abelianGroup (he ▸ d.hall_le) (he ▸ d.hall)
  have hfaith := source_hstar_hall_kernel_eq_bot_of_full_fixation D hn hH hlarge hP d hfix
  exact source_hall_sectionKernel_faithful_of_hall_conjugacy
    (M := D.maximalLocal) (X := localOrbit T L) le_rfl
    (he ▸ d.maximal_solvable) hBM hB (he ▸ d.hall) hfaith

end CFSG.Quasithin.Chapter10
