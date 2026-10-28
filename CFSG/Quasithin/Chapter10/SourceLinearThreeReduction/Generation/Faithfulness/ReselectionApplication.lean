module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.QuietReselection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.HallApplication

/-!
# The remaining Hall-kernel counterexample after valid seed reselection

A nontrivial intrinsic Hall kernel forces the original quiet branch.
The fixed-seed construction reselects a minimal FundamentalSetup with the
same full module and a local module centralized by the entire Hall kernel.
The moving-Thompson theorem forces this new setup to be quiet as well.
Both its local module and the fixed-seed orbit are proper in V_M, since
full fixation contradicts the completed nonnormal normalizer theorem.

This is a reduction of the actual source counterexample. The remaining
normalizer argument must work from the reselected local-module fixation,
or must rule out the displayed proper fixed-seed orbit. No such upgrade
is assumed here. Source: Aschbacher--Smith4.4.3,4.4.14 and10.2.3(2),
printed pp.619--625 and745 (combined manuscript of1 March2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Every surviving original Hall kernel fixes a legitimate reselected local module,
while still failing to fix its unchanged full module. -/
theorem source_hall_kernel_counterexample_reselection
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥) :
    sourceQuietFixedSpan D < D.fullModule ∧
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.IsMinimalFullModule ∧ E.fullModule = D.fullModule ∧
        E.moduleSubgroup ≤ sourceQuietFixedSpan D ∧ E.moduleSubgroup < E.fullModule ∧
        Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
          centralizer (E.moduleSubgroup : Set G) ∧
        d.witness.abelianGroup.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
          centralizer (E.moduleSubgroup : Set G) := by
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  have hYM := he ▸ d.hall_le
  have hY := he ▸ d.hall
  have hnot : ¬ d.witness.abelianGroup.map H.subtype ⊓
      sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G) :=
    fun hfix => hk (source_hstar_hall_kernel_eq_bot_of_full_fixation D hn hH hlarge hP d hfix)
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G) := by
    by_contra hmove
    exact hnot (source_hall_kernel_fixes_of_local_thompson D hmin hn hna hmove
      d.witness.abelianGroup hYM hY)
  have hWfix : d.witness.abelianGroup.map H.subtype ⊓
      sectionCentralizer (localOrbit T L) ≤ centralizer (sourceQuietFixedSpan D : Set G) :=
    source_hall_kernel_fixes_fixed_span_of_local_thompson_centralizes D hJ hH
      d.witness.abelianGroup hYM hY
  have hWlt : sourceQuietFixedSpan D < D.fullModule :=
    lt_of_le_of_ne (sourceQuietFixedSpan_le D) (fun h => hnot (h ▸ hWfix))
  obtain ⟨E,hEmin,hfull,hEW⟩ := sourceQuietFixedSpan_minimal_reselection D hmany hmin hJ
  have hlocal : d.witness.abelianGroup.map H.subtype ⊓
      sectionCentralizer (localOrbit T L) ≤ centralizer (E.moduleSubgroup : Set G) :=
    hWfix.trans (centralizer_le hEW)
  have hEJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (E.moduleSubgroup : Set G) := by
    by_contra hmove
    have hf := source_hall_kernel_fixes_of_local_thompson E hEmin hn hna hmove
      d.witness.abelianGroup hYM hY
    rw [hfull] at hf
    exact hnot hf
  refine ⟨hWlt,E,hEmin,hfull,hEW,?_,hEJ,hlocal⟩
  rw [hfull]
  exact lt_of_le_of_lt hEW hWlt

end CFSG.Quasithin.Chapter10
