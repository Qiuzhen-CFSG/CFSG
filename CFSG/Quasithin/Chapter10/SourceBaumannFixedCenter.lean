module
public import CFSG.Quasithin.Chapter10.SourceBaumannBlocks

/-!
# The fixed-center branch of the original Baumann exception

A nonzero subgroup C_Z(L₀), where Z=Ω₁(Z(T)), is centralized by L₀T.
Uniqueness above L₀T therefore puts its full ambient centralizer in M.
If the Baumann normalizer escapes M, finite minimal descent selects an
actual H* inside that normalizer. Its original Sylow-center span W lies
in Ω₁(Z(Baum(T))), is reduced in H, and has centralizer inside M.
In particular the action of H on W is nontrivial.

This gives the actual auxiliary group and module in the nonzero fixed-center
case of 10.2.1, retaining the literal conjugate span and ambient centralizer.
The later transvection, model-selection and overcomponent contradiction
remain separate source arguments.
Source: Aschbacher–Smith, 10.2.1, printed p.743, using B.2.14 and1.2.7.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

private theorem source_uniqueness :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The nonzero L₀-fixed part of the original Sylow center has centralizer in M. -/
theorem source_fixed_center_centralizer_le
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    centralizer (omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) : Set G) ≤ D.maximalLocal := by
  let N := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)
  have hNT : N ≤ centralizer ((T : Subgroup G) : Set G) := by
    intro z hz t ht
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 t ht
  have hNL : N ≤ centralizer (localJoin T L : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_right) (le_centralizer_iff.mp hNT)
  have hlocal := (le_centralizer_iff.mp hNL).trans (centralizer_le_normalizer (N : Set G))
  exact (centralizer_le_normalizer (N : Set G)).trans
    (normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness (source_uniqueness D)).2.2
      ((omegaOneCenterAmbient_elementaryAbelian _).isPGroup.to_le inf_le_left) hne hlocal)

/-- The escaping Baumann normalizer contains an actual source H* subgroup. -/
theorem source_exists_baumann_HStar
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ H : Subgroup G, H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal := by
  let B := ChapterB.baumann (T : Subgroup G)
  have hT : (T : Subgroup G) ≠ ⊥ := fun ht =>
    D.module_ne_bot (bot_unique (D.module_le_sylow.trans_eq ht))
  have hB : B ≠ ⊥ := fun hb =>
    elementaryAbelianMaxJ_ne_bot_of_finite_pGroup _ T.isPGroup' hT
      (bot_unique ((ChapterB.elementaryAbelianMaxJ_le_baumann _).trans_eq hb))
  have hN : normalizer (B : Set G) ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨Chapter1.mem_H_of_isTwoLocal ⟨B,hB,T.isPGroup'.to_le inf_le_left,rfl⟩,?_⟩
    exact (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  exact Finite.exists_le_minimal
    (p := fun Y : Subgroup G => Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ D.maximalLocal)
    (a := normalizer (B : Set G)) ⟨hN,hout⟩

omit D [Finite G] in
private theorem normalizer_omegaCenter (B : Subgroup G) :
    normalizer (B : Set G) ≤ normalizer (omegaOneCenterAmbient B : Set G) := by
  let R : Subgroup B := (omega₁ (center B) (p := 2)).map (center B).subtype
  let : (omega₁ (center B) (p := 2)).Characteristic := omega₁_characteristic _
  let : R.Characteristic := inferInstance
  exact normalizer_le_normalizer_characteristic_image B R

/-- The original H* and Sylow-center span in the nonzero fixed-center branch
meet the reducedness, placement, and nontrivial-action conclusions. -/
theorem source_baumann_HStar_fixed_center_setup
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal ∧
      H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      (let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
       W ≤ omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) ∧
       IsPReduced 2 (W.subgroupOf H) ∧
       H ⊓ centralizer (W : Set G) ≤ D.maximalLocal ∧
       ¬ H ≤ centralizer (W : Set G)) := by
  obtain ⟨H,hHN,hH⟩ := source_exists_baumann_HStar D hout
  let B := ChapterB.baumann (T : Subgroup G)
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  have hZE : omegaOneCenterAmbient (T : Subgroup G) ≤ omegaOneCenterAmbient B := by
    intro z hz
    obtain ⟨hzT,hz2,hzc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨ChapterC.RankOne.FiveBlockSource.omegaCenter_le_baumann _ hz,hz2,
        fun b hb => hzc b (show b ∈ (T : Subgroup G) from hb.1)⟩
  have hWE : W ≤ omegaOneCenterAmbient B :=
    conjugateSpanBy_le hZE (hHN.trans (normalizer_omegaCenter B))
  have hred : IsPReduced 2 (W.subgroupOf H) :=
    (D.qrcHypotheses (source_uniqueness D) hH).sylowOmega_reduced
      (D.simpleQTKE.evenCharacteristic T)
  have hc : centralizer (W : Set G) ≤ D.maximalLocal :=
    (centralizer_le (inf_le_left.trans (le_conjugateSpanBy _ _))).trans
      (source_fixed_center_centralizer_le D hne)
  exact ⟨H,hH,hHN,hWE,hred,inf_le_right.trans hc,
    fun hh => hH.1.2 (hh.trans hc)⟩
end CFSG.Quasithin.Chapter10
