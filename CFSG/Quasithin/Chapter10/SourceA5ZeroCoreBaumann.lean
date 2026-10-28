module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerPair
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedAxes
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveSaturation

/-!
# The entire zero-center local core lies in the Baumann subgroup

The original two-core is the join of the two alternating block layers,
so it lies in the two-residual. Normality then puts it in the residual's
two-core. The paired source saturation theorem places that core inside
the original local Baumann subgroup.

This makes the latter the full preimage of its marked quotient image,
as needed to identify its actual dihedral centralizer factors.
Source: Aschbacher–Smith10.2.1, p.743, using B.2.18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

theorem source_a5_zero_core_le_baumann
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    pCore 2 (localJoin T L) ≤ ChapterB.baumann
      ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) : Subgroup (localJoin T L)) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  obtain ⟨d,c,hex,_,_⟩ := source_a5_original_paired_axes D e hn hout
  have hs := (paired_alpha_and_saturation_of_symmetric_model S
    (source_a5_minimal_parabolic D e hn) U hU (source_local_thompson_not_centralizes D hout)
    q hq hk d c hex).1
  apply le_trans _ hs
  obtain ⟨t,ht,hne,hb,hab,horbit,hsplit,hE⟩ := source_a5_zero_centralizer_pair_core D e hn hout hz
  have ha := (source_a5_original_block_of_baumann_not_controlled D e hn hout).1
  have hQR : pCore 2 H ≤ pResidual 2 H := by
    rw [hsplit]
    apply sup_le
    · exact (map_subtype_le _).trans (le_pResidual_of_isPPerfect _ ha.short.twoPerfect)
    · exact (map_subtype_le _).trans (le_pResidual_of_isPPerfect _ hb.short.twoPerfect)
  exact le_pCoreIn_of_normalizes pCore_isPGroup hQR le_normalizer_of_normal
end CFSG.Quasithin.Chapter10
