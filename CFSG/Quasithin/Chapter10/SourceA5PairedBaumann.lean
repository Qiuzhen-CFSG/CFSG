module
public import CFSG.Quasithin.Chapter10.SourceBaumannBlocks
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveBaumann

/-!
# The paired Baumann action in the original alternating-five branch

If the original L is not T-invariant and its Baumann normalizer escapes M,
the symmetric-five alternative is necessarily paired. In the single case,
E.2.3 makes the entire two-residual a generating block. Component
correspondence then identifies L with this normal subgroup, a contradiction.
The surviving marked pair gives the actual Baumann quotient as a product of
two transposition four-groups, on the original local module and quotient map.

This supplies the quotient action used before the four-dihedral-factor
calculation in Aschbacher–Smith 10.2.1, printed pp.742–743, from E.2.3 and
C.1.24. No full/local-module equality or coordinate hypothesis is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction
open Representation Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D

/-- The original local Thompson subgroup acts nontrivially whenever its
ambient Baumann normalizer escapes M. -/
theorem source_local_thompson_not_centralizes
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ¬ elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  intro hc
  apply hout
  apply source_local_baumann_normalizer_le_of_centralizes D
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le le_sup_right)
  rw [← hjmap]
  rintro g ⟨j, hj, rfl⟩ z hz
  exact congrArg H.subtype (hc hj
    ⟨z, (D.module_le_core.trans (pCoreIn_le 2 H)) hz⟩ hz)

/-- The paired E.2.3 source on the original local module and quotient. -/
@[expose] def SourcePairedFiveAction : Prop :=
  let U := D.moduleSubgroup.subgroupOf (localJoin T L)
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set (localJoin T L))
  SymmetricFivePairSource (T.subtype le_sup_right) U (QuotientGroup.mk' C)
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)

/-- Nonnormality of the original L excludes the single symmetric-five action. -/
theorem source_a5_paired_five_action
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourcePairedFiveAction D := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  have hP := source_a5_minimal_parabolic D e hn
  have hfive := (source_a5_baumann_normalizer_or_five_action_unconditional D e hn).resolve_left hout
  rcases hfive with ⟨hqs,c,⟨em⟩⟩ | hp
  · have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal
    have h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
      ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    obtain ⟨hb,_,_,_,_⟩ := quasisimple_five_block_of_no_characteristic_baumann
      h36 (D.local_internal_module hu).sqtk S hP U hU
      (source_local_thompson_not_centralizes D hout) q hq hk hqs c.sectionData em
      (source_join_fitting D) (source_baumann_characteristic_normal_eq_bot D hout)
    have hgen := pResidual_sup_sylow_eq_top S
    have hK := nonsolvable_generating_block_isCComponent (source_join_not_solvable D)
      (pResidual 2 H) hb S hgen
    obtain ⟨s,hs⟩ := source_original_component_conjugate_of_generating_component D
      (pResidual 2 H) hK hgen
    have he : L.subgroupOf H = pResidual 2 H := hs.trans
      (normal_iff_map_conj_eq.mp inferInstance (s : H))
    have hnormal : (L.subgroupOf H).Normal := he ▸ inferInstance
    exact False.elim (hn (le_sup_right.trans
      ((normal_subgroupOf_iff_le_normalizer
        ((le_componentOrbit L T).trans le_sup_left)).mp hnormal)))
  · exact hp

/-- The surviving paired marking includes the literal Thompson and Baumann
images; each factor is a conjugate of the transposition four-group. -/
@[expose] def SourcePairedBaumannAction : Prop :=
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  letI := offenderSubgroup_normal α
  ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp (offenderSubgroup α).subtype),
    ∃ c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
      (∃ t : S.mapSurjective (QuotientGroup.mk'_surjective C),
        d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first) ∧
      (elementaryAbelianMaxJ (S : Subgroup H)).map q =
        (ChapterB.baumann (S : Subgroup H)).map q ∧
      ∃ a b : Equiv.Perm (Fin 5), (ChapterB.baumann (S : Subgroup H)).map q =
        (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
          ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
            ((offenderSubgroup α).subtype.comp c.action.groupEquiv.symm.toMonoidHom)

/-- The original alternating-five branch gives the marked paired Baumann
quotient required for the four-dihedral-factor argument. -/
theorem source_a5_paired_baumann_action
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourcePairedBaumannAction D := by
  let := (source_parabolic_module_reduced D).normal
  let := (source_parabolic_module_reduced D).elementary
  obtain ⟨d,t,ht1,ht2,⟨c⟩⟩ := source_a5_paired_five_action D e hn hout
  refine ⟨d,c,⟨t,ht1,ht2⟩,?_⟩
  exact paired_thompson_baumann_of_symmetric_model _
    (source_a5_minimal_parabolic D e hn) _ (source_parabolic_module_reduced D)
    (source_local_thompson_not_centralizes D hout) _ _ _ d c ⟨t,ht1,ht2⟩

end CFSG.Quasithin.Chapter10
