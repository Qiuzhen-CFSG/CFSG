module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.SingleSource
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.FiveSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
/-!
# Selecting the actual original paired linear source

Apply the complete E.2.3 natural-factor classification to the original
local join. Nonnormality excludes its single source, and the given natural
SL₂(4) section excludes its paired five-letter source. The surviving linear
marking retains the same two factors and the prescribed Sylow exchanger.
Source: Aschbacher–Smith E.2.3 and 10.2.3(4), pp.216–217 and 746.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

@[expose] def SourceOriginalPairedLinear : Prop :=
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let hq := QuotientGroup.mk'_surjective C
  let hk := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  letI := offenderSubgroup_normal α
  ∃ (d : SourceTwoFactorCase (α.comp Y.subtype)) (F : BinaryField),
    Nonempty (d.MarkedProduct (linearNatural F 2)) ∧
      ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first

variable {F : Type*} [Field F] [CharP F 2]
local instance originalSelectionFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
set_option backward.isDefEq.respectTransparency false in
theorem source_original_paired_linear_of_natural_four
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)))
    (hF : Nat.card F = 4)
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    SourceOriginalPairedLinear D := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set X) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun Z _ _ => ChapterA.Section02.theoremA_knownSimple (G := Z))
    (fun Z _ _ => ChapterA.Section02.theoremC_knownSimple (G := Z))
    D.simpleQTKE T D.maximal
  have hG := (D.local_internal_module hu).sqtk
  have hP := source_a5_minimal_parabolic D e hn
  rcases source_nonsolvable_natural_factors hG S hP U hU (source_join_not_solvable D) hJ with
    ⟨hqs,_⟩ | ⟨d,_,_⟩
  · exact (source_original_not_quasisimple_source D e hn hJ hqs).elim
  · have hcore : pCore 2 (X ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
    have hne : q.ker ≠ ⊤ := by
      intro he
      apply hJ
      rw [←hk,he]
      exact le_top
    have hp := (minimalParabolic_reduced_image S hP q hq hcore hne).2
    have hff : IsFFModule α := by
      obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk S
      · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top S).trans hf.1)).elim
      · exact hf
    obtain ⟨t,ht₁,ht₂,hkind⟩ :=
      source_offender_two_factor_shared_natural α (S.mapSurjective hq) hp hff hcore d
    rcases hkind with ⟨K,⟨c⟩⟩ | hfive
    · exact ⟨d,K,⟨c⟩,t,ht₁,ht₂⟩
    · exact (source_original_not_paired_five_of_natural_four D e hn hJ hF f n
        ⟨d,t,ht₁,ht₂,hfive⟩).elim
end CFSG.Quasithin.Chapter10
