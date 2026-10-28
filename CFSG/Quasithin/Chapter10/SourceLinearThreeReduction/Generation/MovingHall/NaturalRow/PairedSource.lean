module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.MinimalParabolic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.Inputs
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalSelection
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences

/-!
# Selecting the original paired natural source over a general even field

The genuine minimal-parabolic classification has a single or paired natural
source. Nonnormality of the original component excludes the single source.
In the paired symmetric-five source, its canonical alternating component
and Sylow conjugacy produce an actual A₅ quotient of the original L. This
contradicts the prescribed non-A₅ hypothesis, leaving the paired linear
source with its original quotient and exchanger.

The final application uses the actual even-field component quotient and
original H-star movement. Selecting that component model from the earlier
Chapter 10 alternatives remains with the moving-Hall assembly owner.
Source: Aschbacher–Smith E.2.3, 10.1.2(6), and 10.2.2(1), pp.216–217,742–744.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem not_quasisimple_source
    (hP : IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) ⊤)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X) →
      ¬ IsQuasisimple (generalizedFitting (offenderSubgroup α)) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ hqs
  have hcore : pCore 2 (X ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    change elementaryAbelianMaxJ (S : Subgroup X) ≤ C
    rw [←hk,he]
    exact le_top
  have hp := (minimalParabolic_reduced_image S hP q hq hcore hne).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk S
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top S).trans hf.1)).elim
    · exact hf
  have hr := (source_quasisimple_fitting_eq_residual (S.mapSurjective hq) hp Y
    (offender_generation (S.mapSurjective hq) hp α hff hcore).2 hqs).2
  have hker : q.ker ≤ minimalParabolicCore S hP := by
    rw [hk]
    exact RankOneBaumann.reduced_centralizer_le_core S hP U hU hJ
  let : Group.IsSolvable (minimalParabolicCore S hP) := minimalParabolic_core_solvable S hP
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective (inclusion_injective hker)
  have hL : (L.subgroupOf X).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hnormal := hL.normal_of_solvable_kernel_quasisimple_residual _ q hq hr
  exact hn (le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
    ((le_componentOrbit L T).trans le_sup_left)).mp hnormal))

set_option backward.isDefEq.respectTransparency false in
private theorem a5_quotient_of_paired_five
    (hP : IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) ⊤)
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)))
    (hp : SourcePairedFiveAction D) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
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
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hG := (D.local_internal_module hu).sqtk
  obtain ⟨d,t,ht₁,ht₂,⟨c⟩⟩ := hp
  let B := (alternatingGroup (Fin 5)).map
    (SymmetricFive.Paired.leftFactorMap Y c.action.groupEquiv)
  obtain ⟨K,hK,him,heK,hcan,hUK,hBK,hfit,R,hR⟩ :=
    first_five_component_geometry h36 hG S hP U hU hJ q hq hk
      (source_join_not_solvable D) (source_join_fitting D) d c ⟨t,ht₁,ht₂⟩
  have hJA : (elementaryAbelianMaxJ (S : Subgroup H)).map q ≤ Y :=
    ChapterB.RankOneBaumann.thompson_image_le_offender_layer S U q hq hk
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) Y le_rfl
  have hgen := selected_component_sup_sylow S hP U hU hJ q hq hk Y B hJA
    (five_first_axis_normalized Y c.action.groupEquiv) K hK hcan
  obtain ⟨s,hs⟩ := source_original_component_conjugate_of_generating_component D K hK hgen
  let a : K ≃* L := (((MulAut.conj (s:H)).subgroupMap K).trans
    (MulEquiv.subgroupCongr hs.symm)).trans
      (subgroupOfEquivOfLe ((le_componentOrbit L T).trans le_sup_left))
  exact ⟨(QuotientGroup.congr _ _ a.symm (pCore_map_iso 2 a.symm)).trans heK.some⟩

set_option backward.isDefEq.respectTransparency false in
theorem source_original_paired_linear_of_nona5_parabolic
    (hP : IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) ⊤)
    (ha : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)))
    :
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
  rcases source_nonsolvable_natural_factors hG S hP U hU (source_join_not_solvable D) hJ with
    ⟨hqs,_⟩ | ⟨d,_,_⟩
  · exact (not_quasisimple_source D hP hn hJ hqs).elim
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
    · exact (ha (a5_quotient_of_paired_five D hP hJ ⟨d,t,ht₁,ht₂,hfive⟩)).elim

/-- The original general-field component and moving H-star group determine
its actual paired natural source; no independent module-selection premise remains. -/
theorem Context.original_paired_linear
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) : SourceOriginalPairedLinear D :=
  source_original_paired_linear_of_nona5_parabolic D
    (source_natural_minimal_parabolic D e n hn hF ctx.nonnormal)
    ctx.not_a5 ctx.nonnormal
    (source_hstar_local_thompson_moves_of_omega_commutator D ctx.hstar ctx.moving)

end CFSG.Quasithin.Chapter10.MovingHall
