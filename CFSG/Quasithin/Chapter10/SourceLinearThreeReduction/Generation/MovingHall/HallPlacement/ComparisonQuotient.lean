module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.ActionPlacement

/-!
# The original comparison quotient and its restricted action

The H-star natural alternatives identify the single comparison modulo its
two-core as binary SL₂. Restricting the genuine containing-orbit action
to the smaller component has two-group kernel, because that kernel fixes
the original H-orbit. Its two-core quotient therefore preserves the original
comparison quotient. No equality between the containing action kernel and
its two-core is required.

Source: Aschbacher–Smith 10.2.3, printed pp.745–746; E.2.3 and B.5.1.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterE.ThompsonAction
open ChapterC.RankOne.ChiProduct.SelectedRankOne
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- The original single comparison has a binary rank-one two-core quotient. -/
theorem ComparisonConfiguration.single_linear_quotient
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e) :
    ∃ E : BinaryField, 1 < E.degree ∧
      Nonempty ((c.component ⧸ pCore 2 c.component) ≃* SL(2,E.Carrier)) := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D ctx.hstar
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hCZ := seed_centralizer_eq_sylow D ctx n hn hF e mark
  have hkc : q.ker = pCore 2 H := hk.trans
    (source_hstar_action_kernel_eq_core_of_seed_centralizer D ctx.hstar hCZ)
  have hP := source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large
  have hJ := ctx.hstar_thompson_moves_omega_orbit D n hn hF e
  have hfit := source_hstar_fitting_eq_core D ctx.hstar
  have hsq := Chapter3.sqtk_of_mem_H D.simpleQTKE ctx.hstar.1.1.1
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (ChapterE.generationParameter_le_one_of_solvable (G := H))) ctx.large
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hmodel : ∃ E : BinaryField,
      Nonempty ((c.component ⧸ pCore 2 c.component) ≃* SL(2,E.Carrier)) := by
    rcases ctx.hstar_linear_alternatives_of_seed_centralizer D n hn hF e hCZ with
      ⟨hqs,a,E,⟨aE⟩⟩ | ⟨d,E,⟨a⟩,hexchange⟩
    · let A := generalizedFitting Y
      let := hqs
      have hcore : pCore 2 (H ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
      have hne : q.ker ≠ ⊤ := by
        intro ht
        exact hJ (hk ▸ (ht ▸ le_top))
      have hp := (minimalParabolic_reduced_image S hP q hq hcore hne).2
      have hff : IsFFModule α := by
        obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk S
        · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top S).trans hf.1)).elim
        · exact hf
      have hA := (source_quasisimple_fitting_eq_residual (S.mapSurjective hq) hp Y
        (offender_generation (S.mapSurjective hq) hp α hff hcore).2 hqs).1
      have hmap : c.component.map q = A.map Y.subtype := by
        rw [hsingle,map_pResidual_of_surjective 2 q hq]
        exact hA.symm
      have hkernel : (q.subgroupMap c.component).ker = pCore 2 c.component := by
        rw [ker_subgroupMap,hkc,pCore_subnormal_eq_comap 2 c.component_isCComponent.subnormal]
        rfl
      exact ⟨E,⟨((QuotientGroup.quotientMulEquivOfEq hkernel.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective c.component))).trans
          ((MulEquiv.subgroupCongr hmap).trans
            ((A.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans aE.groupEquiv))⟩⟩
    · obtain ⟨K,hK,_,_,_,_,_,_,_,hE,_,t,ht,hcover⟩ :=
        first_component_localClass_with_coverage h36 hsq S hP U hU hJ q hq hk hkc
          hs hfit d E a hexchange
      have hle : K ≤ c.component := by rw [hsingle,hcover]; exact le_sup_left
      have he := hK.eq_of_le c.component_isCComponent hle
      rw [he] at hE
      exact ⟨E,hE⟩
  obtain ⟨E,⟨a⟩⟩ := hmodel
  let := c.component_isCComponent.perfect
  let : Group.IsPerfect (c.component ⧸ pCore 2 c.component) := inferInstance
  let : Nontrivial (c.component ⧸ pCore 2 c.component) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [Nat.card_congr a.toEquiv,GorensteinWalter.sl2_card_formula]
      have hq : 2 ≤ Nat.card E.Carrier := Finite.one_lt_card
      have hs : 3 ≤ Nat.card E.Carrier ^ 2 - 1 := by
        have hs : 4 ≤ Nat.card E.Carrier ^ 2 := by nlinarith
        omega
      nlinarith)
  have hlarge := ChapterE.ThompsonAction.perfect_linear_two_field_large E a
  have hdegree : 1 < E.degree := by
    rw [E.card_eq] at hlarge
    by_contra h
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show E.degree ≤ 1 by omega)
    norm_num at hh
    omega
  exact ⟨E,hdegree,⟨a⟩⟩

/-- The restricted comparison action has a two-group kernel and preserves the original smaller quotient. -/
theorem ComparisonConfiguration.small_local_quotient
    (c : ComparisonConfiguration D ctx)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e) :
    let J := c.join D
    letI := (c.orbit_reduced D).normal
    let q := actionMk (c.orbit D)
    let A := (c.overcomponent.subgroupOf J).map q
    let K := ((c.component.map H.subtype).subgroupOf J).map q
    Nonempty (((K.subgroupOf A) ⧸ pCore 2 (K.subgroupOf A)) ≃*
      (c.component ⧸ pCore 2 c.component)) := by
  let J := c.join D
  let K := (c.component.map H.subtype).subgroupOf J
  let := (c.orbit_reduced D).normal
  let q := actionMk (c.orbit D)
  let A := (c.overcomponent.subgroupOf J).map q
  let k : c.component →* K := {
    toFun := fun x => ⟨⟨x.val,c.original_le_join D x.val.property⟩,
      mem_map_of_mem H.subtype x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hk : Function.Surjective k := by
    rintro ⟨j,hj⟩
    obtain ⟨x,hx,he⟩ := hj
    exact ⟨⟨x,hx⟩,Subtype.ext (Subtype.ext he)⟩
  let f := (q.subgroupMap K).comp k
  have hf : Function.Surjective f := (q.subgroupMap_surjective K).comp hk
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hcore : centralizer (U : Set H) = pCore 2 H :=
    source_hstar_action_kernel_eq_core_of_seed_centralizer D ctx.hstar
      (seed_centralizer_eq_sylow D ctx n hn hF e mark)
  have hker : ∀ x : f.ker, (x.val.val : H) ∈ pCore 2 H := by
    intro x
    rw [←hcore]
    have hq : q (k x.val).val = 1 := congrArg Subtype.val x.property
    have hc : (k x.val).val ∈ centralizer (c.orbit D : Set J) :=
      (QuotientGroup.eq_one_iff _).mp hq
    intro w hw
    have hwJ : (w:G) ∈ J := c.original_le_join D w.property
    have hwO : (⟨w,hwJ⟩ : J) ∈ c.orbit D :=
      conjugateSpanBy_mono le_rfl (c.original_le_join D) hw
    exact Subtype.ext (congrArg J.subtype (hc ⟨w,hwJ⟩ hwO))
  let j : f.ker →* pCore 2 H := {
    toFun := fun x => ⟨x.val.val,hker x⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 H => (z : H)) h))
  have htwo : IsPGroup 2 f.ker := pCore_isPGroup.of_injective j hj
  have hKA : K.map q ≤ A := map_mono (comap_mono c.component_le)
  let b := subgroupOfEquivOfLe hKA
  exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
    (f.pCoreQuotientEquiv hf htwo).symm⟩

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
