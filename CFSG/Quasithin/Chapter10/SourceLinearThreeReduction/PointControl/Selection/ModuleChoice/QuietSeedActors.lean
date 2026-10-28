module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.ThompsonComparison
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietSeed
public import Theory.Representation.BinaryTensorThree.ConstituentStability
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant
public import CFSG.Quasithin.ChapterD.Section03.PerfectCentralizer

/-!
# Cubic actors preserve the original quiet binary-three seed

The faithful full action retains the normal image of L₀ and the actual
three-free centralizer. The normal perfect centralizer theorem makes every
starred actor faithful on that image. Its literal SL₃(2) square marking
bounds the actor rank by four, hence full displacement by eight.

The original irreducible seed has degree at least nine. Transport through
the unchanged full-action quotient therefore makes each starred actor's
entire preimage preserve it. The genuine cubic bound supplies such an actor;
no actor selection, faithfulness or stability is an additional premise.
The proper-seed exclusion and the separate quiet rank-one branch remain
with ModuleChoice.Source.
Source: Aschbacher--Smith D.3.9, D.3.21 and original3.2.6,
printed pp.199--207,581 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 CentralHall.Nonlinear.Modules
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original full-action cubic actors are faithful on the actual component
square. The full centralizer kernel and the original SQTK cover are retained. -/
theorem quiet_full_actor_starred_faithful
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    ∀ A ∈ ChapterD.QhatStar ρ,
      A ⊓ centralizer (X : Set _) = ⊥ := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let Q := M ⧸ centralizer (U : Set M)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect R := isPerfect_iSup_conjugates L T
  let eR := subgroupOfEquivOfLe R.le_normalizer
  let : Group.IsPerfect (R.subgroupOf M) :=
    Group.IsPerfect.ofSurjective (f := eR.symm.toMonoidHom) eR.symm.surjective
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap (R.subgroupOf M)) (q.subgroupMap_surjective _)
  have hi := quiet_full_action_irreducible D hmany hmin hJ
  have hf := ChapterB.InternalThompsonAction.action_faithful U
  have hXn : X ≠ ⊥ := by
    obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
    have hc := (full_action_component_pair D ht htn).1
    intro he
    apply hc.isCComponent.ne_bot
    exact bot_unique ((map_mono (comap_mono (le_componentOrbit L T))).trans he.le)
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple Q := {
    Cover := M
    kernel := centralizer (U : Set M)
    sqtk := D.simpleQTKE.twoLocal_sqtk
      (source_module_nonsolvable_uniqueness D).normalizer_maximal.1
    equiv := MulEquiv.refl Q }
  intro A hA
  exact ChapterD.starred_inf_perfect_centralizer_eq_bot ρ hf hu.quotient_pCore_eq_bot c X
    (subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf hi X hXn)
    (fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi X hXn)
    (original_full_actor_centralizer_three_free D hn hd) hA

/-- Every original starred actor in the quiet binary-three branch has rank
at most four and moves at most eight dimensions of the original full module. -/
theorem quiet_binaryThree_starred_rank_and_codimension
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let ρ := ChapterB.InternalThompsonAction.action U
    ∀ A ∈ ChapterD.QhatStar ρ, rank A ≤ 4 ∧ fixedCodim ρ A ≤ 8 := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  obtain ⟨p,hp,hpk,_,_⟩ := original_component_product_quotient D hn ht htn
  obtain ⟨i,hi,_,hdiagram⟩ := original_component_product_embedding D hn p hp hpk
  have hrange : i.range = X := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      obtain ⟨x,rfl⟩ := hp a
      rw [hdiagram]
      exact ⟨inclusion R.le_normalizer x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨p ⟨x,hx⟩,hdiagram ⟨x,hx⟩⟩
  let e := (MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hi).symm
  let f := cL.trans (Matrix.PSL3Two.equivGL.trans
    ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryTensorThree.Natural)))
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr cL.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  intro A hA
  have hAC := quiet_full_actor_starred_faithful D hmany hmin hn hJ hd A hA
  have hr := BinaryTensorThree.rank_le_four_of_faithful_on_tensor_base X A hA.1.2.1 hAC
    (e.trans (f.prodCongr f))
  have hb := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)
  exact ⟨hr,hb.trans (by omega)⟩

/-- The complete preimage of every original starred cubic actor preserves
 the unchanged quiet seed. No actor-stability premise is supplied. -/
theorem quiet_binaryThree_starred_preserves_seed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hfix : D.fullModule ⊓ centralizer (L : Set G) = ⊥) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ∀ A ∈ ChapterD.QhatStar ρ, ∀ m : D.maximalLocal, q m ∈ A →
      (m : G) ∈ normalizer (D.seed : Set G) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  let a : U ≃* D.fullModule := subgroupOfEquivOfLe hVM
  let E : Additive U ≃ₗ[ZMod 2] Additive D.fullModule :=
    a.toAdditive.toLinearEquiv (fun c v => ZMod.map_smul a.toAdditive.toAddMonoidHom c v)
  intro A hA m hm
  have hb := (quiet_binaryThree_starred_rank_and_codimension D hmany hmin hn hJ cL A hA).2
  have he : NaturalTensor.operatorFixedCodim (ρ (q m)) =
      NaturalTensor.operatorFixedCodim (originalFullAction D m) := by
    apply NaturalTensor.operatorFixedCodim_eq_of_equiv _ _ E
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun x : M => (x : G)) (ChapterB.InternalThompsonAction.action_apply U m v)
  have hm' := NaturalTensor.operatorFixedCodim_le_fixedCodim ρ A hm
  rw [he] at hm'
  exact quiet_binaryThree_seed_stable_of_displacement_lt_nine D hmany hn hJ cL hfix m
    (lt_of_le_of_lt (hm'.trans hb) (by decide))

/-- The source cubic bound supplies an actual nontrivial elementary actor,
whose entire preimage preserves the original seed. -/
theorem quiet_binaryThree_exists_stable_starred_actor
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hfix : D.fullModule ⊓ centralizer (L : Set G) = ⊥) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ∃ A ∈ ChapterD.QhatStar ρ, rank A ≤ 4 ∧ fixedCodim ρ A ≤ 8 ∧
      ∀ m : D.maximalLocal, q m ∈ A → (m : G) ∈ normalizer (D.seed : Set G) := by
  dsimp only
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let ρ := ChapterB.InternalThompsonAction.action U
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr
    (source_full_module_cubic_bound_of_many D hmany)
  have hb := quiet_binaryThree_starred_rank_and_codimension D hmany hmin hn hJ cL A hA
  exact ⟨A,hA,hb.1,hb.2,
    quiet_binaryThree_starred_preserves_seed D hmany hmin hn hJ cL hfix A hA⟩
end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
