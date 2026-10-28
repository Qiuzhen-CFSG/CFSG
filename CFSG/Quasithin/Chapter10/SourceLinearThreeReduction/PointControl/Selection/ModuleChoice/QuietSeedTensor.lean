module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietSeedActors
public import Theory.Representation.BinaryTensorThree.ConstituentExhaustion
public import Theory.Representation.PSL3Two.ProductTensorRecognition
public import Theory.Representation.PSL3Two.SteinbergSquareActors
public import Theory.Representation.PSL3Two.MixedTensorActors

/-!
# Excluding the original quiet tensor seeds

The exact O₂(L₀) quotient of the seed embeds in the original full action.
The starred actor is faithful on that normal square and satisfies the same
fixed-codimension budget. Natural tensor constituent exhaustion makes the
original seed equal the full module. The Steinberg-square constituent bound
excludes that type even when the original seed is proper. Both transports
retain the actual seed inclusion and the full ambient action kernel.

Product-catalogue recognition supplies the actual tensor coordinates in each
case. ModuleChoice.Source applies the existing ambient tensor contradiction
and excludes the remaining mixed24-dimensional seed using the same actor
and full action kernel. Its factor cubic displacements distinguish the
two actual tensor factors.
Source: Aschbacher--Smith D.3.7--9 and3.2.6, printed pp.197--200,581;
original10.1.1--3, pp.741--742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 CentralHall.Nonlinear.Modules
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem quiet_seed_full_action_embedding
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (q : localOrbit T L →* BinaryLinearThree.Group × BinaryLinearThree.Group)
    (hq : Function.Surjective q) (hk : q.ker = pCore 2 (localOrbit T L))
    (σ : Representation (ZMod 2) (BinaryLinearThree.Group × BinaryLinearThree.Group)
      (Additive D.seed)) (hσ : σ.comp q = originalSeedAction D) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let qM := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    ∃ j : (BinaryLinearThree.Group × BinaryLinearThree.Group) →* _,
      Function.Injective j ∧
      j.range = ((localOrbit T L).subgroupOf D.maximalLocal).map qM ∧
      ∃ f : σ.IntertwiningMap (ρ.comp j), Function.Injective f ∧
        ∀ v, (((f v).toMul : D.maximalLocal) : G) = (v.toMul : G) := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let qM := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let c := cL.prodCongr cL
  let p := c.symm.toMonoidHom.comp q
  have hp : Function.Surjective p := c.symm.surjective.comp hq
  have hpk : p.ker = pCore 2 R := by
    rw [MonoidHom.ker_comp_of_injective _ c.symm.toMonoidHom c.symm.injective,hk]
  obtain ⟨i,hi,_,hdiagram⟩ := original_component_product_embedding D hn p hp hpk
  let j := i.comp c.symm.toMonoidHom
  have hj : Function.Injective j := hi.comp c.symm.injective
  have hjq (x : R) : j (q x) = qM (inclusion R.le_normalizer x) := hdiagram x
  let X := (R.subgroupOf M).map qM
  have hrange : j.range = X := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      obtain ⟨x,rfl⟩ := hq a
      rw [hjq]
      exact ⟨inclusion R.le_normalizer x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨q ⟨x,hx⟩,hjq ⟨x,hx⟩⟩
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Normal.map inferInstance qM (QuotientGroup.mk'_surjective _)
  let : j.range.Normal := hrange.symm ▸ inferInstanceAs X.Normal
  have hSF : D.seed ≤ D.fullModule :=
    (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)
  have hFM : D.fullModule ≤ M := D.fullModule_le_orbit.trans R.le_normalizer
  let a : U ≃* D.fullModule := subgroupOfEquivOfLe hFM
  let fG : D.seed →* U := a.symm.toMonoidHom.comp (inclusion hSF)
  let fL : Additive D.seed →ₗ[ZMod 2] Additive U := fG.toAdditive.toZModLinearMap 2
  let f : σ.IntertwiningMap (ρ.comp j) := {
    toLinearMap := fL
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      obtain ⟨x,rfl⟩ := hq g
      have he := LinearMap.congr_fun (DFunLike.congr_fun hσ x) v
      change σ (q x) v = originalSeedAction D x v at he
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change ((σ (q x) v).toMul : G) = (((ρ (j (q x)) (fL v)).toMul : M) : G)
      rw [he,hjq]
      exact (congrArg (fun z : M => (z : G))
        (ChapterB.InternalThompsonAction.action_apply U (inclusion R.le_normalizer x) (fL v))).symm }
  have hf : Function.Injective f := by
    intro v w he
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z : Additive U => ((z.toMul : M) : G)) he
  exact ⟨j,hj,hrange,f,hf,fun _ => rfl⟩

/-- A natural tensor marking on the unchanged seed forces it to exhaust the
original full module. The ambient actor and its full kernel are unchanged. -/
theorem quiet_binaryThree_natural_seed_eq_full
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (q : localOrbit T L →* BinaryLinearThree.Group × BinaryLinearThree.Group)
    (hq : Function.Surjective q) (hk : q.ker = pCore 2 (localOrbit T L))
    (σ : Representation (ZMod 2) (BinaryLinearThree.Group × BinaryLinearThree.Group)
      (Additive D.seed)) (hσ : σ.comp q = originalSeedAction D)
    (e : (BinaryLinearThree.Group × BinaryLinearThree.Group) ≃*
      (BinaryTensorThree.Factor × BinaryTensorThree.Factor))
    (b : σ.Equiv (BinaryTensorThree.baseRepresentation.comp e.toMonoidHom)) :
    D.seed = D.fullModule := by
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let qM := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map qM
  obtain ⟨j,hj,hrange,f,hf,hval⟩ := quiet_seed_full_action_embedding D hn cL q hq hk σ hσ
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Normal.map inferInstance qM (QuotientGroup.mk'_surjective _)
  let : j.range.Normal := hrange.symm ▸ inferInstanceAs X.Normal
  let : Nontrivial D.seed := (nontrivial_iff_ne_bot D.seed).mpr D.seed_ne_bot
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr
    (source_full_module_cubic_bound_of_many D hmany)
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr cL.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  have hAC : A ⊓ centralizer (j.range : Set _) = ⊥ := by
    rw [hrange]
    exact quiet_full_actor_starred_faithful D hmany hmin hn hJ hd A hA
  have hbudget := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
    (hA.1.2.2.2.le.trans hA.1.1)
  have hsurj := BinaryTensorThree.tensor_intertwiner_surjective ρ
    (quiet_full_action_irreducible D hmany hmin hJ) j hj σ f hf e b A hA.1.2.1 hAC hbudget
  have hSF : D.seed ≤ D.fullModule :=
    (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)
  have hFM : D.fullModule ≤ M := D.fullModule_le_orbit.trans R.le_normalizer
  let a : U ≃* D.fullModule := subgroupOfEquivOfLe hFM
  apply le_antisymm hSF
  intro v hv
  obtain ⟨w,hw⟩ := hsurj (Additive.ofMul (a.symm ⟨v,hv⟩))
  have he := congrArg (fun z : Additive U => ((z.toMul : M) : G)) hw
  have he' : (w.toMul : G) = v := (hval w).symm.trans he
  exact he' ▸ w.toMul.property

/-- The catalogue and the actual actor force any original quiet seed below
degree24 to be the whole full module. -/
theorem quiet_binaryThree_seed_eq_full_of_degree_lt_twentyFour
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hfix : D.fullModule ⊓ centralizer (L : Set G) = ⊥)
    (hd : Module.finrank (ZMod 2) (Additive D.seed) < 24) : D.seed = D.fullModule := by
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  obtain ⟨q,hq,hk,_,_,σ,_,_,hσ,_,a,b,⟨d⟩,_⟩ :=
    quiet_binaryThree_seed_marking_of_no_component_fixed D hmany hn hJ cL hfix ht htn
  obtain ⟨e,⟨c⟩⟩ := BinaryLinearThree.ProductCatalogue.natural_tensor_marking_of_degree_lt_twentyFour
    σ a b d hd
  exact quiet_binaryThree_natural_seed_eq_full D hmany hmin hn hJ cL q hq hk σ hσ e c
/-- A Steinberg-square marking on the original quiet seed contradicts the
same full-action cubic actor, even when that seed is proper. -/
theorem quiet_binaryThree_steinberg_seed_impossible
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (q : localOrbit T L →* BinaryLinearThree.Group × BinaryLinearThree.Group)
    (hq : Function.Surjective q) (hk : q.ker = pCore 2 (localOrbit T L))
    (σ : Representation (ZMod 2) (BinaryLinearThree.Group × BinaryLinearThree.Group)
      (Additive D.seed)) (hσ : σ.comp q = originalSeedAction D)
    (hiσ : Function.Injective σ) (hirr : σ.IsIrreducible)
    (b : σ.Equiv (Representation.QuadraticFourGroup.TensorClassification.externalTensor
      BinaryLinearThree.S BinaryLinearThree.S)) : False := by
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let qM := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map qM
  obtain ⟨j,hj,hrange,f,hf,hval⟩ := quiet_seed_full_action_embedding D hn cL q hq hk σ hσ
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Normal.map inferInstance qM (QuotientGroup.mk'_surjective _)
  let : j.range.Normal := hrange.symm ▸ inferInstanceAs X.Normal
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr
    (source_full_module_cubic_bound_of_many D hmany)
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr cL.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  have hAC : A ⊓ centralizer (j.range : Set _) = ⊥ := by
    rw [hrange]
    exact quiet_full_actor_starred_faithful D hmany hmin hn hJ hd A hA
  have hbudget := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
    (hA.1.2.2.2.le.trans hA.1.1)
  exact BinaryLinearThree.SteinbergSquare.constituent_impossible ρ j hj σ hiσ hirr b f hf
    A hA.1.2.1 hAC hA.1.2.2.1 hbudget

/-- The original quiet seed cannot have degree64: its product catalogue
would mark it as the excluded Steinberg square. -/
theorem quiet_binaryThree_seed_degree_ne_sixtyFour
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hfix : D.fullModule ⊓ centralizer (L : Set G) = ⊥) :
    Module.finrank (ZMod 2) (Additive D.seed) ≠ 64 := by
  intro hdim
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  obtain ⟨q,hq,hk,_,_,σ,hirr,hiσ,hσ,_,a,b,⟨d⟩,hd⟩ :=
    quiet_binaryThree_seed_marking_of_no_component_fixed D hmany hn hJ cL hfix ht htn
  rw [hd] at hdim
  cases a <;> cases b <;> norm_num [BinaryLinearThree.ProductCatalogue.FactorType.degree] at hdim
  exact quiet_binaryThree_steinberg_seed_impossible D hmany hmin hn hJ cL q hq hk σ hσ hiσ hirr d

/-- The same original starred actor excludes every mixed natural/Steinberg
marking, including a proper seed and both factor orientations. -/
theorem quiet_binaryThree_mixed_seed_impossible
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (q : localOrbit T L →* BinaryLinearThree.Group × BinaryLinearThree.Group)
    (hq : Function.Surjective q) (hk : q.ker = pCore 2 (localOrbit T L))
    (σ : Representation (ZMod 2) (BinaryLinearThree.Group × BinaryLinearThree.Group)
      (Additive D.seed)) (hσ : σ.comp q = originalSeedAction D)
    (hirr : σ.IsIrreducible)
    (a₀ b₀ : BinaryLinearThree.ProductCatalogue.FactorType)
    (hdegree : a₀.degree * b₀.degree = 24)
    (b : σ.Equiv (Representation.QuadraticFourGroup.TensorClassification.externalTensor
      a₀.action b₀.action)) : False := by
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let qM := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map qM
  obtain ⟨j,hj,hrange,f,hf,hval⟩ := quiet_seed_full_action_embedding D hn cL q hq hk σ hσ
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Normal.map inferInstance qM (QuotientGroup.mk'_surjective _)
  let : j.range.Normal := hrange.symm ▸ inferInstanceAs X.Normal
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr
    (source_full_module_cubic_bound_of_many D hmany)
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr cL.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  have hAC : A ⊓ centralizer (j.range : Set _) = ⊥ := by
    rw [hrange]
    exact quiet_full_actor_starred_faithful D hmany hmin hn hJ hd A hA
  have hbudget := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
    (hA.1.2.2.2.le.trans hA.1.1)
  exact BinaryLinearThree.MixedTensor.constituent_impossible ρ j hj σ hirr a₀ b₀ hdegree b f hf
    A hA.1.2.1 hAC hbudget

/-- The genuine product catalogue cannot mark the original quiet seed with
degree24, because its actual mixed coordinates contradict the actor budget. -/
theorem quiet_binaryThree_seed_degree_ne_twentyFour
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hfix : D.fullModule ⊓ centralizer (L : Set G) = ⊥) :
    Module.finrank (ZMod 2) (Additive D.seed) ≠ 24 := by
  intro hdim
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  obtain ⟨q,hq,hk,_,_,σ,hirr,hiσ,hσ,_,a,b,⟨d⟩,hd⟩ :=
    quiet_binaryThree_seed_marking_of_no_component_fixed D hmany hn hJ cL hfix ht htn
  have hdegree : a.degree * b.degree = 24 := hd.symm.trans hdim
  exact quiet_binaryThree_mixed_seed_impossible D hmany hmin hn hJ cL q hq hk σ hσ hirr
    a b hdegree d

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
