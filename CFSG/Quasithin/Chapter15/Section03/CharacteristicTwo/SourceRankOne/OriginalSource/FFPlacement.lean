module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Normality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.ExceptionalRankTwo
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.Alternating.Aut

/-!
# Direct placement from the actual FF component models

Every centerless model in the corrected B.5 list has abelian outer group.
The two remaining rows have center of order three. Thus the actual S₃
shadow forces inner action in every centerless row, and solvable-invariant
control gives Y₊ containment. The center-three rows contradict the original
component commutator. This uses the exact star component throughout and
avoids a stronger intrinsic central-cover model comparison.

Source: Aschbacher–Smith B.5.6 and15.3.27(2–3), printed pp.105,1131.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06
open RankOneConfiguration RankOneConfiguration.Parabolics Placement ModelComparison
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Chapter1.XiEmbedding.OuterModels

private theorem simple_perfect_center_eq_bot {X : Type*} [Group X]
    [IsSimpleGroup X] [Group.IsPerfect X] : center X = ⊥ := by
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp h)).elim

private theorem alternatingSeven_outer_commutative :
    IsMulCommutative (MulAut.Outer (alternatingGroup (Fin 7))) := by
  let A := alternatingGroup (Fin 7)
  have hc : Nat.card (Equiv.Perm (Fin 7) ⧸ A) = 2 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  let : IsCyclic (Equiv.Perm (Fin 7) ⧸ A) := isCyclic_of_prime_card hc
  let : IsCyclic (MulAut.Outer A) := isCyclic_of_surjective (MulAut.outerAction A) (by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
    obtain ⟨σ,rfl⟩ :=
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide)).surjective a
    exact ⟨QuotientGroup.mk' A σ,rfl⟩)
  infer_instance

private theorem symplectic_field_large (F : BinaryField)
    [Group.IsPerfect (Matrix.symplecticGroup (Fin 2) F.Carrier)] : 1 < F.degree := by
  by_contra hn
  have he : F.degree = 1 := by have := F.degree_pos; omega
  have hcF : Nat.card F.Carrier = 2 := by rw [F.card_eq, he]; rfl
  let e : Matrix.symplecticGroup (Fin 2) F.Carrier ≃* alternatingGroup (Fin 6) :=
    (topEquiv.symm.trans (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)).trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hcF)
  have hc := Nat.card_congr e.toEquiv
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, hcF, nat_card_alternatingGroup] at hc
  norm_num at hc

private theorem g2_field_large (F : BinaryField)
    [Group.IsPerfect (Atlas.G2.Model F.Carrier)] : 2 < Nat.card F.Carrier := by
  by_contra hn
  have hcF : Nat.card F.Carrier = 2 := by have := Finite.one_lt_card (α := F.Carrier); omega
  let e := Atlas.G2.fieldEquiv (Atlas.G2.binaryFieldEquiv hcF)
  let : Group.IsPerfect (Atlas.G2.Model (ZMod 2)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hc := Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
  change Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 at hc
  rw [Group.IsPerfect.commutator_eq_top, Nat.card_congr topEquiv.toEquiv,
    Atlas.G2.LieAutomorphismExtensions.card_binaryFull] at hc
  omega

/-- Only the star-model center and outer facts required by placement.
The nonperfect binary full Sp₄ and G₂ parameters are ruled out internally. -/
theorem ff_model_center_outer {X : Type*} [Group X] [Finite X] [IsQuasisimple X]
    (hm : QuasisimpleModel X) :
    (center X = ⊥ ∧ IsMulCommutative (MulAut.Outer X)) ∨ Nat.card (center X) = 3 := by
  cases hm with
  | linearTwo F e => exact Or.inl (RegularModel.center_and_outer (.linearTwo F e))
  | linearThree F e =>
    rcases Nat.even_or_odd F.degree with he | ho
    · exact Or.inr (center_card_three_of_even_linearThree F he e)
    · exact Or.inl (RegularModel.center_and_outer (.linearThree F ho e))
  | symplecticFour F e =>
    let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) F.Carrier) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card
      F.card_eq (symplectic_field_large F)
      Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
    exact Or.inl ⟨center_bot_of_equiv e Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot,
      commutative_of_equiv (MulAut.outerCongr e)⟩
  | g2 F e =>
    let : Group.IsPerfect (Atlas.G2.Model F.Carrier) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hlarge := g2_field_large F
    let := g2_outer_isCyclic_of_coverage
      (Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective (F := F.Carrier) hlarge)
    exact Or.inl ⟨center_bot_of_equiv e (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hlarge),
      commutative_of_equiv (MulAut.outerCongr e)⟩
  | alternatingSix e =>
    let := AlternatingSix.ShadowLocal.outer_isMulCommutative
    exact Or.inl ⟨center_bot_of_equiv e (alternatingGroup.center_eq_bot (by simp)),
      commutative_of_equiv (MulAut.outerCongr e)⟩
  | alternatingSeven e =>
    let := alternatingSeven_outer_commutative
    exact Or.inl ⟨center_bot_of_equiv e (alternatingGroup.center_eq_bot (by simp)),
      commutative_of_equiv (MulAut.outerCongr e)⟩
  | tripleSix e _ =>
    exact Or.inr ((Nat.card_congr e.toEquiv).trans (Nat.card_zmod 3))
  | g2DerivedTwo e =>
    let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := Atlas.G2.isSimple_commutator_binary
    let : IsSimpleGroup X := e.isSimpleGroup
    let := g2_derived_outer_isCyclic_of_coverage
      Atlas.G2.LieAutomorphismExtensions.binaryConjugation_surjective
    exact Or.inl ⟨simple_perfect_center_eq_bot, commutative_of_equiv (MulAut.outerCongr e)⟩
  | linearFourTwo e =>
    let := BinaryLinear.OuterCyclic.linear_outer_isCyclic (Or.inl rfl : 4 = 4 ∨ 4 = 5)
    exact Or.inl ⟨center_bot_of_equiv e (BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide)),
      commutative_of_equiv (MulAut.outerCongr (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 4)))⟩
  | linearFiveTwo e =>
    let := BinaryLinear.OuterCyclic.linear_outer_isCyclic (Or.inr rfl : 5 = 4 ∨ 5 = 5)
    exact Or.inl ⟨center_bot_of_equiv e (BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide)),
      commutative_of_equiv (MulAut.outerCongr (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 5)))⟩

/-- Original15.3.27(2) from the actual corrected FF model and original normality. -/
theorem source_lemma_15_3_27_2
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) : d.Yplus ≤ c.L := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have h := source_lemma_15_3_26_1 hG d hempty hM hu hmany hshadow hI
  have hn := source_lemma_15_3_27_1 hG d hempty hM hu hmany hshadow hI hf c
  have hcontrol : SolvableInvariantControl d I :=
    source_lemma_15_3_26_3 hG d hempty hM hu hmany hI hf
  let _ := c.star_quasisimple
  apply yplus_le_component_of_comparison d hI c h hcontrol hn h11.theta_eq.symm
  rcases ff_model_center_outer (component_star_ff_model hG d hI hf c h11.sylow) with ⟨hz,ho⟩ | hc
  · exact Or.inr (Or.inl ⟨hz,inner_action_of_shadow d hI c h hn ho⟩)
  · exact Or.inr (Or.inr hc)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
