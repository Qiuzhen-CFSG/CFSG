module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentRankOne
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FullNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.SourceComparison
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.NormalizerTransport
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.RankOneExclusions
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.ModelRank

/-!
# FF obstructions for the literal Suzuki and unitary quotient models

For a chosen Irr⁺ module, adjoin an offender from its full linear normalizer
to the actual component image. The B.5.1 component in that supplement has
positive three-rank in every classified row. The literal projection from
J/O₂(J) therefore excludes every three-free quotient, in particular Suzuki.

In the unitary row the same supplement has trivial two-core and quasisimple
generalized Fitting subgroup. Its moved central quotient is faithful and
irreducible on the component, even if the original chosen module has a
nonzero fixed layer. The proved unitary quadratic-ratio theorem gives ratio
two, contradicting the retained offender. All projection maps and the
original PSU₃ field parameter are preserved.

RankOneFFSource applies both obstructions to the actual containing component
and connects the surviving PSL₂ model to the parameter/outside-component
conclusion. The full embedding sieve and source FF existence are separate
remaining steps; these lemmas do not assert unconditional 11.3.5.
Source: Aschbacher--Smith, 11.3.5, printed pp.771--772, using B.5.1,
B.4.2 and K.3.6, printed pp.99--103,86,457.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open Representation.BinaryOffender.Homogeneous
universe u

private theorem linear_three_rank_pos (F : BinaryField) {d : ℕ} (hd : 2 ≤ d) :
    0 < primeRank 3 (Matrix.SpecialLinearGroup (Fin d) F.Carrier) := by
  have h3 := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F.Carrier) (i := (⟨0, by omega⟩ : Fin d)) (j := (⟨1, by omega⟩ : Fin d))
    (Fin.ne_of_val_ne (by change (0 : ℕ) ≠ 1; decide))
  apply Nat.pos_of_ne_zero
  intro hz
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    ((h3.trans (card_subgroup_dvd_card _)).trans
      (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (center
        (Matrix.SpecialLinearGroup (Fin d) F.Carrier)))
        (QuotientGroup.mk'_surjective _)))

private theorem ff_component_three_rank_pos
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) X W} {C : Subgroup X}
    (b : ProjectiveLine.QuasisimpleSourceConclusion ρ C) : 0 < primeRank 3 C := by
  cases b.clause_one with
  | irreducible _ _ _ c _ => exact HighThreeRank.CoverCentralizer.action_case_rank_pos c
  | doubleThree F _ e _ _ =>
    rw [primeRank_equiv 3 e.groupEquiv]
    exact linear_three_rank_pos F (by decide)
  | naturalDual d hd _ h =>
    obtain ⟨e⟩ := h
    rw [primeRank_equiv 3 e.groupEquiv]
    exact linear_three_rank_pos BinaryField.two (by omega)
  | repeatedNatural d r hd _ _ _ h =>
    obtain ⟨e⟩ := h
    rw [primeRank_equiv 3 e.groupEquiv]
    exact linear_three_rank_pos BinaryField.two (by omega)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {J W : Subgroup G}

/-- A full-normalizer offender forces a cubic in the actual quotient image. -/
theorem chosen_no_ff_of_three_free_quotient (E : Chapter12.Section02.ChosenModule T J W)
    (hJ : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (hthree : ¬ 3 ∣ Nat.card (J ⧸ pCore 2 J)) :
    ¬ IsFFModule (normalizerRepresentation E.chosenAction) := by
  intro hff
  have hff' := E.chosen_normalizer_ff_iff_seedComponent.mp hff
  obtain ⟨A,hA,hC,⟨b⟩⟩ := E.full_normalizer_source_conclusion hJ hff'
  let := supplement_finite E.seedComponentAction A
  let c := E.normalizerOffenderComparison A hC
  have hz : primeRank 3 (J ⧸ pCore 2 J) = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr hthree
  have hc := PrimeRank.eq_zero_of_surjective c.projection c.surjective hz
  exact (Nat.ne_of_gt (ff_component_three_rank_pos b)) hc

/-- Every nondegenerate Suzuki quotient excludes FF on the original chosen space. -/
theorem chosen_suzuki_no_ff (E : Chapter12.Section02.ChosenModule T J W)
    (hJ : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    {m : ℕ} (hm : 1 ≤ m)
    (he : Nonempty ((J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    ¬ IsFFModule (normalizerRepresentation E.chosenAction) := by
  apply chosen_no_ff_of_three_free_quotient E hJ
  rw [Nat.card_congr he.some.toEquiv]
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)
private theorem unitary_simple {X : Type*} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU X 3 (2 ^ n)) : IsSimpleGroup X := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J (2 ^ n)
      ((by decide : 2 < 2 ^ 2).trans_le (Nat.pow_le_pow_right (by decide) hn)) hcard
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj)
  exact e.isSimpleGroup

private theorem unitary_layer_no_ff
    {X U : Type*} [Group X] [Finite X] [AddCommGroup U] [Module (ZMod 2) U]
    [Module.Finite (ZMod 2) U] (ρ : Representation (ZMod 2) X U)
    (C : Subgroup X) [C.Normal] [IsQuasisimple C]
    (hi : IsIrrPlus ρ C ⊤) (hf : Function.Injective ρ)
    (hcore : pCore 2 X = ⊥) (hq : IsPGroup 2 (X ⧸ C))
    (hsC : IsSQTK KnownSimple.IsKnownSimple C)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU C 3 (2 ^ n)) :
    ¬ IsFFModule ρ := by
  intro hff
  let : IsSimpleGroup C := unitary_simple hn hm
  have hcoreC : pCore 2 C = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : C.Normal).isSubnormal,hcore]
    exact C.subtype.ker_eq_bot_iff.mpr C.subtype_injective
  have hfit := generalizedFitting_eq_of_quasisimple_two_quotient C hq hcore
  let s := MovedSection.ofNormal ρ C
  have hi' : IsIrrPlus ρ C s.space.toSubmodule := by
    rw [s.space_eq]
    change IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C)
    rw [hi.choose_spec.1]
    exact hi
  have hfaithC : Function.Injective (s.action.comp C.subtype) := by
    apply (s.action.comp C.subtype).ker_eq_bot_iff.mp
    apply bot_unique
    rw [←hcoreC]
    exact le_sSup ⟨inferInstance,IrreducibleBranch.component_kernel_isTwoGroup s hf⟩
  have hfaith : Function.Injective s.action := by
    apply IrreducibleBranch.faithful_of_fitting_restriction
    rwa [hfit]
  have hsX := IrreducibleBranch.sqtk_of_twoGroup_quotient
    ChapterB.ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups C hq hsC
  obtain ⟨B,hB⟩ := hff
  have hffs : IsFFModule s.action := ⟨B,IrreducibleBranch.moved_offender s hB⟩
  have hsrc := ChapterB.SourceClassification.source_hypotheses hsX hfit
    (inferInstance : IsQuasisimple C) hfaith
    (IrreducibleBranch.moved_action_irreducible s hi') hffs
  have hz : center C = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center C) inferInstance with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp hz)).elim
  let ez : (C ⧸ center C) ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact ChapterB.SourceClassification.not_ff_unitary hsrc hn (hm.of_mulEquiv ez) hffs

private theorem supplement_irrPlus
    {P U : Type u} [Group P] [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) P U) (hi : IsIrrPlus σ ⊤ ⊤)
    (A : Subgroup (linearNormalizer σ)) :
    IsIrrPlus (linearAction (supplement σ A)) (component σ A) ⊤ := by
  apply hi.of_intertwining σ (linearAction (supplement σ A))
    ((projection σ A).comp (topEquiv (G := P)).toMonoidHom)
    ((projection_surjective σ A).comp (topEquiv (G := P)).surjective)
    LinearMap.id (fun _ _ he => he)
  · intro l v
    rfl
  · exact Submodule.map_id _

private theorem supplement_core
    {P U : Type u} [Group P] [IsQuasisimple P]
    [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
    (σ : Representation (ZMod 2) P U) (hf : Function.Injective σ)
    (hi : IsIrrPlus σ ⊤ ⊤) (A : Subgroup (linearNormalizer σ)) :
    pCore 2 (supplement σ A) = ⊥ := by
  have hk : σ.ker ≤ center P := by
    rw [σ.ker_eq_bot_iff.mpr hf]
    exact bot_le
  let := component_quasisimple σ hk A
  let := component_normal σ A
  let := supplement_finite σ A
  have hl : componentLayer (component σ A) = ⊤ := top_unique
    (le_sSup (show IsComponent (component σ A) ⊤ from
      ⟨Subgroup.IsSubnormal.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩))
  have hc := IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes
    (linearAction (supplement σ A)) (supplement_irrPlus σ hi A) pCore_isPGroup
    (twoCore_centralizes_of_normal_layer_or_odd (component σ A) (.inl hl))
    (le_subspaceStabilizer _ ⊤ (fun _ _ _ _ => Submodule.mem_top))
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply linearAction_injective (supplement σ A)
  apply LinearMap.ext
  intro v
  simpa only [map_one,Module.End.one_apply,MonoidHom.comp_apply,Subgroup.subtype_apply]
    using hc Submodule.mem_top ⟨x,hx⟩

private theorem normalizer_unitary_no_ff
    {P U : Type u} [Group P] [Finite P] [IsQuasisimple P]
    [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
    (σ : Representation (ZMod 2) P U) (hf : Function.Injective σ)
    (hi : IsIrrPlus σ ⊤ ⊤) (hs : IsSQTK KnownSimple.IsKnownSimple P)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU P 3 (2 ^ n)) :
    ¬ IsFFModule (normalizerRepresentation σ) := by
  rintro ⟨A,hA⟩
  let := component_normal σ A
  let := supplement_finite σ A
  let e : P ≃* component σ A := MulEquiv.ofBijective (projection σ A)
    ⟨fun _ _ he => hf (congrArg (fun k : component σ A =>
      linearAction (supplement σ A) k) he),projection_surjective σ A⟩
  let : IsQuasisimple (component σ A) := IsQuasisimple.of_mulEquiv e
  have hq : IsPGroup 2 (supplement σ A ⧸ component σ A) := by
    let B := A.map (linearNormalizer σ).subtype
    let := hA.1.2
    have hb : IsPGroup 2 (B.subgroupOf (supplement σ A)) :=
      (IsElementaryAbelian.isPGroup (p := 2) (G := A)).map _ |>.comap_subtype
    exact quotient_isPGroup_of_sup_eq_top (B.subgroupOf (supplement σ A)) (component σ A) hb
      ((sup_comm _ _).trans (codisjoint_subgroupOf_sup (actionImage σ) B).eq_top)
  exact unitary_layer_no_ff (linearAction (supplement σ A)) (component σ A)
    (supplement_irrPlus σ hi A) (linearAction_injective _) (supplement_core σ hf hi A)
    hq ((IsSQTK.equiv e).mp hs) hn (hm.of_mulEquiv e.symm) (supplement_ff σ A hA)

/-- The literal unitary quotient excludes FF for the full normalizer on the
unchanged chosen space, including its possibly nonsplit fixed layer. -/
theorem chosen_unitary_no_ff (E : Chapter12.Section02.ChosenModule T J W)
    (hJ : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 (2 ^ n)) :
    ¬ IsFFModule (normalizerRepresentation E.chosenAction) := by
  have hsJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe
      (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left))).mp
      (hJ.join_sqtk.subgroup (J.subgroupOf (J ⊔ (T : Subgroup G))))
  let := hJ.quasisimple
  have hf := E.quotientAction_injective (unitary_simple hn hm)
  intro hff
  apply normalizer_unitary_no_ff E.quotientAction hf E.quotientAction_irrPlus
    (ChapterE.Structure.sqtk_two_quotient hsJ (pCore 2 J) pCore_isPGroup) hn hm
  exact (Chapter12.Section02.ModuleClassification.normalizer_ff_iff_of_surjective
    E.chosenAction E.quotientAction (QuotientGroup.mk' (pCore 2 J))
    (QuotientGroup.mk'_surjective _) E.quotientAction_mk).mp hff

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
