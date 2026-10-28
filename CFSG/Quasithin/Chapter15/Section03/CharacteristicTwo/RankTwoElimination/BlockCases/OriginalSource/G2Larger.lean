module
public import Theory.GroupTheory.CComponent.CenterlessRankNormal
public import Theory.AtlasPort.LinearGroups.G2.SolvableInvariantParabolics
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals
public import Theory.SpecificGroups.G2.MultiplierTwoGroup
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.GroupTheory.EquivariantParabolicLift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.LinearThreeLarger.Sylow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.ParabolicDescent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry

/-!
# Larger G₂ star models in the original rank-two source configuration

The two-primary multiplier and the trivial two-core identify the literal
star model with the component quotient, including over the field of four
elements. Cubic rank forces component normality. The solvable local actor
then preserves both root parabolics through its characteristic Sylow.
Their full preimages are proper and generate the component, giving proper
outside overgroups and contradicting the original induction hypothesis.

This specializes the invariant-parabolic argument of Aschbacher–Smith
15.3.20, printed pp.1127–1128, directly to the higher-field G₂ row of B.5.
It needs no reconstruction of the C.1.32 natural block. The covering facts
are I.1.3–I.1.4, printed pp.407–408.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

noncomputable def g2_core_equiv_of_star
    {I L R M : Subgroup G} (h : Input KnownSimple.IsKnownSimple I R M L)
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : starImage L R L ≃* Model F) : (L ⧸ pCore 2 L) ≃* Model F := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  let : Group.IsPerfect (Model F) := isPerfect hq
  have hne : starImage L R L ≠ ⊥ := by
    intro hh
    have hlt := (ChapterC.C27Source.star_thompson_intersection_from_source h).2
    rw [hh] at hlt
    exact not_lt_bot hlt
  let f := coreStarCover h.normalizes h.quasisimple hne
  let g : PerfectCentralCovering.Cover (L ⧸ pCore 2 L) (Model F) :=
    { toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
      surjective := e.surjective.comp f.surjective
      isPerfect := f.isPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact f.ker_le_center }
  exact g.equivOfPCoreEqBotOfUniversalPGroup
    (PerfectCentralCovering.universalCover (Model F))
    (PerfectCentralCovering.universalCover_isUniversal (G := Model F))
    (FiniteCover.universalKernel_isPGroup_of_card_pow hF hn)
    (pCore_quotient_pCore_eq_bot 2)

/-- The two root parabolics lifted to the actual component. -/
theorem g2_original_parabolic_pair
    (L A : Subgroup G) (hn : A ≤ normalizer (L : Set G))
    (hsol : Group.IsSolvable A) (T : Sylow 2 L)
    (hTA : (T : Subgroup L) ≤ A.subgroupOf L)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (L ⧸ pCore 2 L) ≃* Model F) :
    ∃ P Q : Subgroup G, P < L ∧ Q < L ∧ P ⊔ Q = L ∧
      A ≤ normalizer (P : Set G) ∧ A ≤ normalizer (Q : Set G) ∧ A ⊓ L ≤ P ⊓ Q := by
  let q₀ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let U₀ := T.mapSurjective hq₀
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) U₀ (sylow (F := F))
  let e' := e.trans (MulAut.conj g)
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hT : (T : Subgroup L).map q = unipotent := by
    have hh := congrArg (fun V : Sylow 2 (Model F) => (V : Subgroup (Model F))) hg
    change ((T : Subgroup L).map q₀).map (MulAut.conj g).toMonoidHom = unipotent at hh
    rw [map_map] at hh
    exact hh
  let α : A →* MulAut (Model F) := (MulAut.congr e').toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hn)))
  have heq (a : A) (l : L) :
      q (L.normalizerMonoidHom (inclusion hn a) l) = α a (q l) := by
    change e' (QuotientGroup.mk' _ _) = e' (quotientAut _ _ (e'.symm (e' _)))
    rw [e'.symm_apply_apply,quotientAut_apply_mk]
    rfl
  let B := (A.subgroupOf L).map q
  let : Group.IsSolvable A := hsol
  let i : (A.subgroupOf L) →* A :=
    {toFun := fun a => ⟨a.val.val,a.property⟩,map_one' := rfl,map_mul' := fun _ _ => rfl}
  let : Group.IsSolvable (A.subgroupOf L) := Group.isSolvable_of_isSolvable_injective
    (f := i) (by
      intro a b hab
      have hv : (a.val.val : G) = b.val.val := congrArg (fun z : A => (z : G)) hab
      exact Subtype.ext (Subtype.ext hv))
  have hBsol : Group.IsSolvable B := Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  have hUB : unipotent ≤ B := hT ▸ map_mono hTA
  have hBb : B ≤ parabolic₁ ⊓ parabolic₂ := by
    rw [SylowNormalizer.parabolics_intersection]
    exact SolvableSylowPlacement.le_borel hF B hUB hBsol
  have hBinv (a : A) : B.map (α a).toMonoidHom = B :=
    EquivariantLift.map_invariant L q hn α heq A.le_normalizer a
  have hpair (a : A) : parabolic₁.map (α a).toMonoidHom = parabolic₁ ∧
      parabolic₂.map (α a).toMonoidHom = parabolic₂ :=
    SolvableSylowPlacement.parabolic_pair_map_of_solvable_overgroup hF B hBsol hUB (α a) (hBinv a)
  refine ⟨EquivariantLift.lift L q parabolic₁,EquivariantLift.lift L q parabolic₂,
    EquivariantLift.lift_lt L q hq HigherFieldResiduals.parabolic₁_isCoatom.ne_top,
    EquivariantLift.lift_lt L q hq HigherFieldResiduals.parabolic₂_isCoatom.ne_top,?_,
    EquivariantLift.normalizes_lift L q hn α heq (fun a => (hpair a).1),
    EquivariantLift.normalizes_lift L q hn α heq (fun a => (hpair a).2),?_⟩
  · rw [←EquivariantLift.lift_sup L q hq,parabolics_generate,EquivariantLift.lift_top]
  · apply le_inf
    · apply EquivariantLift.le_lift L q inf_le_right
      simpa only [inf_subgroupOf_right] using hBb.trans inf_le_left
    · apply EquivariantLift.le_lift L q inf_le_right
      simpa only [inf_subgroupOf_right] using hBb.trans inf_le_right

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)

include hG hempty hM hu hmany hI htwo hf hproper

theorem source_15_3_20_g2_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Model F) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  let K := c.L.subgroupOf I
  let a : K ≃* c.L := subgroupOfEquivOfLe (component_le c)
  let b : (K ⧸ pCore 2 K) ≃* Model F :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  have hK : K.IsCComponent := LocalData.thompson_component_in c.le_thompson c.component
  let : IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
  let : Group.IsPerfect (Model F) := isPerfect hF
  let : IsSimpleGroup (Model F) := isSimple hF
  have hzModel : center (Model F) = ⊥ := by
    rcases (inferInstance : (center (Model F)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (Group.IsPerfect.not_isMulCommutative (Model F)
        (center_eq_top_iff.mp h))
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact b.map_eq_one_iff.mp (hzModel.le ((centerCongr b) ⟨x,hx⟩).property)
  have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 3 b]
    exact EvenThreeRank.two_le_primeRank
  have hnormal : K.Normal := hK.normal_of_centerless_core_threeRank hz hr
    ((OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 Nat.prime_three (by decide))
  have hn : d.Yplus ⊔ d.S ≤ normalizer (c.L : Set G) :=
    hI.1.2.trans ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnormal)
  obtain ⟨S,hS⟩ := h11.sylow
  obtain ⟨T,hT⟩ := LinearThree.Extension.SourceCases.component_sylow d c S hS
  have hTA : (T : Subgroup c.L) ≤ (d.Yplus ⊔ d.S).subgroupOf c.L := by
    rw [hT]
    exact comap_mono le_sup_right
  obtain ⟨P,Q,hP,hQ,hgen,hnP,hnQ,hbase⟩ := g2_original_parabolic_pair c.L (d.Yplus ⊔ d.S)
    hn (LinearThreeLarger.local_solvable d htwo) T hTA hF e
  exact source_15_3_20_of_generating_parabolics d hI ⟨S,hS⟩ hf c hproper
    P Q hP hQ hgen hnP hnQ hbase

theorem source_15_3_20_g2_star
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : starImage c.L d.R c.L ≃* Model F) : False := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  exact source_15_3_20_g2_quotient hG d hempty hM hu hmany hI htwo hf c hproper hq
    (g2_core_equiv_of_star h hF hn e)
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
