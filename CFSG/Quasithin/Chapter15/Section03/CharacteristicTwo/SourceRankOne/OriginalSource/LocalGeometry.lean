module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Components
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Line

/-!
# Original rank-one plane geometry and characteristic exclusion

The actual15.3.7 action image supplies both plane commutators and the
central-seed span. Under the S₃ shadow,15.3.26 selects the second source
choice. Apply15.3.11(12) directly to I: its residual is Y₊ and its action
on V is the nontrivial second plane. This proves15.3.29 without a further
component classification or a minimality hypothesis.

Source: Aschbacher–Smith15.3.11(3),(12),15.3.29, pp.1123–1124,1131.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06
open RankOneConfiguration.EightGeometry.NaturalModule.Recognition
variable {G : Type*} [Group G] [Finite G]

/-- The original orthogonal source supplies the full selected plane action. -/
theorem source_lineData
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.Hplus) : LineData d I := by
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have h7 := source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have hspan := source_residual_seed_span hG d.T hempty d.action hM hu hmany hne
  have h := source_lemma_15_3_26_1 hG d hempty hM hu hmany hshadow hI
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have hcomm := OutsideStructure.LocalBranches.second_choice_commutator d h.choice h7.1
  refine ⟨h11.theta_eq.symm,h11.normalizer_eq,hcomm.1,hcomm.2,?_⟩
  exact (OutsideStructure.LocalBranches.second_choice_plane_le_span d h.choice h7.1 hspan).trans
    (conjugateSpanBy_mono le_rfl (le_sup_left.trans hI.1.2))

/-- Original15.3.29: no nontrivial characteristic subgroup of S is normal
in I, and the first plane is centralized by Y₊ with its normalizer in M. -/
theorem source_lemma_15_3_29
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.Hplus) :
    (∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf I).Normal) ∧
      normalizer (d.V₁ : Set G) ≤ d.M ∧
      d.V₁ ≤ centralizer (d.Yplus : Set G) := by
  have h := source_lemma_15_3_26_1 hG d hempty hM hu hmany hshadow hI
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have hline := source_lineData hG d hempty hM hu hmany hshadow hI
  have hsecond := h11.second_choice h.choice
  have hact : ⁅d.V,d.Yplus⁆ ≠ ⊥ := by
    rw [hline.plane_eq]
    exact OutsideStructure.LocalBranches.plane_ne_bot d _
  refine ⟨?_,hsecond.2.1,?_⟩
  · intro C hchar hne
    have hc := h11.characteristic_exclusion I le_rfl (hsecond.1 ▸ hact) hI.2 C hchar hne
    have hSI : d.S ≤ I := le_sup_right.trans (show d.Yplus ⊔ d.S ≤ I from hI.1.2)
    have he : I ⊔ d.S = I := sup_eq_left.mpr hSI
    rwa [he] at hc
  · apply le_centralizer_iff.mpr
    rw [h.choice.2]
    exact (map_subtype_le _).trans inf_le_right

/-- The original Sylow-fixed plane is precisely the central omega subgroup. -/
theorem source_central_omega (d : LocalData G) :
    d.ZS = centralOmegaIn d.S ∧ Nat.card d.ZS = 4 :=
  ⟨(source_lemma_15_3_8 d.T d.action d.sylow_le 1).1,
    d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1⟩

/-- The full residual Y has cubic rank at least two, as witnessed by its
actual elementary-nine action image. -/
theorem source_y_three_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard) :
    2 ≤ primeRank 3 d.Y := by
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have h7 := source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  obtain ⟨e⟩ := orthogonalActor_residual_equiv_elementaryNine
  let B := Multiplicative (Fin 2 → ZMod 3)
  have hc : Nat.card B = 3 ^ 2 := by simp [B,Nat.card_eq_fintype_card]
  have hp : ∀ x : B, x ^ 3 = 1 := by decide +kernel
  have hr : primeRank 3 B = 2 := by
    apply le_antisymm
    · apply (primeRank_le_iff_elementary_card_le B).mpr
      intro E _
      exact E.card_le_card_group.trans hc.le
    · exact primeRank_ge_of_elementary_embedding hp hc (MonoidHom.id _) Function.injective_id
  let f := (MulEquiv.subgroupCongr h7.1).trans e
  let q := f.toMonoidHom.comp (d.action.actor.subgroupMap (d.Y.subgroupOf d.M))
  have hq : Function.Surjective q :=
    f.surjective.comp (d.action.actor.subgroupMap_surjective _)
  have hbound := PrimeRank.le_of_surjective_of_target_le_two (by decide : 3 ≠ 2) q hq hr.le
  rw [hr] at hbound
  let j : d.Y.subgroupOf d.M →* d.Y := {
    toFun x := ⟨x,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  exact hbound.trans (_root_.primeRank_le_of_injective 3 j (by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : d.Y => (x : G)) hab))))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
