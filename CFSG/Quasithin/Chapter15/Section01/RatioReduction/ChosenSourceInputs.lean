module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ChosenRatio
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SelectedAction
/-!
# Source inputs for the chosen-module chief-factor equalities

The solvable residual of the selected local group centralizes its original
module and therefore every chosen invariant subgroup of that module. Its
actual action image is solvable. With the chosen-normalizer image equality
and reducedness, quadratic ratio two consequently excludes dual FF.

The final theorem applies the genuine SQTK equality theorem to the same
chosen subgroup. It yields one minimal maximum elementary actor and all
chief-factor and conjugate-generator equalities. Its remaining inputs are
core containment and the quadratic ratio, supplied by the source
15.1.8 and 15.1.11 branches, including the literal proper moved support.

Source: Aschbacher--Smith 14.1.6, 15.1.9(6), 15.1.12(1--2),
and 3.1.9(1--3), printed pp.1066,1088--1090 and576--577.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
theorem source_chosen_action_isSolvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    ∀ (V : Subgroup G) (hMV : M ≤ normalizer (V : Set G)), V ≤ localModule T M →
      Group.IsSolvable (internalActionImage M V hMV) := by
  intro V hMV hVL
  let f := actionHom M V hMV
  have hr := residual_le_centralizer_localModule
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hG T hempty ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hk : solvableResidual M ≤ f.ker := by
    rw [show f.ker = (centralizer (_ : Set G)).subgroupOf M from actionHom_ker M _ _]
    exact fun _ hx => (centralizer_le hVL) (hr (mem_map_of_mem _ hx))
  have hz : solvableResidual f.range = ⊥ := by
    rw [←map_solvableResidual_eq f.rangeRestrict f.rangeRestrict_surjective]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [MonoidHom.ker_rangeRestrict] using hk)
  obtain ⟨n,hn⟩ := exists_derivedSeries_eq_solvableResidual (G := f.range)
  exact ⟨n,hn.trans hz⟩

theorem source_chosen_noncentral_count_two_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M)
    (hVL : V ≤ localModule T M) (hV : V ≤ twoCoreIn H)
    (hq : quadraticRatio (imageRepresentation M V hMV) = 2)
    (s : NoncentralChiefRefinement.SeriesOn ((conjugateSpan H V).subgroupOf H)) :
    s.noncentralCount = 2 := by
  exact source_chosen_noncentral_count_two hG T hempty hM hH hJ hVM hVne hMV hspan
    hVL hV (source_chosen_action_isSolvable hG T hempty hM V hMV hVL) hq s

theorem source_chosen_equality_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M)
    (hVL : V ≤ localModule T M)
    (hq : quadraticRatio (imageRepresentation M V hMV) = 2) :
    let d := source_chosenNormalizer_qrcConfiguration hG T hempty hM hJ hVM hVne hMV hspan hH
    quadraticRatio (imageRepresentation (chosenNormalizer T M V) V d.module_normalized) = 2 ∧
      ¬ DualFF d := by
  let h := chosenNormalizer_qrcHypotheses T hM.1.2 hVM hMV hspan hH
  have hu := source_chosenNormalizer_unique hG T hempty hM hJ hVne hMV hspan
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let ρ := imageRepresentation (chosenNormalizer T M V) V d.module_normalized
  have hqN : quadraticRatio ρ = 2 := (chosenNormalizer_quadraticRatio_eq T hM.1.2 hMV).trans hq
  have hsolN : Group.IsSolvable (internalActionImage (chosenNormalizer T M V) V
      d.module_normalized) := by
    rw [show internalActionImage (chosenNormalizer T M V) V d.module_normalized =
      internalActionImage M V hMV from chosenNormalizer_actionImage_eq T hM.1.2 hMV]
    exact source_chosen_action_isSolvable hG T hempty hM V hMV hVL
  refine ⟨hqN,?_⟩
  intro hdual
  have hff := ChapterB.SolvableDualFF.isFFModule_of_dual ρ hsolN
    (chosenNormalizer_actionImage_reduced T hM.1.2 hVM hMV hspan)
    (imageRepresentation_injective _ _ _) hdual
  have hh := (isFFModule_iff_quadraticRatio_le_one ρ).mp hff
  rw [hqN] at hh
  norm_num at hh

theorem source_chosen_minimal_actor_equalities
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M)
    (hVL : V ≤ localModule T M) (hV : V ≤ twoCoreIn H)
    (hq : quadraticRatio (imageRepresentation M V hMV) = 2) :
    let d := source_chosenNormalizer_qrcConfiguration hG T hempty hM hJ hVM hVne hMV hspan hH
    let U := (conjugateSpan H V).subgroupOf H
    let S := T.subtype hH.1.1.2
    letI := d.module_elementary
    ∃ (hqN : quadraticRatio (imageRepresentation (chosenNormalizer T M V)
        V d.module_normalized) = 2),
    ¬ DualFF d ∧
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hqN)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H), ¬ A ≤ pCore 2 H ∧
      IsQuadratic (normalRepresentation U) A ∧
      (∀ B ∈ elementaryAbelianMaxSubgroups (S : Subgroup H),
        ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) ∧
      ∀ s : SeriesOn U,
        s.noncentralCount = 2 ∧
        2 * Nat.log 2 ((pCore 2 H).relIndex A) = fixedCodim (normalRepresentation U) A ∧
        fixedCodim (normalRepresentation U) A =
          2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (A ⊓ pCore 2 H)) ∧
        U ⊓ centralizer (A : Set H) = U ⊓ centralizer (A ⊓ pCore 2 H : Set H) ∧
        (∀ i, ¬ s.Central i →
          Nat.log 2 ((pCore 2 H).relIndex A) = fixedCodim (s.factorRepresentation i) A) ∧
        ∀ g : H,
          (fixedCodim (conjugateGenerator d (A ⊓ pCore 2 H) inf_le_right g).toRepresentation ⊤ : ℝ) =
            2 * (Nat.log 2 (subspaceKernel ((normalRepresentation U).comp (A ⊓ pCore 2 H).subtype)
              (conjugateGenerator d (A ⊓ pCore 2 H) inf_le_right g).toSubmodule ⊤).index : ℝ) := by
  obtain ⟨hqN,hdual⟩ := source_chosen_equality_inputs hG T hempty hM hH hJ
    hVM hVne hMV hspan hVL hq
  refine ⟨hqN,hdual,?_⟩
  let h := chosenNormalizer_qrcHypotheses T hM.1.2 hVM hMV hspan hH
  have hu := source_chosenNormalizer_unique hG T hempty hM hJ hVne hMV hspan
  exact h.sqtk_minimal_actor_equalities hG hM.1.1 hu
    (hJ.trans (centralizer_le hVL)) hVne hV hdual hqN

end CFSG.Quasithin.Chapter15.Section01
