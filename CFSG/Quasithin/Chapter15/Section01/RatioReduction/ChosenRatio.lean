module
public import CFSG.Quasithin.Chapter15.Section01.ChosenNormalizerSource
public import CFSG.Quasithin.Chapter3.Section01.SourceSQTKEquality
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.DualFF
/-!
# The same quadratic ratio on the actual chosen normalizer

Frattini representatives identify the two literal conjugation images on
chosen V. The inclusion maps in both directions preserve their quadratic
ratios. Thus ratio two gives an elementary H-conjugate span once V lies in
the H-core. In the solvable image case B.1.8 also excludes dual FF, supplying
the two-chief-factor theorem for the chosen module of15.1.4.

The inside-core and model ratio inputs remain with their source15.1.8/11
producers. The construction retains chosen V throughout, including the
proper moved four-space. Source: Aschbacher--Smith15.1.9(6),15.1.11(2), and
15.1.12(1), printed pp.1088--1090.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
theorem chosenNormalizer_quadraticRatio_eq (T : Sylow 2 G) {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hTM : (T : Subgroup G) ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    quadraticRatio (imageRepresentation (chosenNormalizer T M V) V (inf_le_left.trans hMV)) =
      quadraticRatio (imageRepresentation M V hMV) := by
  let ρ := imageRepresentation (chosenNormalizer T M V) V (inf_le_left.trans hMV)
  let σ := imageRepresentation M V hMV
  have he := chosenNormalizer_actionImage_eq T hTM hMV
  apply le_antisymm
  · exact quadraticRatio_le_of_injective_equivariant σ ρ (inclusion he.ge)
      (inclusion_injective he.ge) (LinearEquiv.refl (ZMod 2) (Additive V)) (fun _ _ => rfl)
  · exact quadraticRatio_le_of_injective_equivariant ρ σ (inclusion he.le)
      (inclusion_injective he.le) (LinearEquiv.refl (ZMod 2) (Additive V)) (fun _ _ => rfl)

theorem source_chosen_elementary_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M)
    (hV : V ≤ twoCoreIn H)
    (hq : quadraticRatio (imageRepresentation M V hMV) = 2) :
    IsElementaryAbelian 2 (conjugateSpan H V) := by
  let d := source_chosenNormalizer_qrcConfiguration hG T hempty hM hJ hVM hVne hMV hspan hH
  have hqN : quadraticRatio (imageRepresentation (chosenNormalizer T M V) V
      d.module_normalized) = 2 := (chosenNormalizer_quadraticRatio_eq T hM.1.2 hMV).trans hq
  exact source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hqN)
theorem source_chosen_noncentral_count_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M)
    (hVL : V ≤ localModule T M) (hV : V ≤ twoCoreIn H)
    (hsol : Group.IsSolvable (internalActionImage M V hMV))
    (hq : quadraticRatio (imageRepresentation M V hMV) = 2)
    (s : NoncentralChiefRefinement.SeriesOn ((conjugateSpan H V).subgroupOf H)) :
    s.noncentralCount = 2 := by
  let h := chosenNormalizer_qrcHypotheses T hM.1.2 hVM hMV hspan hH
  have hu := source_chosenNormalizer_unique hG T hempty hM hJ hVne hMV hspan
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let ρ := imageRepresentation (chosenNormalizer T M V) V d.module_normalized
  have hqN : quadraticRatio ρ = 2 := (chosenNormalizer_quadraticRatio_eq T hM.1.2 hMV).trans hq
  have hsolN : Group.IsSolvable (internalActionImage (chosenNormalizer T M V) V
      d.module_normalized) := by
    rw [show internalActionImage (chosenNormalizer T M V) V d.module_normalized =
      internalActionImage M V hMV from chosenNormalizer_actionImage_eq T hM.1.2 hMV]
    exact hsol
  have hdual : ¬ DualFF d := by
    intro hdual
    have hff := ChapterB.SolvableDualFF.isFFModule_of_dual ρ hsolN
      (chosenNormalizer_actionImage_reduced T hM.1.2 hVM hMV hspan)
      (imageRepresentation_injective _ _ _) hdual
    have hh := (isFFModule_iff_quadraticRatio_le_one ρ).mp hff
    rw [hqN] at hh
    norm_num at hh
  exact h.sqtk_noncentral_count_two hG hM.1.1 hu
    (hJ.trans (centralizer_le hVL)) hVne hV hdual hqN s
end CFSG.Quasithin.Chapter15.Section01
