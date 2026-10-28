module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.DualFF
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.InsideAllCores
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.InsideCore
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.MinimalActorEqualities

/-!
# Original local ratio-two chief-factor equalities

The strict outside-core bound puts V(M) in every relevant local two-core.
The normalizer action embeds in the full M-action, so its cubic lower
bound and the proved inside-core quadratic upper bound give exact ratio two.
Its solvable dual-FF alternative would be FF by B.1.8, contradicting that
ratio. These derived inputs supply one minimal quadratic actor and the
literal two-chief-factor and fixed-codimension identities on its conjugate span.

This is the full-module branch. The proper four-space chosen in case (6)
is treated with its own seed and normalizer; no identification with V(M)
is made here. Source: Aschbacher--Smith 15.1.11--12(1--2), pp.1089--1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.GroupTheory Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The ratio-two input supplies the actual three prerequisites of the
chosen-module SQTK equality theorem. -/
theorem source_ratio_two_equality_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    2 ≤ cubicRatio (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) →
    let d := source_15_1_1_qrcConfiguration hG T hM hH
    localModule T M ≤ twoCoreIn H ∧ ¬ DualFF d ∧
      quadraticRatio (imageRepresentation (sourceNormalizer T M) (localModule T M)
        d.module_normalized) = 2 := by
  let d := source_15_1_1_qrcConfiguration hG T hM hH
  let := d.module_elementary
  intro hq
  have hV := (source_inside_all_cores_of_two_le_cubicRatio hG T hM hJ hq H hH).1
  let V := localModule T M
  let N := sourceNormalizer T M
  let ρ := imageRepresentation N V d.module_normalized
  let σ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  have hi : internalActionImage N V d.module_normalized ≤
      internalActionImage M V (le_normalizer_conjugateSpanBy _ _) := by
    rintro a ⟨n,rfl⟩
    exact ⟨⟨n,n.property.1⟩,rfl⟩
  have hlo : 2 ≤ quadraticRatio ρ := hq.trans
    ((cubicRatio_le_of_injective_equivariant ρ σ (inclusion hi)
      (inclusion_injective hi) (LinearEquiv.refl (ZMod 2) (Additive V))
      (fun _ _ => rfl)).trans (cubicRatio_le_quadraticRatio ρ))
  have heq : quadraticRatio ρ = 2 := le_antisymm
    (source_insideCore_quadraticRatio_le_two hG T hempty hM hH hJ hV) hlo
  refine ⟨hV,?_,heq⟩
  intro hd
  have hoff := ChapterB.SolvableDualFF.isFFModule_of_dual ρ
    (sourceNormalizer_actionImage_isSolvable hG T hempty hM _)
    (sourceNormalizer_actionImage_reduced hG T hM.1)
    (imageRepresentation_injective _ _ _) hd
  have hh := (isFFModule_iff_quadraticRatio_le_one ρ).mp hoff
  rw [heq] at hh
  norm_num at hh

/-- Original15.1.12(1--2) in the full-module ratio-two branch, with
core containment, nondual-FF and the normalizer ratio all discharged. -/
theorem source_ratio_two_minimal_actor_equalities
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    2 ≤ cubicRatio (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) →
    let d := source_15_1_1_qrcConfiguration hG T hM hH
    let U := (conjugateSpan H (localModule T M)).subgroupOf H
    let S := T.subtype hH.1.1.2
    letI := d.module_elementary
    ∃ (hV : localModule T M ≤ twoCoreIn H)
      (hqN : quadraticRatio (imageRepresentation (sourceNormalizer T M)
        (localModule T M) d.module_normalized) = 2),
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
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro hq
  let inputs := source_ratio_two_equality_inputs hG T hempty hM hH hJ hq
  refine ⟨inputs.1, inputs.2.2, inputs.2.1, ?_⟩
  exact source_centralizing_minimal_actor_equalities hG T hM hH hJ
    inputs.1 inputs.2.1 inputs.2.2

end CFSG.Quasithin.Chapter15.Section01
