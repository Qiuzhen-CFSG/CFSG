module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Inputs
public import CFSG.Quasithin.Chapter14.Section06.SourceClassificationComplete
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.GeneratedMSInputs

/-!
# The unchanged generated choice for the seven-letter module branches

Escape follows from the completed original factorization and local Sylow
placement follows from U3. The generated I₀ retains the original IStar
intersection and preferred-centralizer condition. Its actual first core
has the C.2.7 and MS inputs, and the entire generated plane span lies in
the literal block commutator module.

Source: Aschbacher--Smith, original14.6.10(5), pp.1029--1030.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.Seven
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))


variable (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))

include hG hempty hM hunique hmany hcard e hab H hH d hI

/-- The original preferred choice transfers to the literal generated group. -/
theorem generated_choice
    (hpreferred : (T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({d.u} : Set G) →
      I ≤ centralizer ({d.u} : Set G)) :
    let I0 := sourceGeneratedParabolic T M Mc I d.H2
    I0 ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) ∧
    (T : Subgroup G) ⊓ I0 = (T : Subgroup G) ⊓ I ∧
    ¬ I0 ⊓ M ≤ Mc ∧
    sourceSecondParabolic T I d.H2 ≤ H ∧
    ((T : Subgroup G) ⊓ I0 = (T : Subgroup G) ⊓ centralizer ({d.u} : Set G) →
      I0 ≤ centralizer ({d.u} : Set G)) := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨hI0,hS,_,hI2H2,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal
    ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
    ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput
    I d.H2 hI hout d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  have hH2H : d.H2 ≤ H := fun x hx =>
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H d.mem_span))).mp
      (d.le_quotient_centralizer hx)).1
  refine ⟨hI0,hS,source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d _ hI0,hI2H2.trans hH2H,?_⟩
  intro hs
  have hsI : (T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({d.u} : Set G) :=
    hS.symm.trans hs
  have hIu := hpreferred hsI
  have hRu : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ centralizer ({d.u} : Set G) :=
    ((map_subtype_le _).trans inf_le_right).trans hIu
  have hSu : (T : Subgroup G) ⊓ I ≤ centralizer ({d.u} : Set G) := hsI ▸ inf_le_right
  exact sup_le (sup_le hRu hSu)
    (sup_le (RankFiveNaturalSixPlacement.residual_kernel_centralizes h d.u d.mem_span
      d.H2 d.le_quotient_centralizer) hSu)

/-- Full-span containment, with escape and local Sylow placement discharged. -/
theorem generated_span_le_module :
    conjugateSpanBy (localModule T M) (sourceGeneratedParabolic T M Mc I d.H2) ≤
      (ChapterC.blockU (sourceGeneratedComponent T M Mc I d.H2)).map
        (sourceGeneratedComponent T M Mc I d.H2).subtype := by
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨K,_,_,_,_,hK,_,_,hmodule,_⟩ := source_generated_parabolic_module_data
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  subst K
  exact hmodule.2

/-- The original C.2.7 and MS inputs on the recomputed first core.
This supplies the source hypotheses for seven-letter reconstruction. -/
theorem generated_ms_inputs :
    let I0 := sourceGeneratedParabolic T M Mc I d.H2
    let I1 := firstResidual T M Mc I d.H2 ⊔ ((T : Subgroup G) ⊓ I0)
    Input KnownSimple.IsKnownSimple I0 (I1.pCoreIn 2) (I0 ⊓ M)
      (sourceGeneratedComponent T M Mc I d.H2) ∧
    ChapterC.MSOddIndexRadical ((I1.pCoreIn 2).subgroupOf I0) ∧
    ChapterC.MSCharacteristicCondition ((I1.pCoreIn 2).subgroupOf I0) := by
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  exact source_generated_parabolic_ms_inputs
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI
    (source_second_parabolic_intersection_escape hG T hempty hM hunique hmany hcard e hab H hH d I hI)
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank

end CFSG.Quasithin.Chapter14.Section06.Seven
