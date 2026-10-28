module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.KernelObstruction
public import Theory.Alternating.Theorem523Reduction
/-!
# The A₈ exclusion in the lifted-component comparison

The existing Schur presentation gives the universal double cover of A₈.
Every perfect central-cover kernel is a quotient of its two-element kernel,
so it has order prime to three. Applied to the actual component lift, whose
center has a three-part, this excludes the eight-point B.5.1 alternative.

This is an application of the proved universality theorem, not an assumption
of a multiplier order or an identification by group order.
Source: Aschbacher–Smith, I.1.3(1), printed p.407, and B.5.7, p.106;
GLS3 Theorem 5.2.3, as formalized in Theory.Alternating.Theorem523Reduction.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
universe u
/-- The constructed Schur double cover rules out three-primary perfect-cover kernels. -/
theorem alternatingEight_threeFreePerfectKernels :
    ThreeFreePerfectKernels.{u} (alternatingGroup (Fin 8)) := by
  intro E _ _ f
  let : IsQuasisimple (alternatingGroup (Fin 8)) :=
    GLS3.Chapter5.SchurPresentation.alternatingGroup_isQuasisimple 3
  let : IsQuasisimple E := f.isQuasisimple
  have hd := GLS3.Chapter5.Covering.coveringKernel_card_dvd_of_universal
    (GLS3.Chapter5.SchurPresentation.schurAlternatingCovering 3)
    (GLS3.Chapter5.SchurPresentation.theorem_5_2_3_b_universality 3 (by decide) (by decide))
    f.toCovering
  rw [GLS3.Chapter5.SchurPresentation.theorem_5_2_3_a] at hd
  intro h
  have he : 3 ∣ 2 := h.trans hd
  norm_num at he
/-- The original lifted component rules out A₈, with no model premise. -/
theorem not_alternatingEight_component
    {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
    {L : Subgroup G} (hL : IsComponent G L) (d : NoncentralContext K G L) :
    ¬ Nonempty (L ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨e⟩
  exact not_model_of_threeFreePerfectKernels hL d
    (alternatingGroup.center_eq_bot (by simp)) alternatingEight_threeFreePerfectKernels e

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
