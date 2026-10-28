module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates.Preparation
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Preparing the genuine offender-generated component for B.5.1

Under (i), the conjugate span of Vα is perfect. After (k)–(l), H = LT and
H/L is a two-group, so this span equals L. Thus Vα* lies in L*, and the
faithful action of L* itself is offender-generated. The marked S₈ extension
identifies L* with the actual A₈, supplying quasisimplicity.

These arguments discharge the group hypotheses of B.5.1 on L*, rather than
incorrectly applying that theorem to all of H* = S₈. The full enumerated
classification implication remains an explicit earlier source input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed p.99, and proof of 15.3.49(i)–(l), printed pp.1143–1145.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight

open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open ComponentReduction ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {H M Y V Y₀ L ZS Z A : Subgroup G} {T : Sylow 2 G}
  [IsElementaryAbelian 2 (localSpan ZS H)]
  (d : BorelInner.SourceSetup κ H M Y V Y₀ L ZS Z A T)
  (r : ReducedLocalData H M L Y₀ T)

omit [Finite G] in
include r in
/-- The reduced component is already closed under the Sylow conjugates. -/
theorem component_closure_eq : localSpan L T = L := by
  apply le_antisymm _ (le_conjugateSpanBy L T)
  apply conjugateSpanBy_le le_rfl
  exact (r.factorization_LT ▸ le_sup_right).trans r.normalizes_component

include d r in
/-- The perfect source span has trivial image in the two-group H/L. -/
theorem offender_span_eq_component : localSpan A H = L := by
  have hc := component_closure_eq r
  exact (LargerFields.NaturalCoordinates.span_eq_closure d
    (r.cubic_in_component.trans (le_conjugateSpanBy L T))).trans hc

include d r in
/-- Containment of the chosen offender follows from generation; it is not
added as an extra model hypothesis. -/
theorem offender_le_component : A ≤ L :=
  (le_conjugateSpanBy A H).trans_eq (offender_span_eq_component d r)

include d r in
theorem star_offender_le_component : starImage H A ≤ starImage H L :=
  map_mono (comap_mono (offender_le_component d r))

/-- The extension marking restricts to an actual A₈ equivalence. -/
noncomputable def component_alternating
    (m : BinaryGeometry.MiddleNodeEight (starImage H L) (componentParabolic H L Y₀ T)) :
    starImage H L ≃* alternatingGroup (Fin 8) :=
  (m.extension.subgroupMap (starImage H L)).trans (MulEquiv.subgroupCongr m.component_image)

private theorem alternatingEight_quasisimple : IsQuasisimple (alternatingGroup (Fin 8)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

omit [Finite G] in
theorem component_quasisimple
    (m : BinaryGeometry.MiddleNodeEight (starImage H L) (componentParabolic H L Y₀ T)) :
    IsQuasisimple (starImage H L) := by
  let := alternatingEight_quasisimple
  exact IsQuasisimple.of_mulEquiv (component_alternating m).symm

include r in
/-- Every B.5.1 group hypothesis holds for the actual component action. -/
theorem component_sourceHypothesis
    (m : BinaryGeometry.MiddleNodeEight (starImage H L) (componentParabolic H L Y₀ T)) :
    QuasisimpleSourceHypothesis
      (d.action.representation.comp (starImage H L).subtype) κ ⊤ := by
  have hc := component_closure_eq r
  have hy := r.cubic_in_component.trans (le_conjugateSpanBy L T)
  obtain ⟨hf, hp, hg, _⟩ := LargerFields.NaturalCoordinates.component_actor_hypotheses d hy
  have hs := LargerFields.NaturalCoordinates.component_actor_sqtk d hy
  rw [hc] at hf hp hg hs
  let := component_quasisimple m
  refine ⟨Module.Finite.of_finite, hf, ?_, hs.subgroup ⊤, ?_, hp, hg⟩
  · exact IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm
  · rw [LargerFields.NaturalCoordinates.generalizedFitting_eq_top_of_quasisimple]
    simp

include r in
/-- Retain the whole enumerated conclusion: no natural-plus-dual alternative
has been selected merely by applying B.5.1. -/
theorem component_sourceConclusion
    (m : BinaryGeometry.MiddleNodeEight (starImage H L) (componentParabolic H L Y₀ T))
    (hB51 : QuasisimpleClassificationInput.{u,u} κ) :
    Nonempty (QuasisimpleSourceConclusion
      (d.action.representation.comp (starImage H L).subtype) ⊤) :=
  hB51 _ _ _ _ (component_sourceHypothesis d r m)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight
