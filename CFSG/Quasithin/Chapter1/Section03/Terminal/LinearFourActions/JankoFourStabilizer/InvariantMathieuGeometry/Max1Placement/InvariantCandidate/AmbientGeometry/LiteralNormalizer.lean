module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralNormalizer.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer

/-!
# The literal max1 core normalizer

An ambient normalizer element with the same action on the core as an element
of max1 differs from it by an element of the ambient core centralizer. Thus
the action-realization and centralizer bounds together prove the required
normalizer containment. The Theory assembly discharges both concrete inputs
for the actual embedded local kernel. Transport through its equality with
the literal two-core proves `LiteralCoreNormalizerControl` unconditionally.

The conditional action-and-centralizer and vector-stabilizer routes remain
available. Source: GLS3 Table 5.3i and the literal matrix provenance
documented in `LiteralNormalizer.Reduction`.
-/

public section

open Subgroup Janko4 Janko4.Cardinality
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

/-- The alternative stabilizer route retains its unproved ambient premise. -/
theorem literalCoreNormalizerControl_of_vectorStabilizer
    (hst : cosetVectorStabilizer ≤ max1Subgroup matrixA_mul_self matrixB_pow_four) :
    LiteralCoreNormalizerControl :=
  literalCore_normalizer_le_vectorStabilizer.trans hst

/-- Realizing the action reduces normalizer membership to centralizer membership.
The two independent concrete premises must both be discharged. -/
theorem literalCoreNormalizerControl_of_action_and_centralizer
    (hact : LiteralCoreActionRealization) (hcent : LiteralCoreCentralizerControl) :
    LiteralCoreNormalizerControl := by
  intro g hg
  obtain ⟨h, hh, he⟩ := hact g hg
  have heq : Set.EqOn (MulAut.conj g).toMonoidHom (MulAut.conj h).toMonoidHom
      (certifiedMathieuSubgroup.pCoreIn 2 : Set Model) := by
    rw [← literalCoreGenerators_generate]
    apply MonoidHom.eqOn_closure
    rintro x ⟨i, rfl⟩
    exact he i
  have hc : h⁻¹ * g ∈ centralizer (certifiedMathieuSubgroup.pCoreIn 2 : Set Model) := by
    intro x hx
    have hxg : g * x * g⁻¹ = h * x * h⁻¹ := heq hx
    have hxh := congrArg (fun y : Model => h⁻¹ * y * g) hxg
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hxh.symm
  have hm := certifiedMathieuSubgroup.mul_mem hh (hcent hc)
  simpa only [mul_inv_cancel_left] using hm

/-- The ambient normalizer of the literal embedded two-core lies in max1. -/
theorem literalCoreNormalizerControl : LiteralCoreNormalizerControl := by
  change normalizer (certifiedMathieuSubgroup.pCoreIn 2 : Set Model) ≤
    certifiedMathieuSubgroup
  rw [literalCore_eq_embedded_localKernel]
  exact LocalStructure.normalizer_embedded_localKernel_le_max1

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry
