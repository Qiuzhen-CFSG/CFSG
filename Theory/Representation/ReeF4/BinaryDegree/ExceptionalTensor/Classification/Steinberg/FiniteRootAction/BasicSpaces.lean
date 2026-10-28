module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.BasicFactors
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceHighestWeight
import all Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity

/-!
# Uniform source geometry of every basic factor

Actual highest-weight uniqueness removes the former uniqueness input from
short-root cyclicity and the primitive-line theorem. The trivial weight is
handled as the one-dimensional rational trivial factor, so these statements
include all four basic factors. Their actual coroot weight spaces span, and
positive short-root words are uniformly nilpotent.

Universality of the literal F4 carrier remains the independent geometric
input. These are the factor inputs for finite tensor restriction, not a
finite irreducibility or exhaustion assertion.
Source: Steinberg, Representations of Algebraic Groups (1963), 11.1 and 12.2.
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.BasicSpaces
open AlgebraicTensor
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

theorem finrank_one_of_zero {B : AlgebraicFactor F}
    (hB : Classification.HasBasicHighestWeight B (0,0)) :
    Module.finrank F B.Space = 1 := by
  obtain ⟨e, _⟩ := SourceHighestWeight.equivalent_of_same_basicHighestWeight B trivialFactor (0,0)
    hB trivialFactor_highestWeight
  exact e.finrank_eq.trans (Module.finrank_self F)

theorem shortNegativeSpan_eq_top (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) : p.shortNegativeSpan v = ⊤ := by
  by_cases hb : b = (0,0)
  · subst b
    let : IsSimpleOrder (Submodule F B.Space) :=
      is_simple_module_of_finrank_eq_one (finrank_one_of_zero ⟨v,hv⟩)
    rcases eq_bot_or_eq_top (p.shortNegativeSpan v) with h | h
    · have hm : v ∈ p.shortNegativeSpan v := by
        apply Submodule.subset_span
        exact ⟨[], rfl⟩
      exact (hv.1 (by simpa [h] using hm)).elim
    · exact h
  · exact p.shortNegativeSpan_eq_top_of_basic_highestWeight hU
      SourceHighestWeight.equivalent_of_same_highestWeight hb hv

theorem shortPositiveKernel_eq_span (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) :
    p.shortPositiveKernel = Submodule.span F {v} := by
  by_cases hb : b = (0,0)
  · subst b
    let : IsSimpleOrder (Submodule F B.Space) :=
      is_simple_module_of_finrank_eq_one (finrank_one_of_zero ⟨v,hv⟩)
    have ht : Submodule.span F {v} = ⊤ :=
      (eq_bot_or_eq_top (Submodule.span F {v})).resolve_left
        (by simpa only [Submodule.span_singleton_eq_bot] using hv.1)
    rw [ht]
    apply top_unique
    rw [← ht]
    exact (Submodule.span_singleton_le_iff_mem v _).mpr (p.highest_mem_shortPositiveKernel hv)
  · exact p.shortPositiveKernel_eq_span_of_negative_span
      SourceHighestWeight.equivalent_of_same_highestWeight hb hv (shortNegativeSpan_eq_top hU p hv)

/-- The actual integral coroot weight spaces span every basic factor. -/
theorem corootWeightSpace_iSup_eq_top
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) :
    (⨆ μ : EndNode.Weight, EndNode.corootWeightSpace B μ) = ⊤ :=
  p.corootWeightSpace_iSup_eq_top_of_negative_span hv (shortNegativeSpan_eq_top hU p hv)

/-- The positive short-root operators uniformly annihilate sufficiently long words. -/
theorem hasNilpotentShortPositiveAction
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) : p.HasNilpotentShortPositiveAction :=
  p.hasNilpotentShortPositiveAction_of_negative_span hv (shortNegativeSpan_eq_top hU p hv)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.BasicSpaces
