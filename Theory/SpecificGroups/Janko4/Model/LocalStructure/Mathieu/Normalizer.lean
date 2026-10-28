module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer.ActionRealization
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer.CoreCentralizer

/-!
# The ambient normalizer of the literal max1 kernel

Let M be the literal ATLAS max1 subgroup and E the image of its order-2048
local kernel in the matrix model. Every ambient normalizer action on E is
realized by some h in M. Thus h⁻¹g centralizes E, and the ambient centralizer
bound puts it in M. It follows that the entire normalizer lies in M.

Both inputs are proved for these actual embedded subgroups. No assumption
about ambient simplicity, perfectness, or order enters the conclusion.

Source: the normalizer calculation N(O₂(C(2B))) = E₂¹¹.M₂₄ in GLS3,
Table 5.3i, printed p.270. The literal matrix words are documented in
`Cardinality.Subgroup`, and `LocalStructure.Mathieu` identifies their local
kernel with the intrinsic two-core of max1.
-/

public section

open Subgroup
namespace Janko4.LocalStructure
open Cardinality

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

/-- The ambient normalizer of the embedded local kernel lies in literal max1. -/
theorem normalizer_embedded_localKernel_le_max1 :
    normalizer ((localKernel matrixA_mul_self matrixB_pow_four).map
      (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype : Set Model) ≤
        max1Subgroup matrixA_mul_self matrixB_pow_four := by
  intro g hg
  obtain ⟨h, hh, he⟩ := MathieuNormalizer.localKernel_action_realization g hg
  have hc : h⁻¹ * g ∈ centralizer
      ((localKernel matrixA_mul_self matrixB_pow_four).map
        (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype : Set Model) := by
    intro x hx
    have hxh := congrArg (fun y : Model => h⁻¹ * y * g) (he x hx)
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hxh.symm
  have hm := (max1Subgroup matrixA_mul_self matrixB_pow_four).mul_mem hh
    (centralizer_embedded_localKernel_le_max1 hc)
  simpa only [mul_inv_cancel_left] using hm

end Janko4.LocalStructure
