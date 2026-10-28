module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction

/-!
# Simplicity of the actual characteristic-two Spin group

Normal-root extraction, followed by the checked root-generation argument,
proves simplicity of the concrete connected algebraic group. Universality
is a separate geometric assertion and is not inferred from point faithfulness.

Source: GLS3, Theorem 1.13.1 and the D4 construction in §1.14.
-/

public section
namespace Triality.SimplyConnected
open Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The concrete D4 Spin algebraic group is simple. -/
theorem source_simple : IsSimpleAlgebraicGroup (groupVariety k) :=
  isSimple_of_normal_root_extraction k (NormalRootExtraction.exists_rootPoint_mem k)

end Triality.SimplyConnected
