module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.ComparisonA
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.ComparisonB
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.PackedA
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.PackedB

/-!
# The exact Fi22 generators preserve the certificate graph

The comparison modules identify the packed point maps with the inverse ATLAS
cycle products. The packed invariance modules certify the graph rows by bit
transformations and prove how those transformations act on individual columns.
Transport gives invariance under the original generators, supplying the two
invariance premises of `Fi22CentralizerKernel.isPGroup_fixedPointAction_ker_of_graph`.
The separate signature-separation premise remains with the kernel assembly.

Source: ATLAS F22G1-p3510B0 and GLS3 Table 5.3t. No centralizer identification,
external computation as proof, or group-order certificate is used.
-/

public section
namespace Sporadic.Fischer.Fi22.KernelCertificate

/-- The original first ATLAS generator preserves the certificate relation. -/
theorem related_generatorA (x y : Fin 3510) :
    related (generatorA x) (generatorA y) = related x y := by
  rw [generatorA_apply_eq_fastA, generatorA_apply_eq_fastA]
  exact related_fastA x y

/-- The original second ATLAS generator preserves the certificate relation. -/
theorem related_generatorB (x y : Fin 3510) :
    related (generatorB x) (generatorB y) = related x y := by
  rw [generatorB_apply_eq_fastB, generatorB_apply_eq_fastB]
  exact related_fastB x y

end Sporadic.Fischer.Fi22.KernelCertificate
