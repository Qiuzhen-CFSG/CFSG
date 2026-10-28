module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowGeometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowNormalizerReduction
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Automorphisms
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Reduction
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order

/-!
# Self-normalizing Sylow two-subgroups of the native J₄ model

The characteristic elementary kernel of a max1 Sylow forces every ambient
Sylow normalizer to preserve max1. Its two-core is characteristic, and its
proved ambient normalizer is max1 itself. The original max1 quotient map
then reduces Sylow self-normalization to the native M₂₄ calculation.

The application to a cubic permuting with a full Sylow excludes the normal
Sylow case of the three-coset action. It therefore identifies the actual
product modulo its two-core with S₃.

Source: GLS3 Table 5.3i; Aschbacher–Smith 4.4.3, printed p.623.
The imported ATLAS words and certificates retain their attribution and license.
-/

public noncomputable section
open Subgroup
namespace Janko4
open Cardinality OuterReduction.OddIndex
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

private theorem max1_self_normalizing :
    normalizer (max1Subgroup matrixA_mul_self matrixB_pow_four : Set Model) ≤
      max1Subgroup matrixA_mul_self matrixB_pow_four := by
  have hn := normalizer_le_normalizer_characteristic_image
    (max1Subgroup matrixA_mul_self matrixB_pow_four)
    (pCore 2 (max1Subgroup matrixA_mul_self matrixB_pow_four))
  rw [←LocalStructure.localKernel_eq_twoCore] at hn
  exact hn.trans LocalStructure.normalizer_embedded_localKernel_le_max1

/-- Every Sylow two-subgroup is self-normalizing in the original matrix model. -/
theorem sylow_normalizer_eq (S : Sylow 2 Model) :
    normalizer (S : Set Model) = (S : Subgroup Model) := by
  apply le_antisymm _ (S : Subgroup Model).le_normalizer
  apply LocalStructure.SymmetricLinear.sylowNormalizer_le_of_max1Normalizer
  · intro g hg
    apply max1_self_normalizing
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply LocalStructure.max1_invariant_of_sylow_image_invariant localSylow (MulAut.conj g)
    exact mem_normalizer_iff_map_conj_eq.mp hg
  · intro P
    exact Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.sylow_normalizer_le
      Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate_card
      (Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate_automorphisms_isPGroup
        Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate_card) P
end Janko4
