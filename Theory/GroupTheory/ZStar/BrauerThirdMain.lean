module

public import Theory.GroupTheory.ZStar.ThirdMain.ObstructionExistence
public import Theory.GroupTheory.ZStar.ThirdMain.NoExtraObstruction

/-!
# Principal Brauer equality for an involution

The ambient principal block idempotent restricts under the involution Brauer
map to the compatible local principal idempotent. If equality failed, the
primitive-factor reduction would give an extra obstruction. Choose one of
maximal subgroup order and take its normalizer-orbit idempotent. A maximal
coefficient-support subgroup in the normalizer contains the canonical
original subgroup. Equality of these subgroups contradicts the exact-support
transfer theorem; strict inclusion produces a larger extra obstruction,
contradicting the chosen maximality.

This unconditional equality is the block-theoretic input to characterwise
local core support. The assembly assumes no correspondence theorem or local
support statement. Shared coefficient and transfer helpers are re-exported
with their historical names.
Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BrauerThirdMain.lean` (revision `c3503435`).
-/

public section

noncomputable section

namespace Glauberman.ZStar.BrauerThirdMain

open ModularBlock Subgroup PrincipalBlockConstruction

export ModularBlock.BrauerThirdMain
  (subgroupRestriction_conjugationMap_q_mul
    subgroupRestriction_relativeTransfer_eq_subtype_of_fixedTerms_zero
    normalizerAlgebraEmbedding_coeff_centralizes
    subgroupOf_normalizer_isPGroup
    subgroupRestriction_subgroupSubtypeMap_normalizerAlgebraEmbedding
    subgroupSubtypeMap_apply_image
    normalizerAlgebraEmbedding_apply_image
    subgroupRestriction_normalizerEmbedding_subgroupRestriction_eq
    centralizer_map_normalizerSubtype_le_normalizer
    eq_zero_of_subgroupRestriction_mul_eq_self_of_corner_augmentation_zero
    fixedTerm_zero_of_exact_normalizer_support
    false_of_exact_normalizer_support)

universe v

attribute [local instance] Fintype.ofFinite

theorem involutionPrincipalBrauerEquality
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G)
    (z : G) (hzI : IsInvolution z) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  by_contra hne
  obtain ⟨Q, hQ⟩ := exists_extraObstruction_of_not_brauerEquality d z hzI hne
  exact not_isExtraObstruction d Q hQ


end Glauberman.ZStar.BrauerThirdMain

namespace Glauberman.ZStar

universe v

/-- Unconditional principal Brauer equality for an involution. -/
theorem involutionPrincipalBrauerEquality
    {G : Type v} [Group G] [Finite G]
    (d : ModularBlock.PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hzI : IsInvolution z) :
    ModularBlock.CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z :=
  BrauerThirdMain.involutionPrincipalBrauerEquality d z hzI

end Glauberman.ZStar
