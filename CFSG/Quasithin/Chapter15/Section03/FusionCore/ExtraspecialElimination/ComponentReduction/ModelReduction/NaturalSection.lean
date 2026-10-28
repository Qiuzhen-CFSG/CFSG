module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.SeedAction
public import Theory.Representation.SL2CubicFixedSection

/-!
# The natural-section contradiction in the component reduction

The centralization of `Z_S` by `Y₀` supplies fixed vectors in the literal
section `U_H/Z`. Equivariant natural-section coordinates force these vectors
into the component fixed space. Splitting off the global fixed space and
using `U_H = ⟨Z_S^H⟩` then annihilates the component's star image.

The B.2.14 sum decomposition and actual rank-one natural-section
identification are explicit inputs. No disjointness of the two summands
and no assertion that `Y₀*` has order three is required. The remaining
larger-field reduction must construct these inputs and a cubic element.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49 between (k) and (l), printed p.1144.
-/

@[expose] public section

open Subgroup Matrix Representation.BinaryOffender Representation.SL2CubicFixedSection
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

section Application
variable {G : Type*} [Group G]

/-- Source centralization of the seed gives fixation on its actual quotient. -/
lemma seed_fixed_of_centralizes
    (H ZS Z Y0 : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hcent : Y0 ≤ centralizer (ZS : Set G)) (z : ZS) :
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
      ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩) ∈
        fixedSpace action.representation (starImage H Y0) := by
  rintro ⟨y, ⟨a, ha, rfl⟩⟩
  change action.representation (QuotientGroup.mk' (pCore 2 H) a)
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
        ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩)) = _
  rw [action.on_representatives]
  have hc : (a : G) * z = z * a := (mem_centralizer_iff.mp (hcent ha) z z.property).symm
  have he : (⟨(a : G) * z * (a : G)⁻¹,
      le_normalizer_iff.mp action.normalizes a a.property z
        (le_conjugateSpanBy ZS H z.property)⟩ : localSpan ZS H) =
        ⟨z, le_conjugateSpanBy ZS H z.property⟩ := by
    apply Subtype.ext
    change (a : G) * z * (a : G)⁻¹ = (z : G)
    rw [hc, mul_inv_cancel_right]
  rw [he]

/-- Apply the natural-section fixed-space calculation to the generating seed. -/
lemma starImage_eq_bot_of_natural_section
    (H ZS Z L Y0 : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hZSH : ZS ≤ H) (hLH : L ≤ H) (hHL : H ≤ normalizer (L : Set G))
    (D : Submodule (ZMod 2) (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H))))
    (hsplit : D ⊔ fixedSpace action.representation ⊤ = ⊤)
    (sectionModel : NaturalComponentSection (F := F) action.representation (starImage H L) D)
    (hYL : Y0 ≤ L) (hcubic : ∃ y : starImage H Y0, orderOf y = 3)
    (hB : ∀ y : starImage H Y0,
      sectionModel.model ⟨y, (map_mono (comap_mono hYL)) y.property⟩ ∈
        SpecialLinearGroup.rankOneBorel F)
    (hcent : Y0 ≤ centralizer (ZS : Set G)) : starImage H L = ⊥ := by
  apply starImage_eq_bot_of_fixedSpace_projection H ZS Z L Y0 action hZSH hLH hHL D hsplit
  · exact fixedSpace_le_of_natural_section action.representation _ _ D sectionModel
      (map_mono (comap_mono hYL)) hcubic hB
  · exact seed_fixed_of_centralizes H ZS Z Y0 action hcent

end Application
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
