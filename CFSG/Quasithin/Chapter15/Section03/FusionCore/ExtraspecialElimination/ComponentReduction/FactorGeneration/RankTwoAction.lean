module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.SolvableFactor
public import Theory.Representation.BinaryPlaneNormalizer

/-!
# Eliminating the solvable rank-two factor

The actual S₃ star action splits into its faithful moved plane and its fixed
space. The two-perfect Y₀ normalizes the factor, hence either centralizes its
star image or has fixed space contained in that of the factor. The first case
contradicts the residual-normalizer argument. In the second case the factor
fixes the image of Z_S in U_H/Z; since Z ≤ Z_S, it normalizes Z_S and lies in M.
This contradicts the escape of its order-three generators.

This proves conditional elimination of every SolvableStarFactor from the
stated local inputs. Constructing a factor when component generation fails
remains the separate B.5.6 classification obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(i), printed pp.1143–1144; B.5.6, printed pp.105–110.
-/

@[expose] public section

open Subgroup Representation

open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration
variable {G : Type*} [Group G]

/-- Fixing the image of the seed implies normalization of the seed itself,
since the entire quotient kernel lies in the seed. -/
theorem normalizes_seed_of_fixed_image
    (H ZS Z L : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hZ : Z ≤ ZS) (hLH : L ≤ H)
    (hseed : ∀ z : ZS,
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
        ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩) ∈
          fixedSpace action.representation (starImage H L)) :
    L ≤ normalizer (ZS : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl z hz
  let u : localSpan ZS H := ⟨z, le_conjugateSpanBy ZS H hz⟩
  let lH : H := ⟨l, hLH hl⟩
  have hf := hseed ⟨z, hz⟩
    ⟨QuotientGroup.mk' (pCore 2 H) lH, ⟨lH, hl, rfl⟩⟩
  change action.representation (QuotientGroup.mk' (pCore 2 H) lH)
    (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H)) u)) =
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H)) u) at hf
  rw [action.on_representatives] at hf
  have he := congrArg Additive.toMul hf
  have hc := QuotientGroup.eq_iff_div_mem.mp he
  change (l * z * l⁻¹) / z ∈ Z at hc
  simpa only [div_mul_cancel] using ZS.mul_mem (hZ hc) hz

namespace SolvableStarFactor
variable {H ZS Z A : Subgroup G} [IsElementaryAbelian 2 (localSpan ZS H)]
  {action : SectionAction H (localSpan ZS H) Z}
  (F : SolvableStarFactor H ZS Z A action)

/-- The rank-two action forces centralization or containment of fixed spaces. -/
theorem rankTwo_dichotomy [Finite G] (Y0 : Subgroup G)
    (hYH : Y0 ≤ H) (hY : IsPPerfect 2 Y0) :
    ⁅starImage H F.carrier, starImage H Y0⁆ = ⊥ ∨
      fixedSpace action.representation (starImage H Y0) ≤
        fixedSpace action.representation (starImage H F.carrier) :=
  Representation.BinaryPlaneNormalizer.symmetric_three_twoPerfect_dichotomy action.representation action.faithful
    _ _ F.model F.commutator_rank (starImage_twoPerfect H Y0 hYH hY)
    (F.star_normalizes Y0 hYH hY)

include F in
/-- Eliminate the putative S₃ factor from the genuine local and seed inputs.
Existence of a candidate remains the separate B.5.6 classification obligation. -/
theorem eliminate [Finite G] (M Y0 T : Subgroup G)
    (hZ : Z ≤ ZS) (hAH : A ≤ H) (hYH : Y0 ≤ H) (hY : IsPPerfect 2 Y0)
    (hN : normalizer (Y0 : Set G) = M) (hQM : localTwoCore H ≤ M)
    (hθ : theta (M ⊓ H) = Y0)
    (hA : starImage H A ≤
      (pCore 2 ↥(starImage H Y0 ⊔ starImage H T)).map
        (starImage H Y0 ⊔ starImage H T).subtype)
    (hseed : ∀ z : ZS,
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
        ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩) ∈
          fixedSpace action.representation (starImage H Y0))
    (hseedN : normalizer (ZS : Set G) ≤ M) : False := by
  rcases F.rankTwo_dichotomy Y0 hYH hY with hc | hf
  · exact F.star_commutator_ne_bot M Y0 T hAH hYH hY hN hQM hθ hA hc
  · exact F.not_le_M M Y0 T hAH hθ hA
      ((normalizes_seed_of_fixed_image H ZS Z F.carrier action hZ
        (F.le_span.trans (conjugateSpanBy_le_self hAH)) (fun z => hf (hseed z))).trans hseedN)

end SolvableStarFactor
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration
