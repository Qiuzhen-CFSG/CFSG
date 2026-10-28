module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Action
public import Theory.GroupTheory.PResidual.CubicKernel

/-!
# Residual and index consequences of the ordinary action image

Once the action image of BL₁ is covered by L₁, the source product
factorization puts O²(O³(B)) in the actual centralizing residual C.
This uses the cubic intrinsic quotient of L₁ and relative normality of C,
not an identification of the full A₄ action image with a cyclic group.
Together with the odd Borel quotient, it gives O³(B) ≤ C O₂(B).

The concrete action-image calculation remains an explicit model premise
of these reduction theorems. It must be discharged in the ordinary source
assembly; none of the repaired residual or index conclusions is an input.

Source: the sufficient two-kernel calculation for Aschbacher–Smith 13.8.20,
printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Consequences
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : NaturalSetup L (T : Subgroup G) V V₁)

include a in
private theorem iterated_residual_le_of_factorization
    (hfactor : d.B ⊔ one L (T : Subgroup G) V₁ =
      centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔ one L (T : Subgroup G) V₁) :
    residualIn 2 (residualIn 3 d.B) ≤
      centralizingResidual d.B (one L (T : Subgroup G) V₁) L := by
  let X := one L (T : Subgroup G) V₁
  let J := d.B ⊔ X
  let C := centralizingResidual d.B X L
  have hCJ : C ≤ J := centralizingResidual_le _ _ _
  have hXJ : X ≤ J := le_sup_right
  let _ : (C.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCJ).mpr
      (TwoKernels.product_normalizes_centralizingResidual d)
  have hgen : C.subgroupOf J ⊔ X.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup hCJ hXJ, ← hfactor, subgroupOf_self]
  let e := subgroupOfEquivOfLe hXJ
  have hcube : Nat.card ((X.subgroupOf J) ⧸ pCore 2 (X.subgroupOf J)) = 3 :=
    (Nat.card_congr
      (Theory.GroupTheory.ComponentLocalCoreSection.quotientCoreEquiv 2 e.toMonoidHom
        e.surjective (IsPGroup.ker_isPGroup_of_injective e.injective)).toEquiv).trans
          (source_residual_quotient_card a X rfl)
  have hj := two_threeResidual_le_normal_of_cubic_supplement
    (C.subgroupOf J) (X.subgroupOf J) hgen hcube
  have hm := map_mono (f := J.subtype) hj
  rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hCJ] at hm
  exact (embedded_pResidual_mono 2 (embedded_pResidual_mono 3
    (show d.B ≤ J from le_sup_left))).trans hm

/-- Covering the genuine model action puts the iterated Borel residual in C. -/
theorem iterated_residual_le_of_action_image
    (himage : ∀ g : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G),
      ∃ l : one L (T : Subgroup G) V₁,
        Action.modelAction d a g = Action.modelAction d a (inclusion le_sup_right l)) :
    residualIn 2 (residualIn 3 d.B) ≤
      centralizingResidual d.B (one L (T : Subgroup G) V₁) L :=
  iterated_residual_le_of_factorization d a (Action.product_eq_of_action_image d a himage)

/-- The required saturated containment uses the proved odd residual supplement. -/
theorem saturated_residual_le_of_action_image
    (hab : ⁅d.B, d.B⁆ ≤ d.B.pCoreIn 2)
    (himage : ∀ g : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G),
      ∃ l : one L (T : Subgroup G) V₁,
        Action.modelAction d a g = Action.modelAction d a (inclusion le_sup_right l)) :
    residualIn 3 d.B ≤
      centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔ d.B.pCoreIn 2 := by
  rw [TwoKernels.borel_threeResidual d hab]
  exact sup_le_sup (iterated_residual_le_of_action_image d a himage) le_rfl

/-- All hypotheses of the corrected cubic-index adapter are discharged by the
source data and the same concrete model-image premise. -/
theorem cubic_index_of_action_image
    (himage : ∀ g : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G),
      ∃ l : one L (T : Subgroup G) V₁,
        Action.modelAction d a g = Action.modelAction d a (inclusion le_sup_right l)) :
    (centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔
      (d.B ⊔ one L (T : Subgroup G) V₁).pCoreIn 2).relIndex
        (d.B ⊔ one L (T : Subgroup G) V₁) = 3 :=
  TwoKernels.cubic_index_of_factorization d a (Action.product_eq_of_action_image d a himage)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Consequences
