module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.ModelImage
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Consequences
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Centralization

/-!
# The ordinary Borel product and its two distinct kernels

The genuine ordinary action-image calculation discharges the factorization
premise in the residual and index reductions. Thus J = CL₁,
O²(O³(B)) ≤ C, and [J : C O₂(J)] = 3 are derived from the unchanged
SourceContext and NaturalSetup. The independent abelian-Borel hypothesis
gives the odd quotient and O³(B) = O²(O³(B)) O₂(B), hence its saturated
containment in C O₂(B).

Centralization of V is reduced in Centralization to the intrinsic natural
A₆ centralizer theorem. Construction of the marked inverter and final
source assembly remain separate obligations; the incompatible literal
ordinary residual/index assertions are preserved in Ordinary.lean.

Source: the sufficient two-kernel calculation for Aschbacher–Smith 13.8.20,
printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.LocalCalculation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : NaturalSetup L (T : Subgroup G) V V₁)

include a in
/-- The product factorization follows from the actual A₄ action image. -/
theorem factorization : d.B ⊔ one L (T : Subgroup G) V₁ =
    centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔ one L (T : Subgroup G) V₁ :=
  Action.product_eq_of_action_image d a (ModelImage.action_image d a)

include a in
/-- The iterated residual lies in the literal centralizing residual. -/
theorem iterated_residual_le : residualIn 2 (residualIn 3 d.B) ≤
    centralizingResidual d.B (one L (T : Subgroup G) V₁) L :=
  Consequences.iterated_residual_le_of_action_image d a (ModelImage.action_image d a)

include a in
/-- The cubic index retains O₂(J), distinct from the two-core of B. -/
theorem cubic_index :
    (centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔
      (d.B ⊔ one L (T : Subgroup G) V₁).pCoreIn 2).relIndex
        (d.B ⊔ one L (T : Subgroup G) V₁) = 3 :=
  Consequences.cubic_index_of_action_image d a (ModelImage.action_image d a)

include a in
/-- This saturated residual containment is sufficient for the repaired torus adapter. -/
theorem saturated_residual_le (hab : ⁅d.B, d.B⁆ ≤ d.B.pCoreIn 2) :
    residualIn 3 d.B ≤
      centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔ d.B.pCoreIn 2 :=
  Consequences.saturated_residual_le_of_action_image d a hab (ModelImage.action_image d a)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.LocalCalculation
