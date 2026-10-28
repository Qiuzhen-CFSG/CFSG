module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Core
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.NaturalSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup

/-!
# Inputs to the ordinary and covered local Borel calculations

The context retains the genuine standing counterexample and natural flag,
the literal local residuals of Notation 13.2.1, and an actual higher-field
model. The allowed preceding steps B≤M and L₁T-normalization are explicit,
as are the two exact assertions of 13.7.3(9). Neither a B_C identity,
a cubic index, nor an inverter is an input.

The ordinary and covered natural-action interfaces are re-exported so that
both branches can use their existing concrete quotient markings. The covered
factorization from 13.2.2(3) and normalizer bounds from (9) remain separate
earlier source inputs when needed.

Source: Aschbacher–Smith, Notation 13.2.1, p.877; Hypothesis 13.7.1, p.935;
13.7.3(9), p.936; proof of 13.8.20, p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- Only standing data and the preceding permitted conclusions. -/
structure SourceContext (T : Sylow 2 G) (H K L V V₁ V₂ V₃ M G₁ : Subgroup G)
    [(Source.starImage H K).Normal] (n : ℕ) (unitary four : Bool) where
  standing : TransvectionRecognition.Component.ModelExtension.LocalSetup T L V V₁ V₂ V₃ M G₁
  member : H ∈ Source.Hz (one L (T : Subgroup G) V₁) (T : Subgroup G) G₁ M
  component_le : K ≤ H
  sylow_H : Chapter1.IsSylowIn 2 (T : Subgroup G) H
  model : TorusModels.Assembly.Model.{u,v} (Source.starImage H K) n unitary four
  degree : 1 < n
  generated : H = K ⊔ one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G)
  borel_in_M : borel H K (T : Subgroup G) component_le sylow_H ≤ M
  borel_normalized : one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) ≤
    normalizer (borel H K (T : Subgroup G) component_le sylow_H : Set G)
  intersection : H ⊓ M = H ⊓ normalizer (V : Set G)
  theta : one L (T : Subgroup G) V₁ = closure {g : G | g ∈ H ⊓ M ∧ orderOf g = 3}

namespace SourceContext
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)

/-- The actual B attached to this context. -/
noncomputable abbrev B : Subgroup G := borel H K (T : Subgroup G) d.component_le d.sylow_H

include d

theorem one_le_H : one L (T : Subgroup G) V₁ ≤ H := le_sup_left.trans d.member.1.2

theorem T_le_H : (T : Subgroup G) ≤ H := le_sup_right.trans d.member.1.2

theorem one_le_M : one L (T : Subgroup G) V₁ ≤ M := by
  rw [d.standing.local_normalizer]
  exact (one_le _ _ _).trans (inf_le_left.trans
    (sup_le L.le_normalizer d.standing.normalizes_L))

/-- The product normalizes L using its actual placement in N_G(L). -/
theorem product_normalizes_L : d.B ⊔ one L (T : Subgroup G) V₁ ≤ normalizer (L : Set G) := by
  rw [← d.standing.local_normalizer]
  exact sup_le d.borel_in_M d.one_le_M

/-- The prescribed Sylow normalizes BL₁. -/
theorem T_normalizes_product : (T : Subgroup G) ≤
    normalizer ((d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G) : Set G) :=
  (le_inf (le_sup_right.trans d.borel_normalized)
    (T_normalizes_one L (T : Subgroup G) V₁ d.standing.line_stable)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The exact order-three closure in BL₁, derived by restriction. -/
theorem theta_product : one L (T : Subgroup G) V₁ =
    closure {g : G | g ∈ d.B ⊔ one L (T : Subgroup G) V₁ ∧ orderOf g = 3} :=
  theta_restrict H M _ _ d.theta le_sup_right
    (le_inf (sup_le ((borel_le_component _ _ _ _ _).trans d.component_le) d.one_le_H)
      (sup_le d.borel_in_M d.one_le_M))

end SourceContext

/-- Inversion on the actual intrinsic quotient, written without a choice of
quotient representatives. The normalizer clause makes it an automorphism. -/
def InvertsTwoCoreQuotient (X : Subgroup G) (t : G) : Prop :=
  t ∈ normalizer (X : Set G) ∧ ∀ x ∈ X, t * x * t⁻¹ * x ∈ X.pCoreIn 2

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
