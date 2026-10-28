module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.TensorInputs

/-!
# The natural tensor section with the constructed source product marking

The covered-product geometry constructs the component, cubic and point
parabolic images and supplies normalization and both seed commutator identities.
The seed tensor argument therefore gives a literal natural chief section of
U_H/V₁ under that very same product equivalence, from the earlier seed dimension
and nontrivial component action. In particular all critical-actor marks remain
available for the proper and saturated critical-pair arguments.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), covered-A₆ paragraph, printed p.957.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.SourceProductGeometry
open ResidualPlacement ExternalModules

variable {G : Type*} [Group G] [Finite G] {H K L T V₁ V₃ : Subgroup G}
    {eK : Source.starImage H K ≃* BinaryLinearThree.Group}
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The constructed source product has a natural tensor chief section, with
its component, residual L₀, cubic X and critical parabolic marks unchanged. -/
theorem exists_natural_tensor_chief_section
    (geo : SourceProductGeometry H K L T V₁ V₃ eK)
    (act : SourceAction H V₃ V₁)
    (hd : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2)
    (hn : ∃ k : Source.starImage H K, ∃ v, act.representation k v ≠ v) :
    ∃ A B : Subrepresentation act.representation,
      IsNaturalTensorChiefSection act.representation geo.equiv A B := by
  exact source_natural_tensor_chief_section H V₃ V₁ act geo.equiv
    K (one L T V₁) T (zero L) (plus L T V₁) geo.component_image hn
    geo.parabolic_seed_normalizes geo.plus_le (geo.plus_le_one.trans le_sup_left)
    geo.oneT_image geo.tensorCubic_inverse_image hd geo.component.seed_zero_fixed
    geo.component.seed_moved

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.SourceProductGeometry
