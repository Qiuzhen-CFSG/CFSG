module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders
/-!
# The original covered L₀ normalizer

For the actual L₀ = O²(O₂,Z(L)), its quotient by the two-core has order
three, so L₀ is nontrivial. It is characteristic under every normalizer of L.
In the original Hypothesis 12.2.1, A/C uniqueness and characteristic two
therefore identify N_G(L₀) with N_G(L), using the same covered natural setup.
No normalizer bound or classification conclusion is assumed.

Source: Aschbacher--Smith 13.2.2(9), printed p.878.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V V₁ V₃ : Subgroup G}

theorem NaturalSetup.zero_ne_bot (d : NaturalSetup L (T : Subgroup G) V V₁ V₃) :
    zero L ≠ ⊥ := by
  intro he
  have hc := d.zero_core_card
  rw [he] at hc
  have h1 : Nat.card ((⊥ : Subgroup G) ⧸ pCore 2 (⊥ : Subgroup G)) = 1 :=
    Nat.card_unique
  omega

theorem NaturalSetup.zero_normalizer_eq
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    normalizer (zero L : Set G) = normalizer (L : Set G) := by
  apply le_antisymm _ (normalizer_le_zero_normalizer L)
  exact h.normal_subgroup_normalizer_le d.normalizes_L ((zero_le L).trans le_sup_left)
    d.zero_ne_bot ((sup_le L.le_normalizer d.normalizes_L).trans (normalizer_le_zero_normalizer L))
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
