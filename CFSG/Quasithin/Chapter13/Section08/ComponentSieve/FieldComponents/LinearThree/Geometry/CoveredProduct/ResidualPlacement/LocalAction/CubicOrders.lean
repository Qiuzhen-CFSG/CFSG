module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders.Transport
public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders

/-!
# Intrinsic cubic quotients of the covered local residuals

The center of the actual hexacode triple cover has order three. The image
of its central preimage's two-residual is the whole center, since elements
of odd order survive the two-residual. Relative normality then identifies
L₀/O₂(L₀) with that center.

The companion transport module identifies the second source quotient with
the intrinsic quotient of the concrete point commutator residual. The model
calculation gives order three for every Sylow-stable natural line. The actual
point and Sylow marking supplied by the natural setup discharge those
premises. Only the source factorization from 13.2.2(3) remains an explicit
input to the second order theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, printed p.877, and application 13.8.21(1), printed p.957.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralPreimage_star (L : Subgroup G) :
    Source.starImage L (centralPreimage L) = center (L ⧸ pCore 2 L) := by
  unfold Source.starImage centralPreimage
  rw [← comap_subtype, comap_map_eq_self_of_injective L.subtype_injective,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

/-- The first cubic order in Notation 13.2.1, derived from the actual cover. -/
theorem NaturalSetup.zero_core_card {L T V V₁ V₃ : Subgroup G}
    (d : NaturalSetup L T V V₁ V₃) : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3 := by
  have hc : Nat.card (center (L ⧸ pCore 2 L)) = 3 :=
    (Nat.card_congr (Subgroup.centerCongr d.cover).toEquiv).trans
      Representation.Hexacode.even_center_card
  have hr : residual (center (L ⧸ pCore 2 L)) = center (L ⧸ pCore 2 L) := by
    apply le_antisymm (residual_le _)
    intro x hx
    refine ⟨⟨x, hx⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
    exact (by decide : Nat.Coprime 2 3).of_dvd_right
      (hc ▸ orderOf_dvd_natCard (⟨x, hx⟩ : center (L ⧸ pCore 2 L)))
  have hs : Source.starImage L (zero L) = center (L ⧸ pCore 2 L) := by
    rw [zero, star_residual L (centralPreimage L) (map_subtype_le _),
      centralPreimage_star, hr]
  have hn : (Source.starImage L (zero L)).Normal := by rw [hs]; infer_instance
  exact (Nat.card_congr (normalStarEquiv L (zero L) (zero_le L) hn).toEquiv).trans
    (by rwa [hs])

/-- The second cubic order in Notation 13.2.1, for `i = 1`, derived from
the actual natural action and the source factorization in 13.2.2(3). -/
theorem NaturalSetup.plus_core_card {L T V V₁ V₃ : Subgroup G}
    (d : NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3 := by
  rw [CubicOrders.plus_core_card_eq_model d hfactor]
  exact Representation.Hexacode.CubicLocalModel.Orders.commutatorResidual_quotient_card
    d.point (CubicOrders.coverSylow d) d.point_dim
    (CubicOrders.coverSylow_le_stabilizer d)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
