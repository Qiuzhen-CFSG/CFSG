module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Recognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Component
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Products
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct.Inverter
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct.Assembly
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct.ComponentAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct.NormalizerBound

/-!
# The selected local marked five-normalizer product

The selected centralizer supplies an inverter in its root component,
including its fusion to the seed involution. The marked A₄ subgroup forces
the root-component normalizer to centralize the intrinsic five-component.
Frattini's argument through the marked root normalizer bounds the full
five-normalizer by 600. The two commuting factors already have that order,
so their marked internal product is the whole normalizer.

The quotient recognition equivalence is the permitted earlier intermediate
premise. No normalizer bound or component-action premise remains in
`selected_product`; ambient simplicity and order are unnecessary here.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct
variable {G : Type*} [Group G] [Finite G]

/-- Application to the literal selected geometry with the normalizer bound
and component action supplied explicitly. -/
theorem selected_product_of_bound_and_component_action {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (E : Subgroup G)
    (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t)
    (e : Quotient E ≃* alternatingGroup (Fin 5))
    (hN : Nat.card (normalizer (E : Set G)) ≤ 600)
    (hact : InvolutionGeometry.rootComponent S.t ⊓ normalizer (E : Set G) ≤
      centralizer (fiveComponent E : Set G)) : Nonempty (ProductData D E) := by
  obtain ⟨j, hjK, hjconj, hj, hinv⟩ := selected_inverter S E hE hEt
  exact productData_of_inverter_and_bound D E hE e hN j hj hjconj hinv
    (hact ⟨hjK, mem_normalizer_of_inverts E j hinv⟩)

/-- The selected geometry and recognized centralizer quotient give the literal
normalizer D₁₀ × A₅, with its intrinsic component and seed-conjugate inverter
marking the two factors. This supplies the local-product premise of
`MarkedNormalizer.rootFiveFamily_of_local_products`. -/
theorem selected_product {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (E : Subgroup G)
    (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer S.t)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) : Nonempty (ProductData D E) := by
  exact selected_product_of_bound_and_component_action S E hE hEt e
    (normalizer_card_le S E hE hEt e)
    (root_component_normalizer_centralizes S E hE hEt e)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct
