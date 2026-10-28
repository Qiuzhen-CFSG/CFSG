module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.PointNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus

/-!
# The even-degree component and Frattini actions

Source 11.5.6(1--2) excludes three from Y when the original field degree is
even. The full component classification then gives the actual Suzuki
quotient. The constructed orbit coordinates, field actor and diagonal
normalizer lifts prove BorelMovement, contradicting the checked original
point-normalizer calculation. This proves the component action in (3),
and the literal quotient/Frattini argument supplies (4).

The marked consumer uses Coordinates.cartanTorusEquiv and cartan_primeRank;
there is no additional torus or field-action input. Only the genuine preceding
point/flag, Cartan and local-centralizer geometry remains explicit, with final
discharge owned by qt-d-1222-natural-closure. The odd original degree branch
is separate.

Source: Aschbacher--Smith 11.5.6(3--4), printed pp.780--781.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
variable {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The even original degree supplies every component-detection premise. -/
theorem component_borel_detection_of_even
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (ho : Odd (Nat.card E.X))
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (eX : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    (he : Even E.input.field.degree) : E.ComponentBorelDetection := by
  intro I hI hmoved
  obtain ⟨m,hm,⟨e⟩⟩ := E.component_suzuki_of_even hp hc he hI
  exact E.suzuki_borel_movement_of_quotient hp hT hX ho hXR eX hc hI hm e hmoved

/-- Literal 11.5.6(3--4) in even degree, consuming the original natural marking. -/
theorem cartan_actions_of_even_marked (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (he : Even E.input.field.degree) :
    (∀ I : Subgroup G, Source.ComponentIn E.Y I → ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2) ∧
      (∀ P : Subgroup G, P ≤ T → P = ⁅P, E.X⁆ →
        (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P, E.Y⁆ ≤ E.Y.pCoreIn 2) := by
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  exact E.cartan_actions_of_borel_detection hp hT hX hcart hXR hCX hz hNG
    (E.oddPointNormalizerAction_of_cartan hT hX hcart)
    (E.component_borel_detection_of_even hp hT hX hcart.odd hXR
      (c.cartanTorusEquiv hcart) hc he)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
