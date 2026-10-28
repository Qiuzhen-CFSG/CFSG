module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Frattini
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CoreAssembly

/-!
# Applying the proved Cartan actions to the symplectic closure

The source Frattini action 11.5.6(4) is now available in both parities from
preceding marked geometry. Combine it with the proved core commutator (5)
and apply the existing full-cover and opposite-pair argument. This puts the
original seed, its G₁-closure and O₂(L) in O₂(G₁), and proves that U is
abelian in the contrary branch. No 11.5.6 action conclusion is assumed.

The remaining inputs are the original flag and parabolic markings, TI,
local generation, and the preceding strict-component geometry. Their final
discharge remains with qt-d-1222-natural-closure and its earlier-input owners;
the characteristic-subgroup and terminal parts of 11.5.7 remain open here.
Source: Aschbacher--Smith 11.5.6(4--5) and 11.5.7, pp.781--783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The actual initial symplectic closure consumer with both Cartan-action
premises discharged, retaining all preceding source geometry. -/
theorem initial_and_opposite_core_of_cartan (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hrank : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    (hstrict : E.L₁ < E.K → ⁅E.R₁,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hne : ¬ IsMulCommutative E.W) :
    V ≤ E.G₁.pCoreIn 2 ∧ E.W ≤ E.G₁.pCoreIn 2 ∧ IsMulCommutative E.U ∧
      L.pCoreIn 2 ≤ E.G₁.pCoreIn 2 := by
  have hXL : E.X ≤ L := hX.1.trans inf_le_left
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact OppositeGeometry.cartan_normalizes_marked_flag E m hX 0
  have hfour (P : Subgroup G) (hPX : ⁅P,E.X⁆ = P) (hPT : P ≤ T)
      (hphi : (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2) :
      ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2 :=
    E.cartan_frattini_action_of_marked (m.point_ne_bot E)
      m.sylow_le_point_normalizer hXG (LocalGeometry.Coordinates.sp4 m.action)
      hX hXR hCX hz hNG hrank hexception P hPT hPX.symm hphi
  have hfive := E.core_commutator_le
    ((hXL.trans le_sup_left).trans (L ⊔ (T : Subgroup G)).le_normalizer) hstrict
  exact initial_and_opposite_core_of_preceding E m g hpoint hthree hX hcartan
    hn3 hirr hti hgen hVX hfour hfive hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
