module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.Initial
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore

/-!
# The original core containment after the initial symplectic closure argument

The full-cover commutators and ambient radical comparison prove the initial
U-abelianness and root-image assertions. Applying the opposite-pair theorem
to those very subgroups then places O₂(L) inside O₂(G₁). The source Cartan,
flag coordinates and conclusions through 11.5.6 remain explicit earlier
inputs. Characteristic-subgroup reduction and the final terminal assembly
remain with qt-d-1222-natural-closure-sp4.

Source: Aschbacher--Smith 11.5.7, printed pp.782--783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The initial branch and opposite-core transfer on the literal chosen
module. No U-abelianness, root action or core-containment premise remains. -/
theorem initial_and_opposite_core_of_preceding (m : MarkedFlag E)
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
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hne : ¬ IsMulCommutative E.W) :
    V ≤ E.G₁.pCoreIn 2 ∧ E.W ≤ E.G₁.pCoreIn 2 ∧ IsMulCommutative E.U ∧
      L.pCoreIn 2 ≤ E.G₁.pCoreIn 2 := by
  have hXL : E.X ≤ L := hX.1.trans inf_le_left
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact OppositeGeometry.cartan_normalizes_marked_flag E m hX 0
  obtain ⟨hV,hW,hU,hroot,hmove,_,hPhi,_⟩ :=
    RadicalAction.initial_branch_of_preceding E m g hpoint hthree hcartan hXL hXG
      hn3 hirr hti hgen hVX hfour hfive hne
  exact ⟨hV,hW,hU,NaturalQuotient.core_le_point_core E m hX hV hW hroot hmove hPhi
    hfour hfive hti (CoverGeometry.radical_commutator m g hpoint hthree) hgen⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
