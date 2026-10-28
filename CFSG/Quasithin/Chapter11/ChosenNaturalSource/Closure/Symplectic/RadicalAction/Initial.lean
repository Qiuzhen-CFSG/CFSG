module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.CoverGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.FullAmbient

/-!
# The initial symplectic closure branch on the original module

The actual natural normalizer supplies the radical-image comparison, and
the full central cover supplies the root and radical commutators. Together
with the preceding Cartan and closure bounds these prove that U is abelian.
Under the contradiction hypothesis on W_H, its source auxiliary subgroup
has precisely the local root image and the required Frattini bound.

Only preceding flag, Cartan and 11.5.6 inputs remain explicit. In particular,
there is no ambient-innerness, radical-image, full-cover commutator or
hyperplane-fixer hypothesis. Final 11.5.7 assembly remains with
qt-d-1222-natural-closure-sp4.
Source: Aschbacher--Smith 11.5.7, printed pp.782--783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
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

include hpoint hthree hcartan hXL hXG hn3 hirr hti hgen hVX hfour hfive in
/-- The original V and W_H lie in O₂(G₁), and U is abelian. -/
theorem initial_bounds_and_U_abelian :
    V ≤ E.G₁.pCoreIn 2 ∧ E.W ≤ E.G₁.pCoreIn 2 ∧ IsMulCommutative E.U := by
  obtain ⟨hV,hW,hU,_,hc⟩ := initial_core_bounds E m hn3 hirr hti hgen hVX hfour hfive
  exact ⟨hV,hW,CoverGeometry.U_abelian m g hpoint hthree hcartan hXL hXG
    (FullAmbient.radical_image_le m g hpoint) hV hU hc⟩

include hpoint hthree hcartan hXL hXG hn3 hirr hti hgen hVX hfour hfive in
/-- All initial radical-action conclusions, with their original subgroup
maps and central attachment. The source correction is Φ(W)≤V₁. -/
theorem initial_branch_of_preceding (hne : ¬ IsMulCommutative E.W) :
    V ≤ E.G₁.pCoreIn 2 ∧ E.W ≤ E.G₁.pCoreIn 2 ∧ IsMulCommutative E.U ∧
    actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype ∧
    ⁅V,auxiliaryW E⁆ = E.V₁ ∧ ⁅E.V₃,auxiliaryW E⁆ = ⊥ ∧
    (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁ ∧
    auxiliaryW E ≤ E.W ∧ auxiliaryW E ≤ E.G₁.pCoreIn 2 ∧
    E.G₁ ≤ normalizer (auxiliaryW E : Set G) := by
  obtain ⟨hV,hW,hU,_,hc⟩ := initial_core_bounds E m hn3 hirr hti hgen hVX hfour hfive
  exact ⟨hV,hW,auxiliaryW_properties_of_action_comparisons E m g
    (PointModel.local_identification m g hpoint) hcartan hXL hXG
    (FullAmbient.radical_image_le m g hpoint) hV hW hU hc
    (CoverGeometry.root_centralizes_threeSpace m g hpoint hthree)
    (CoverGeometry.radical_commutator m g hpoint hthree)
    (CoverGeometry.root_commutator m g hpoint)
    (FullAmbient.local_fixer_bound m g hpoint hthree) hne⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction
