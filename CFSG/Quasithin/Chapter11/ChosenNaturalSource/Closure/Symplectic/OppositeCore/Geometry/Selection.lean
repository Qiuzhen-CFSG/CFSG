module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Selection.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Selection.Spaces
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Selection.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Selection.Containment

/-!
# The marked opposite-action geometry in the original group

The radical root image and the actual marked flag determine an opposite
lift in L. Its pair has the literal first-plane SL₂ image, its original
quotient spaces are complementary, its core lies in O₂(LT), and three
L₁-conjugates generate L modulo that same core. The geometric sum also
puts the literal denominator (W∩Wʸ)V inside Q.

The Cartan-compatible endpoint also supplies opposite-point and core-pair
normalization by X, and proves X₁≤I in the original group. The natural-module
and opposite-stabilizer Cartan arguments giving Q≤O₂(G₁) remain with the
final opposite-core assembly.
Source: Aschbacher--Smith, 11.5.7, printed p.783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The action and complementary-space part of the source opposite choice,
including its actual denominator and three original L₁ conjugators. -/
theorem exists_opposite_pair_geometry (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hroot : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁) :
    ∃ (g : Sp E.input.field.Carrier) (y : L),
      (∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ) ∧
      PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom ∧
      PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹ ∧
      actionImage (V := V) (oppositeJoin (auxiliaryW E) (y : G)) =
        (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map
          (FullAction.modelHom m) ∧
      IsCompl E.threeSpace (E.point.map (D.chosenCentralAction y)) ∧
      E.V₃ ⊔ E.V₁.map (MulAut.conj (y : G)).toMonoidHom = V ∧
      E.V₃ ⊓ E.V₁.map (MulAut.conj (y : G)).toMonoidHom = V ⊓ centralizer (L : Set G) ∧
      (oppositeJoin (auxiliaryW E) (y : G)).pCoreIn 2 ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      pairDenominator E (y : G) ≤ corePair (auxiliaryW E) (y : G) ∧
      ∃ l : Fin 3 → G, (∀ i, l i ∈ E.L₁) ∧
        L ≤ (⨆ i, (oppositeJoin (auxiliaryW E) (y : G)).map
          (MulAut.conj (l i)).toMonoidHom) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨g,y,hflag,hlocal,hy,hi,hc,hl⟩ := exists_marked_opposite_action E m hW hroot
  have hs := opposite_preimages E m g hflag y hy
  exact ⟨g,y,hflag,hlocal,hy,hi,opposite_quotient_spaces_complementary E m g hflag y hy,
    hs.1,hs.2,hc,opposition_denominator_le_corePair E m hW hPhi g hflag y hy,hl⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
