module

public import Theory.GroupAction.CoprimeTwoOuter
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Components
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Parameters

/-!
# The small-outer-group rows of the odd component sieve

The original Cartan normalizes every relative component. Its literal
two-core quotient actors have odd order coprime to the component order.
A two-group outer quotient therefore makes every actor trivial, proving
the source commutator bound. In particular the actual odd-characteristic
PSL₂ models of field degree at most two are eliminated using their proved
full outer-group calculation.

This is a component-case exclusion, not the complete source sieve.
The remaining catalogue inspection and final assembly stay with
qt-d-1222-natural-closure-cartan. Only the preceding point geometry and
split Cartan marking remain explicit in the applications below.

Source: Aschbacher--Smith A.3.15(1), pp.50--51, and 11.5.6(3), p.781.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- A full two-group outer quotient eliminates a moved original component. -/
theorem component_commutator_of_outer_two
    (hp : E.point ≠ ⊥) (hX : E.X ≤ E.G₁) (ho : Odd (Nat.card E.X))
    (eX : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (houter : IsPGroup 2 (MulAut.Outer (I ⧸ pCore 2 I))) :
    ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2 := by
  by_contra hm
  obtain ⟨x,hx,hne⟩ := E.exists_component_quotient_mover hp hX ho hI hm
  have hd : orderOf (coreQuotientAction I x) ∣ Nat.card E.X := by
    apply (orderOf_map_dvd (coreQuotientAction I) x).trans
    rw [← Subgroup.orderOf_coe x]
    exact E.X.orderOf_dvd_natCard hx
  exact hne (MulAut.eq_one_of_odd_coprime_of_outer_two _
    (ho.of_dvd_nat hd) ((E.cartan_coprime_component_of_split_marking eX hc hI).of_dvd
      hd (pCore 2 I).card_quotient_dvd_card) houter)

/-- The odd-characteristic PSL₂ rows of Theorem C cannot be moved by X. -/
theorem oddLinearTwo_component_commutator
    (hp : E.point ≠ ⊥) (hX : E.X ≤ E.G₁) (ho : Odd (Nat.card E.X))
    (eX : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    {p n : ℕ} (hpprime : p.Prime) (hpodd : Odd p) (hn : n ≤ 2)
    (he : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (p ^ n)) :
    ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  apply E.component_commutator_of_outer_two hp hX ho eX hc hI
  exact (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
    hpprime hpodd hn hF).of_equiv (MulAut.outerCongr e).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
