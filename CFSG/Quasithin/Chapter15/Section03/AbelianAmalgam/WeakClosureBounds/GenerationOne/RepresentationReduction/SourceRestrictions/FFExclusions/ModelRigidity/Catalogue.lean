module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.SourceCases.Models
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The central component carriers in B.4.2

This catalogue records actual multiplicative equivalences, with their defining
field cardinalities. It lists central quotients of the components, rather than
the offender-generated overgroups H. In particular S₅ and S₇ contribute A₅
and A₇; Sp₄(2) and G₂(2) contribute their literal derived subgroups. The
triple cover of A₆ contributes A₆ after taking its center quotient, and the
two L₄(2) and two L₅(2) module alternatives share their respective carriers.
Thus no exceptional central quotient in any of the eleven alternatives is
discarded. An alternating entry has parameter zero, meaning no field parameter.

Membership is only a conclusion predicate. Deriving it from the complete
B.4.2 or B.5.1 output remains the responsibility of the classification owner.
The comparisons in this directory also accept the binary SL₂ endpoint;
quasisimplicity can exclude that endpoint in the source application.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.4.2--3,
printed p.86, B.4.4, p.87, B.5.1, pp.99--100, and E.2.2, pp.215--216.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity

open Matrix
open scoped MatrixGroups

/-- Distinct entries retain the small derived and alternating endpoints. -/
inductive Family
  | linearTwo | linearThree | symplecticFour | gTwo
  | symplecticFourTwoDerived | gTwoTwoDerived
  | alternatingFive | alternatingSix | alternatingSeven
  | linearFourTwo | linearFiveTwo
  deriving DecidableEq

/-- The possible central component carriers, connected to S by actual
isomorphisms. The natural-number index is the defining field cardinality. -/
inductive ComponentModel (S : Type*) [Group S] : Family → ℕ → Prop
  | linearTwo (F : Type) [Field F] [Finite F] {n : ℕ}
      (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (e : S ≃* PSL(2, F)) :
      ComponentModel S .linearTwo (2 ^ n)
  | linearThree (F : Type) [Field F] [Finite F] {n : ℕ}
      (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (e : S ≃* PSL(3, F)) :
      ComponentModel S .linearThree (2 ^ n)
  | symplecticFour (F : Type) [Field F] [Finite F] {n : ℕ}
      (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
      (e : S ≃* (Theory.SpecificGroups.SymplecticFour.Sp F ⧸
        Subgroup.center (Theory.SpecificGroups.SymplecticFour.Sp F))) :
      ComponentModel S .symplecticFour (2 ^ n)
  | gTwo (F : Type) [Field F] [Finite F] {n : ℕ}
      (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (e : S ≃* Atlas.G2.Model F) :
      ComponentModel S .gTwo (2 ^ n)
  | symplecticFourTwoDerived
      (e : S ≃* commutator (Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2))) :
      ComponentModel S .symplecticFourTwoDerived 2
  | gTwoTwoDerived (e : S ≃* commutator (Atlas.G2.Model (ZMod 2))) :
      ComponentModel S .gTwoTwoDerived 2
  | alternatingFive (e : S ≃* alternatingGroup (Fin 5)) :
      ComponentModel S .alternatingFive 0
  | alternatingSix (e : S ≃* alternatingGroup (Fin 6)) :
      ComponentModel S .alternatingSix 0
  | alternatingSeven (e : S ≃* alternatingGroup (Fin 7)) :
      ComponentModel S .alternatingSeven 0
  | linearFourTwo (e : S ≃* PSL(4, ZMod 2)) :
      ComponentModel S .linearFourTwo 2
  | linearFiveTwo (e : S ≃* PSL(5, ZMod 2)) :
      ComponentModel S .linearFiveTwo 2

/-- Transport keeps both the family and the field parameter. -/
theorem ComponentModel.transport {S R : Type*} [Group S] [Group R]
    {family : Family} {q : ℕ} (h : ComponentModel S family q) (e : R ≃* S) :
    ComponentModel R family q := by
  cases h with
  | linearTwo F hn hF a => exact .linearTwo F hn hF (e.trans a)
  | linearThree F hn hF a => exact .linearThree F hn hF (e.trans a)
  | symplecticFour F hn hF a => exact .symplecticFour F hn hF (e.trans a)
  | gTwo F hn hF a => exact .gTwo F hn hF (e.trans a)
  | symplecticFourTwoDerived a => exact .symplecticFourTwoDerived (e.trans a)
  | gTwoTwoDerived a => exact .gTwoTwoDerived (e.trans a)
  | alternatingFive a => exact .alternatingFive (e.trans a)
  | alternatingSix a => exact .alternatingSix (e.trans a)
  | alternatingSeven a => exact .alternatingSeven (e.trans a)
  | linearFourTwo a => exact .linearFourTwo (e.trans a)
  | linearFiveTwo a => exact .linearFiveTwo (e.trans a)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
