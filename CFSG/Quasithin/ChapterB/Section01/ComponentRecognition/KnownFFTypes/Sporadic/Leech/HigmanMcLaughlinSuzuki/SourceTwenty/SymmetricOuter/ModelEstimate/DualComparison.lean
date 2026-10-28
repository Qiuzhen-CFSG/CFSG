module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.SymmetricOuter.ModelEstimate.Reduction
public import Theory.Representation.SymmetricEightConstituents.OuterDual

/-!
# Discharging the marked outer-dual comparison for the HS induced eight-space

The explicit nonsingular pairing on the four-space intertwines the literal
outer action and the natural dual action. This discharges the comparison
premise of the even-actor model estimate, with the exceptional marking and
(0 1) conjugation used by the actual induced representation.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, pp.16--17; Aschbacher--Smith K.4, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Symmetric
open Representation.SymmetricEightConstituents

/-- The actual outer-conjugate natural four-space is its marked dual. -/
theorem outerDualComparison : HasOuterDualComparison :=
  ⟨outerDualEquiv, outerDualEquiv_equivariant⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Symmetric
