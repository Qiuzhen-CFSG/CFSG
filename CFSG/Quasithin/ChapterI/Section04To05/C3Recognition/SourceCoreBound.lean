module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.SourcePointAction
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PointCoreBound
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.Noncollinear

/-!
# C₃ reconstruction with all local-action inputs discharged

The faithful point action and the point-core order bound now follow from
the bare D-system. The reconstruction consumes only the later global
incidence conclusions: 63 points, noncollinearity and one-or-all triples.
I.5.9–14 remain the explicit source producer for these three conclusions.
-/

public noncomputable section
namespace Quasithin.I5.C3Recognition
open Theory.LinearAlgebra
open Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] (S : DSystem .C3 G)

def equivSp6_of_source_geometry (hc : Nat.card S.Point = 63)
    (hn : ∀ x : S.Point, ∃ y, ¬ S.Collinear x y)
    (ht : ∀ x y : S.Point, x ≠ y → ∃ z, BinaryPolarGeometry.OneOrAll S.Collinear x y z) :
    G ≃* Sp (ZMod 2) :=
  equivSp6_of_source_incidence S hc hn ht S.point_core_card_ge_thirty_two

/-- Only the global point count and the singular/nonsingular triples remain. -/
def equivSp6_of_source_triples (hc : Nat.card S.Point = 63)
    (ht : ∀ x y : S.Point, x ≠ y → ∃ z, BinaryPolarGeometry.OneOrAll S.Collinear x y z) :
    G ≃* Sp (ZMod 2) :=
  equivSp6_of_source_geometry S hc S.c3_exists_noncollinear ht

end Quasithin.I5.C3Recognition
