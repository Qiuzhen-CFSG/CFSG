module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.FullImage
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.KernelSeparation

/-!
# The original point action in C₃ reconstruction

The source local-core calculation now supplies the faithful action required
by the six-space reconstruction. Only the subsequent I.5.9–14 incidence
conclusions and the I.5.15 core-order bound remain explicit below. These
are earlier source obligations, not an assumed representation or recognition.

The conclusion uses the original D-system point cosets and the actual
binary symplectic group from `FullImage`.
-/

public noncomputable section
namespace Quasithin.I5.C3Recognition
open Theory.LinearAlgebra
open Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem geometryData_of_incidence (hc : Nat.card S.Point = 63)
    (hn : ∀ x : S.Point, ∃ y, ¬ S.Collinear x y)
    (ht : ∀ x y : S.Point, x ≠ y → ∃ z, BinaryPolarGeometry.OneOrAll S.Collinear x y z) :
    GeometryData S where
  card_points := hc
  faithful_points := S.faithful_points
  noncollinear := hn
  triples := ht

def equivSp6_of_source_incidence (hc : Nat.card S.Point = 63)
    (hn : ∀ x : S.Point, ∃ y, ¬ S.Collinear x y)
    (ht : ∀ x y : S.Point, x ≠ y → ∃ z, BinaryPolarGeometry.OneOrAll S.Collinear x y z)
    (hQ : 32 ≤ Nat.card (pCore 2 (S.family 0))) : G ≃* Sp (ZMod 2) :=
  equivSp6_of_geometry S (geometryData_of_incidence S hc hn ht) hQ

end Quasithin.I5.C3Recognition
