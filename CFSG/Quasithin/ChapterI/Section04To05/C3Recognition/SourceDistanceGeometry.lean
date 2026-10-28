module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.SourceCoreBound
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SingularTriples

/-!
# C₃ recognition after the original distance geometry

The local polar-residue facts now produce the 63 original points and all
singular triples. The remaining global input is precisely the nonsingular
one-or-all triple of I.5.13–14; no point count, faithfulness or core-order
hypothesis remains in this application of the six-space reconstruction.
-/

public noncomputable section
namespace Quasithin.I5.C3Recognition
open Theory.LinearAlgebra Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] (S : DSystem .C3 G)

def equivSp6_of_source_nonsingular_triples (d : S.LocalPolarFacts)
    (ht : ∀ x y : S.Point, ¬ S.Collinear x y →
      ∃ z, BinaryPolarGeometry.OneOrAll S.Collinear x y z) :
    G ≃* Sp (ZMod 2) :=
  equivSp6_of_source_triples S (S.c3_points_card d) (fun x y hxy => by
    by_cases h : S.Collinear x y
    · exact S.singular_one_or_all d hxy h
    · exact ht x y h)

end Quasithin.I5.C3Recognition
