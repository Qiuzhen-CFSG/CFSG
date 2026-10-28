module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.Model
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Filtration.Packed

/-!
# Packed certificate predicates for the eleven-coset matrices

A column certificate checks the left inverse and both generator intertwining
identities. A block certificate checks the zero tail and the entire diagonal
slice of each column in one of the 33 layers. The source arrays are used
literally; bit r in a column denotes row r.

Source: James, J. Algebra 27 (1973), 57–111; witness conventions in
`PointSimpleDegrees/source/README.md`.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks
open Data
open Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration

def originalColumns (s : Fin 2) : List ℕ :=
  (Witness.leftAction[s.val]!).toList.map (fun j => 2 ^ j.val)

def columnCertificate (j : ℕ) : Prop :=
  Packed.combineList Witness.inverseColumns.toList Witness.basisColumns[j]! = 2 ^ j ∧
  (∀ s : Fin 2,
    Packed.combineList (originalColumns s) Witness.basisColumns[j]! =
      Packed.combineList Witness.basisColumns.toList (Witness.adaptedColumns[s.val]!)[j]!)

def blockCertificate (t : Factor) : Prop :=
  ∀ (s : Fin 2) (y : Fin (degree t)),
    (Witness.adaptedColumns[s.val]!)[cut t.val + y.val]! >>> cut (t.val + 1) = 0 ∧
    ((Witness.adaptedColumns[s.val]!)[cut t.val + y.val]! >>> cut t.val) % 2 ^ degree t =
      ((modelColumns[(factorKind t).val]!)[s.val]!)[y.val]!

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks
