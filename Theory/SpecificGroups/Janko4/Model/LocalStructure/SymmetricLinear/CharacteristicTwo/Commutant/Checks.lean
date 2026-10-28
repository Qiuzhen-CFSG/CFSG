module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Tables

/-!
# Exact finite identities for the commutant bound

The first checks calibrate the literal qₖ−I tables and the four generating rows.
The orbit checks reconstruct their images under any commuting matrix. The last
checks express all strictly upper entries as combinations of commutator equations.
In particular the format certifies exhaustive coverage, including singular matrices.
Source: `CharacteristicTwo/source/README.md` and `Commutant/source/generate.py`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof

def DifferenceCheck (a : Fin 11) : Prop := ∀ i : Fin 112,
  (differences.get a).get i = (Coordinates.conjugateRows.get a).get i ^^^ 2 ^ i.val

def ColumnCheck (a : Fin 11) : Prop := ∀ i j : Fin 112,
  ((columns.get a).get j).testBit i.val = ((differences.get a).get i).testBit j.val

def ExpressionColumnCheck (j : Fin 112) : Prop := ∀ i : Fin 112,
  (expressionColumns.get j).get i = (expressions.get i).get j

def InitialCheck (i : Fin 4) : Prop :=
  orbitRows.get (Fin.castLE (by decide) i) = 2 ^ (Fin.natAdd 108 i).val ∧
  ∀ j : Fin 112, (expressions.get (Fin.castLE (by decide) i)).get j =
    2 ^ (finProdFinEquiv (i, j)).val

def OrbitCheck (i : Fin 112) : Prop := 4 ≤ i.val →
  (parents.get i).val < i.val ∧
  scan (orbitRows.get (parents.get i)) (differences.get (factors.get i)).toList =
    orbitRows.get i ∧
  ∀ j : Fin 112,
    scan ((columns.get (factors.get i)).get j) (expressions.get (parents.get i)).toList =
      (expressions.get i).get j

def InverseCheck (i : Fin 112) : Prop :=
  scan (inverseRows.get i) orbitRows.toList = 2 ^ i.val

def SmallCheck (i : Fin 112) : Prop :=
  scan (smallRows.get i) orbitRows.toList = scan (orbitRows.get i) difference0.toList

def EquationCheck (t : Fin 418) : Prop :=
  let ij := equationPositions.get t
  equationRows.get t =
    scan (column0.get ij.2) (expressions.get ij.1).toList ^^^
      scan (smallRows.get ij.1) (expressionColumns.get ij.2).toList

def PivotCheck (t : Fin 418) : Prop :=
  scan (pivotSources.get t) equationRows.toList = pivotRows.get t

def UpperCheck (i : Fin 112) : Prop := ∀ j : Fin 112, i < j →
  scan (inverseRows.get i) (expressionColumns.get j).toList =
    scan ((upperWitnesses.get i).get j) pivotRows.toList

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof
