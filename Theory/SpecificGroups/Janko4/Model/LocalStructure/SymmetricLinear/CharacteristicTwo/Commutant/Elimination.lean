module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Elimination.Pivots
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Elimination.Upper0
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Elimination.Upper1
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Elimination.Upper2
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Elimination.Upper3
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Elimination.Upper4
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Elimination.Upper5
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Elimination.Upper6

/-!
# Complete pivot and strictly upper-entry elimination certificates

The two unconditional exports certify every original `PivotCheck` and
`UpperCheck`. They use scalar kernel reductions and a proved indexed traversal
of the unchanged equation, pivot and expression tables. The final application
supplies both families to `lowerTriangular_of_checks`; the independent numerical
calibration premises remain with the commutant assembly owner.

Source: `Commutant/source/README.md` and `Elimination/source/README.md`.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof

theorem pivots_checked : ∀ t, PivotCheck t := Elimination.all_pivots

theorem upper_checked : ∀ i, UpperCheck i := by
  intro i
  fin_cases i
  · exact Elimination.upperRow0
  · exact Elimination.upperRow1
  · exact Elimination.upperRow2
  · exact Elimination.upperRow3
  · exact Elimination.upperRow4
  · exact Elimination.upperRow5
  · exact Elimination.upperRow6
  · exact Elimination.upperRow7
  · exact Elimination.upperRow8
  · exact Elimination.upperRow9
  · exact Elimination.upperRow10
  · exact Elimination.upperRow11
  · exact Elimination.upperRow12
  · exact Elimination.upperRow13
  · exact Elimination.upperRow14
  · exact Elimination.upperRow15
  · exact Elimination.upperRow16
  · exact Elimination.upperRow17
  · exact Elimination.upperRow18
  · exact Elimination.upperRow19
  · exact Elimination.upperRow20
  · exact Elimination.upperRow21
  · exact Elimination.upperRow22
  · exact Elimination.upperRow23
  · exact Elimination.upperRow24
  · exact Elimination.upperRow25
  · exact Elimination.upperRow26
  · exact Elimination.upperRow27
  · exact Elimination.upperRow28
  · exact Elimination.upperRow29
  · exact Elimination.upperRow30
  · exact Elimination.upperRow31
  · exact Elimination.upperRow32
  · exact Elimination.upperRow33
  · exact Elimination.upperRow34
  · exact Elimination.upperRow35
  · exact Elimination.upperRow36
  · exact Elimination.upperRow37
  · exact Elimination.upperRow38
  · exact Elimination.upperRow39
  · exact Elimination.upperRow40
  · exact Elimination.upperRow41
  · exact Elimination.upperRow42
  · exact Elimination.upperRow43
  · exact Elimination.upperRow44
  · exact Elimination.upperRow45
  · exact Elimination.upperRow46
  · exact Elimination.upperRow47
  · exact Elimination.upperRow48
  · exact Elimination.upperRow49
  · exact Elimination.upperRow50
  · exact Elimination.upperRow51
  · exact Elimination.upperRow52
  · exact Elimination.upperRow53
  · exact Elimination.upperRow54
  · exact Elimination.upperRow55
  · exact Elimination.upperRow56
  · exact Elimination.upperRow57
  · exact Elimination.upperRow58
  · exact Elimination.upperRow59
  · exact Elimination.upperRow60
  · exact Elimination.upperRow61
  · exact Elimination.upperRow62
  · exact Elimination.upperRow63
  · exact Elimination.upperRow64
  · exact Elimination.upperRow65
  · exact Elimination.upperRow66
  · exact Elimination.upperRow67
  · exact Elimination.upperRow68
  · exact Elimination.upperRow69
  · exact Elimination.upperRow70
  · exact Elimination.upperRow71
  · exact Elimination.upperRow72
  · exact Elimination.upperRow73
  · exact Elimination.upperRow74
  · exact Elimination.upperRow75
  · exact Elimination.upperRow76
  · exact Elimination.upperRow77
  · exact Elimination.upperRow78
  · exact Elimination.upperRow79
  · exact Elimination.upperRow80
  · exact Elimination.upperRow81
  · exact Elimination.upperRow82
  · exact Elimination.upperRow83
  · exact Elimination.upperRow84
  · exact Elimination.upperRow85
  · exact Elimination.upperRow86
  · exact Elimination.upperRow87
  · exact Elimination.upperRow88
  · exact Elimination.upperRow89
  · exact Elimination.upperRow90
  · exact Elimination.upperRow91
  · exact Elimination.upperRow92
  · exact Elimination.upperRow93
  · exact Elimination.upperRow94
  · exact Elimination.upperRow95
  · exact Elimination.upperRow96
  · exact Elimination.upperRow97
  · exact Elimination.upperRow98
  · exact Elimination.upperRow99
  · exact Elimination.upperRow100
  · exact Elimination.upperRow101
  · exact Elimination.upperRow102
  · exact Elimination.upperRow103
  · exact Elimination.upperRow104
  · exact Elimination.upperRow105
  · exact Elimination.upperRow106
  · exact Elimination.upperRow107
  · exact Elimination.upperRow108
  · exact Elimination.upperRow109
  · exact Elimination.upperRow110
  · exact Elimination.upperRow111

/-- Discharge exactly the two elimination families in the exhaustive commutant
reduction, retaining the independent calibration contracts verbatim. -/
theorem lowerTriangular_of_calibration
    (hd : ∀ a, DifferenceCheck a) (hcols : ∀ a, ColumnCheck a)
    (hc : ∀ j, ExpressionColumnCheck j) (hi : ∀ i, InitialCheck i)
    (ho : ∀ i, OrbitCheck i) (hinv : ∀ i, InverseCheck i)
    (hs : ∀ i, SmallCheck i) (he : ∀ t, EquationCheck t)
    (M : BinaryMatrix)
    (hM : ∀ a, Commute M (decodeRows (Coordinates.conjugateRows.get a))) :
    ∀ i j : Fin 112, i < j → M i j = 0 :=
  lowerTriangular_of_checks hd hcols hc hi ho hinv hs he pivots_checked upper_checked M hM

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof
