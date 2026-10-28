module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Checker

/-!
# Checked inverse for the max4 commutant

Each inverse row reconstructs the corresponding coordinate row from the orbit basis.
These certificates discharge `InverseCheck` in `lowerTriangular_of_checks`.
Source: `../source/README.md` and `../../source/reconstruction.json`.
Regenerate these proof declarations with `Calibration/source/generate.py`.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof

-- Avoid checking several substantial fixed-table reductions concurrently.
set_option Elab.async false

private theorem inverse_0 : InverseCheck 0 :=
  Calibration.inverse_of_skip 0 (by decide +kernel)

private theorem inverse_1 : InverseCheck 1 :=
  Calibration.inverse_of_skip 1 (by decide +kernel)

private theorem inverse_2 : InverseCheck 2 :=
  Calibration.inverse_of_skip 2 (by decide +kernel)

private theorem inverse_3 : InverseCheck 3 :=
  Calibration.inverse_of_skip 3 (by decide +kernel)

private theorem inverse_4 : InverseCheck 4 :=
  Calibration.inverse_of_skip 4 (by decide +kernel)

private theorem inverse_5 : InverseCheck 5 :=
  Calibration.inverse_of_skip 5 (by decide +kernel)

private theorem inverse_6 : InverseCheck 6 :=
  Calibration.inverse_of_skip 6 (by decide +kernel)

private theorem inverse_7 : InverseCheck 7 :=
  Calibration.inverse_of_skip 7 (by decide +kernel)

private theorem inverse_8 : InverseCheck 8 :=
  Calibration.inverse_of_skip 8 (by decide +kernel)

private theorem inverse_9 : InverseCheck 9 :=
  Calibration.inverse_of_skip 9 (by decide +kernel)

private theorem inverse_10 : InverseCheck 10 :=
  Calibration.inverse_of_skip 10 (by decide +kernel)

private theorem inverse_11 : InverseCheck 11 :=
  Calibration.inverse_of_skip 11 (by decide +kernel)

private theorem inverse_12 : InverseCheck 12 :=
  Calibration.inverse_of_skip 12 (by decide +kernel)

private theorem inverse_13 : InverseCheck 13 :=
  Calibration.inverse_of_skip 13 (by decide +kernel)

private theorem inverse_14 : InverseCheck 14 :=
  Calibration.inverse_of_skip 14 (by decide +kernel)

private theorem inverse_15 : InverseCheck 15 :=
  Calibration.inverse_of_skip 15 (by decide +kernel)

private theorem inverse_16 : InverseCheck 16 :=
  Calibration.inverse_of_skip 16 (by decide +kernel)

private theorem inverse_17 : InverseCheck 17 :=
  Calibration.inverse_of_skip 17 (by decide +kernel)

private theorem inverse_18 : InverseCheck 18 :=
  Calibration.inverse_of_skip 18 (by decide +kernel)

private theorem inverse_19 : InverseCheck 19 :=
  Calibration.inverse_of_skip 19 (by decide +kernel)

private theorem inverse_20 : InverseCheck 20 :=
  Calibration.inverse_of_skip 20 (by decide +kernel)

private theorem inverse_21 : InverseCheck 21 :=
  Calibration.inverse_of_skip 21 (by decide +kernel)

private theorem inverse_22 : InverseCheck 22 :=
  Calibration.inverse_of_skip 22 (by decide +kernel)

private theorem inverse_23 : InverseCheck 23 :=
  Calibration.inverse_of_skip 23 (by decide +kernel)

private theorem inverse_24 : InverseCheck 24 :=
  Calibration.inverse_of_skip 24 (by decide +kernel)

private theorem inverse_25 : InverseCheck 25 :=
  Calibration.inverse_of_skip 25 (by decide +kernel)

private theorem inverse_26 : InverseCheck 26 :=
  Calibration.inverse_of_skip 26 (by decide +kernel)

private theorem inverse_27 : InverseCheck 27 :=
  Calibration.inverse_of_skip 27 (by decide +kernel)

private theorem inverse_28 : InverseCheck 28 :=
  Calibration.inverse_of_skip 28 (by decide +kernel)

private theorem inverse_29 : InverseCheck 29 :=
  Calibration.inverse_of_skip 29 (by decide +kernel)

private theorem inverse_30 : InverseCheck 30 :=
  Calibration.inverse_of_skip 30 (by decide +kernel)

private theorem inverse_31 : InverseCheck 31 :=
  Calibration.inverse_of_skip 31 (by decide +kernel)

private theorem inverse_32 : InverseCheck 32 :=
  Calibration.inverse_of_skip 32 (by decide +kernel)

private theorem inverse_33 : InverseCheck 33 :=
  Calibration.inverse_of_skip 33 (by decide +kernel)

private theorem inverse_34 : InverseCheck 34 :=
  Calibration.inverse_of_skip 34 (by decide +kernel)

private theorem inverse_35 : InverseCheck 35 :=
  Calibration.inverse_of_skip 35 (by decide +kernel)

private theorem inverse_36 : InverseCheck 36 :=
  Calibration.inverse_of_skip 36 (by decide +kernel)

private theorem inverse_37 : InverseCheck 37 :=
  Calibration.inverse_of_skip 37 (by decide +kernel)

private theorem inverse_38 : InverseCheck 38 :=
  Calibration.inverse_of_skip 38 (by decide +kernel)

private theorem inverse_39 : InverseCheck 39 :=
  Calibration.inverse_of_skip 39 (by decide +kernel)

private theorem inverse_40 : InverseCheck 40 :=
  Calibration.inverse_of_skip 40 (by decide +kernel)

private theorem inverse_41 : InverseCheck 41 :=
  Calibration.inverse_of_skip 41 (by decide +kernel)

private theorem inverse_42 : InverseCheck 42 :=
  Calibration.inverse_of_skip 42 (by decide +kernel)

private theorem inverse_43 : InverseCheck 43 :=
  Calibration.inverse_of_skip 43 (by decide +kernel)

private theorem inverse_44 : InverseCheck 44 :=
  Calibration.inverse_of_skip 44 (by decide +kernel)

private theorem inverse_45 : InverseCheck 45 :=
  Calibration.inverse_of_skip 45 (by decide +kernel)

private theorem inverse_46 : InverseCheck 46 :=
  Calibration.inverse_of_skip 46 (by decide +kernel)

private theorem inverse_47 : InverseCheck 47 :=
  Calibration.inverse_of_skip 47 (by decide +kernel)

private theorem inverse_48 : InverseCheck 48 :=
  Calibration.inverse_of_skip 48 (by decide +kernel)

private theorem inverse_49 : InverseCheck 49 :=
  Calibration.inverse_of_skip 49 (by decide +kernel)

private theorem inverse_50 : InverseCheck 50 :=
  Calibration.inverse_of_skip 50 (by decide +kernel)

private theorem inverse_51 : InverseCheck 51 :=
  Calibration.inverse_of_skip 51 (by decide +kernel)

private theorem inverse_52 : InverseCheck 52 :=
  Calibration.inverse_of_skip 52 (by decide +kernel)

private theorem inverse_53 : InverseCheck 53 :=
  Calibration.inverse_of_skip 53 (by decide +kernel)

private theorem inverse_54 : InverseCheck 54 :=
  Calibration.inverse_of_skip 54 (by decide +kernel)

private theorem inverse_55 : InverseCheck 55 :=
  Calibration.inverse_of_skip 55 (by decide +kernel)

private theorem inverse_56 : InverseCheck 56 :=
  Calibration.inverse_of_skip 56 (by decide +kernel)

private theorem inverse_57 : InverseCheck 57 :=
  Calibration.inverse_of_skip 57 (by decide +kernel)

private theorem inverse_58 : InverseCheck 58 :=
  Calibration.inverse_of_skip 58 (by decide +kernel)

private theorem inverse_59 : InverseCheck 59 :=
  Calibration.inverse_of_skip 59 (by decide +kernel)

private theorem inverse_60 : InverseCheck 60 :=
  Calibration.inverse_of_skip 60 (by decide +kernel)

private theorem inverse_61 : InverseCheck 61 :=
  Calibration.inverse_of_skip 61 (by decide +kernel)

private theorem inverse_62 : InverseCheck 62 :=
  Calibration.inverse_of_skip 62 (by decide +kernel)

private theorem inverse_63 : InverseCheck 63 :=
  Calibration.inverse_of_skip 63 (by decide +kernel)

private theorem inverse_64 : InverseCheck 64 :=
  Calibration.inverse_of_skip 64 (by decide +kernel)

private theorem inverse_65 : InverseCheck 65 :=
  Calibration.inverse_of_skip 65 (by decide +kernel)

private theorem inverse_66 : InverseCheck 66 :=
  Calibration.inverse_of_skip 66 (by decide +kernel)

private theorem inverse_67 : InverseCheck 67 :=
  Calibration.inverse_of_skip 67 (by decide +kernel)

private theorem inverse_68 : InverseCheck 68 :=
  Calibration.inverse_of_skip 68 (by decide +kernel)

private theorem inverse_69 : InverseCheck 69 :=
  Calibration.inverse_of_skip 69 (by decide +kernel)

private theorem inverse_70 : InverseCheck 70 :=
  Calibration.inverse_of_skip 70 (by decide +kernel)

private theorem inverse_71 : InverseCheck 71 :=
  Calibration.inverse_of_skip 71 (by decide +kernel)

private theorem inverse_72 : InverseCheck 72 :=
  Calibration.inverse_of_skip 72 (by decide +kernel)

private theorem inverse_73 : InverseCheck 73 :=
  Calibration.inverse_of_skip 73 (by decide +kernel)

private theorem inverse_74 : InverseCheck 74 :=
  Calibration.inverse_of_skip 74 (by decide +kernel)

private theorem inverse_75 : InverseCheck 75 :=
  Calibration.inverse_of_skip 75 (by decide +kernel)

private theorem inverse_76 : InverseCheck 76 :=
  Calibration.inverse_of_skip 76 (by decide +kernel)

private theorem inverse_77 : InverseCheck 77 :=
  Calibration.inverse_of_skip 77 (by decide +kernel)

private theorem inverse_78 : InverseCheck 78 :=
  Calibration.inverse_of_skip 78 (by decide +kernel)

private theorem inverse_79 : InverseCheck 79 :=
  Calibration.inverse_of_skip 79 (by decide +kernel)

private theorem inverse_80 : InverseCheck 80 :=
  Calibration.inverse_of_skip 80 (by decide +kernel)

private theorem inverse_81 : InverseCheck 81 :=
  Calibration.inverse_of_skip 81 (by decide +kernel)

private theorem inverse_82 : InverseCheck 82 :=
  Calibration.inverse_of_skip 82 (by decide +kernel)

private theorem inverse_83 : InverseCheck 83 :=
  Calibration.inverse_of_skip 83 (by decide +kernel)

private theorem inverse_84 : InverseCheck 84 :=
  Calibration.inverse_of_skip 84 (by decide +kernel)

private theorem inverse_85 : InverseCheck 85 :=
  Calibration.inverse_of_skip 85 (by decide +kernel)

private theorem inverse_86 : InverseCheck 86 :=
  Calibration.inverse_of_skip 86 (by decide +kernel)

private theorem inverse_87 : InverseCheck 87 :=
  Calibration.inverse_of_skip 87 (by decide +kernel)

private theorem inverse_88 : InverseCheck 88 :=
  Calibration.inverse_of_skip 88 (by decide +kernel)

private theorem inverse_89 : InverseCheck 89 :=
  Calibration.inverse_of_skip 89 (by decide +kernel)

private theorem inverse_90 : InverseCheck 90 :=
  Calibration.inverse_of_skip 90 (by decide +kernel)

private theorem inverse_91 : InverseCheck 91 :=
  Calibration.inverse_of_skip 91 (by decide +kernel)

private theorem inverse_92 : InverseCheck 92 :=
  Calibration.inverse_of_skip 92 (by decide +kernel)

private theorem inverse_93 : InverseCheck 93 :=
  Calibration.inverse_of_skip 93 (by decide +kernel)

private theorem inverse_94 : InverseCheck 94 :=
  Calibration.inverse_of_skip 94 (by decide +kernel)

private theorem inverse_95 : InverseCheck 95 :=
  Calibration.inverse_of_skip 95 (by decide +kernel)

private theorem inverse_96 : InverseCheck 96 :=
  Calibration.inverse_of_skip 96 (by decide +kernel)

private theorem inverse_97 : InverseCheck 97 :=
  Calibration.inverse_of_skip 97 (by decide +kernel)

private theorem inverse_98 : InverseCheck 98 :=
  Calibration.inverse_of_skip 98 (by decide +kernel)

private theorem inverse_99 : InverseCheck 99 :=
  Calibration.inverse_of_skip 99 (by decide +kernel)

private theorem inverse_100 : InverseCheck 100 :=
  Calibration.inverse_of_skip 100 (by decide +kernel)

private theorem inverse_101 : InverseCheck 101 :=
  Calibration.inverse_of_skip 101 (by decide +kernel)

private theorem inverse_102 : InverseCheck 102 :=
  Calibration.inverse_of_skip 102 (by decide +kernel)

private theorem inverse_103 : InverseCheck 103 :=
  Calibration.inverse_of_skip 103 (by decide +kernel)

private theorem inverse_104 : InverseCheck 104 :=
  Calibration.inverse_of_skip 104 (by decide +kernel)

private theorem inverse_105 : InverseCheck 105 :=
  Calibration.inverse_of_skip 105 (by decide +kernel)

private theorem inverse_106 : InverseCheck 106 :=
  Calibration.inverse_of_skip 106 (by decide +kernel)

private theorem inverse_107 : InverseCheck 107 :=
  Calibration.inverse_of_skip 107 (by decide +kernel)

private theorem inverse_108 : InverseCheck 108 :=
  Calibration.inverse_of_skip 108 (by decide +kernel)

private theorem inverse_109 : InverseCheck 109 :=
  Calibration.inverse_of_skip 109 (by decide +kernel)

private theorem inverse_110 : InverseCheck 110 :=
  Calibration.inverse_of_skip 110 (by decide +kernel)

private theorem inverse_111 : InverseCheck 111 :=
  Calibration.inverse_of_skip 111 (by decide +kernel)

attribute [local irreducible] InverseCheck

theorem inverse_checked : ∀ i, InverseCheck i := by
  intro i
  fin_cases i
  · exact inverse_0
  · exact inverse_1
  · exact inverse_2
  · exact inverse_3
  · exact inverse_4
  · exact inverse_5
  · exact inverse_6
  · exact inverse_7
  · exact inverse_8
  · exact inverse_9
  · exact inverse_10
  · exact inverse_11
  · exact inverse_12
  · exact inverse_13
  · exact inverse_14
  · exact inverse_15
  · exact inverse_16
  · exact inverse_17
  · exact inverse_18
  · exact inverse_19
  · exact inverse_20
  · exact inverse_21
  · exact inverse_22
  · exact inverse_23
  · exact inverse_24
  · exact inverse_25
  · exact inverse_26
  · exact inverse_27
  · exact inverse_28
  · exact inverse_29
  · exact inverse_30
  · exact inverse_31
  · exact inverse_32
  · exact inverse_33
  · exact inverse_34
  · exact inverse_35
  · exact inverse_36
  · exact inverse_37
  · exact inverse_38
  · exact inverse_39
  · exact inverse_40
  · exact inverse_41
  · exact inverse_42
  · exact inverse_43
  · exact inverse_44
  · exact inverse_45
  · exact inverse_46
  · exact inverse_47
  · exact inverse_48
  · exact inverse_49
  · exact inverse_50
  · exact inverse_51
  · exact inverse_52
  · exact inverse_53
  · exact inverse_54
  · exact inverse_55
  · exact inverse_56
  · exact inverse_57
  · exact inverse_58
  · exact inverse_59
  · exact inverse_60
  · exact inverse_61
  · exact inverse_62
  · exact inverse_63
  · exact inverse_64
  · exact inverse_65
  · exact inverse_66
  · exact inverse_67
  · exact inverse_68
  · exact inverse_69
  · exact inverse_70
  · exact inverse_71
  · exact inverse_72
  · exact inverse_73
  · exact inverse_74
  · exact inverse_75
  · exact inverse_76
  · exact inverse_77
  · exact inverse_78
  · exact inverse_79
  · exact inverse_80
  · exact inverse_81
  · exact inverse_82
  · exact inverse_83
  · exact inverse_84
  · exact inverse_85
  · exact inverse_86
  · exact inverse_87
  · exact inverse_88
  · exact inverse_89
  · exact inverse_90
  · exact inverse_91
  · exact inverse_92
  · exact inverse_93
  · exact inverse_94
  · exact inverse_95
  · exact inverse_96
  · exact inverse_97
  · exact inverse_98
  · exact inverse_99
  · exact inverse_100
  · exact inverse_101
  · exact inverse_102
  · exact inverse_103
  · exact inverse_104
  · exact inverse_105
  · exact inverse_106
  · exact inverse_107
  · exact inverse_108
  · exact inverse_109
  · exact inverse_110
  · exact inverse_111

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof
