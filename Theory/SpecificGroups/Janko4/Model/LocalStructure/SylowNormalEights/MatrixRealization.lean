module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Presentation
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.MatrixWords
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.MatrixRealization.Relations
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.MatrixRealization.Generation
import Mathlib.Tactic.FinCases

/-!
# Literal matrix realization of the 21-generator Sylow presentation

The actual matrix words satisfy all 21 square and 210 inverse-conjugation
relations. The eleven kernel generators and four Sylow lifts are ascending
products of these words, so they generate the whole intrinsic two-subgroup.
The parent comparison theorem can therefore construct the actual isomorphism.

The proof composes kernel-checked row products with the faithful original
matrix representation; no external matrix assertion is trusted. Source:
Kleidman--Wilson (1988), pp.484–510, and the literal ATLAS words and discovery
conventions documented in `SylowNormalEights/source/README.md`.
-/

public section
namespace Janko4.LocalStructure.SylowNormalEights.MatrixWords
open MatrixRealization

attribute [local irreducible] modelGroup matrixA matrixB

/-- All published PC relations hold for the fixed literal matrix words. -/
theorem pcGenerator_relations : Presentation.Relations pcGenerator := by
  constructor
  · intro i
    fin_cases i
    · exact square0
    · exact square1
    · exact square2
    · exact square3
    · exact square4
    · exact square5
    · exact square6
    · exact square7
    · exact square8
    · exact square9
    · exact square10
    · exact square11
    · exact square12
    · exact square13
    · exact square14
    · exact square15
    · exact square16
    · exact square17
    · exact square18
    · exact square19
    · exact square20
  · intro i j hij
    fin_cases i
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((0 : Fin 21) < 0)) hij)
      · exact conjugate0_1
      · exact conjugate0_2
      · exact conjugate0_3
      · exact conjugate0_4
      · exact conjugate0_5
      · exact conjugate0_6
      · exact conjugate0_7
      · exact conjugate0_8
      · exact conjugate0_9
      · exact conjugate0_10
      · exact conjugate0_11
      · exact conjugate0_12
      · exact conjugate0_13
      · exact conjugate0_14
      · exact conjugate0_15
      · exact conjugate0_16
      · exact conjugate0_17
      · exact conjugate0_18
      · exact conjugate0_19
      · exact conjugate0_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((1 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((1 : Fin 21) < 1)) hij)
      · exact conjugate1_2
      · exact conjugate1_3
      · exact conjugate1_4
      · exact conjugate1_5
      · exact conjugate1_6
      · exact conjugate1_7
      · exact conjugate1_8
      · exact conjugate1_9
      · exact conjugate1_10
      · exact conjugate1_11
      · exact conjugate1_12
      · exact conjugate1_13
      · exact conjugate1_14
      · exact conjugate1_15
      · exact conjugate1_16
      · exact conjugate1_17
      · exact conjugate1_18
      · exact conjugate1_19
      · exact conjugate1_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((2 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((2 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((2 : Fin 21) < 2)) hij)
      · exact conjugate2_3
      · exact conjugate2_4
      · exact conjugate2_5
      · exact conjugate2_6
      · exact conjugate2_7
      · exact conjugate2_8
      · exact conjugate2_9
      · exact conjugate2_10
      · exact conjugate2_11
      · exact conjugate2_12
      · exact conjugate2_13
      · exact conjugate2_14
      · exact conjugate2_15
      · exact conjugate2_16
      · exact conjugate2_17
      · exact conjugate2_18
      · exact conjugate2_19
      · exact conjugate2_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((3 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((3 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((3 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((3 : Fin 21) < 3)) hij)
      · exact conjugate3_4
      · exact conjugate3_5
      · exact conjugate3_6
      · exact conjugate3_7
      · exact conjugate3_8
      · exact conjugate3_9
      · exact conjugate3_10
      · exact conjugate3_11
      · exact conjugate3_12
      · exact conjugate3_13
      · exact conjugate3_14
      · exact conjugate3_15
      · exact conjugate3_16
      · exact conjugate3_17
      · exact conjugate3_18
      · exact conjugate3_19
      · exact conjugate3_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((4 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((4 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((4 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((4 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((4 : Fin 21) < 4)) hij)
      · exact conjugate4_5
      · exact conjugate4_6
      · exact conjugate4_7
      · exact conjugate4_8
      · exact conjugate4_9
      · exact conjugate4_10
      · exact conjugate4_11
      · exact conjugate4_12
      · exact conjugate4_13
      · exact conjugate4_14
      · exact conjugate4_15
      · exact conjugate4_16
      · exact conjugate4_17
      · exact conjugate4_18
      · exact conjugate4_19
      · exact conjugate4_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((5 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((5 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((5 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((5 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((5 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((5 : Fin 21) < 5)) hij)
      · exact conjugate5_6
      · exact conjugate5_7
      · exact conjugate5_8
      · exact conjugate5_9
      · exact conjugate5_10
      · exact conjugate5_11
      · exact conjugate5_12
      · exact conjugate5_13
      · exact conjugate5_14
      · exact conjugate5_15
      · exact conjugate5_16
      · exact conjugate5_17
      · exact conjugate5_18
      · exact conjugate5_19
      · exact conjugate5_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((6 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((6 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((6 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((6 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((6 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((6 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((6 : Fin 21) < 6)) hij)
      · exact conjugate6_7
      · exact conjugate6_8
      · exact conjugate6_9
      · exact conjugate6_10
      · exact conjugate6_11
      · exact conjugate6_12
      · exact conjugate6_13
      · exact conjugate6_14
      · exact conjugate6_15
      · exact conjugate6_16
      · exact conjugate6_17
      · exact conjugate6_18
      · exact conjugate6_19
      · exact conjugate6_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((7 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((7 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((7 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((7 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((7 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((7 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((7 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((7 : Fin 21) < 7)) hij)
      · exact conjugate7_8
      · exact conjugate7_9
      · exact conjugate7_10
      · exact conjugate7_11
      · exact conjugate7_12
      · exact conjugate7_13
      · exact conjugate7_14
      · exact conjugate7_15
      · exact conjugate7_16
      · exact conjugate7_17
      · exact conjugate7_18
      · exact conjugate7_19
      · exact conjugate7_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((8 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((8 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((8 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((8 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((8 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((8 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((8 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((8 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((8 : Fin 21) < 8)) hij)
      · exact conjugate8_9
      · exact conjugate8_10
      · exact conjugate8_11
      · exact conjugate8_12
      · exact conjugate8_13
      · exact conjugate8_14
      · exact conjugate8_15
      · exact conjugate8_16
      · exact conjugate8_17
      · exact conjugate8_18
      · exact conjugate8_19
      · exact conjugate8_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((9 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((9 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((9 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((9 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((9 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((9 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((9 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((9 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((9 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((9 : Fin 21) < 9)) hij)
      · exact conjugate9_10
      · exact conjugate9_11
      · exact conjugate9_12
      · exact conjugate9_13
      · exact conjugate9_14
      · exact conjugate9_15
      · exact conjugate9_16
      · exact conjugate9_17
      · exact conjugate9_18
      · exact conjugate9_19
      · exact conjugate9_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((10 : Fin 21) < 10)) hij)
      · exact conjugate10_11
      · exact conjugate10_12
      · exact conjugate10_13
      · exact conjugate10_14
      · exact conjugate10_15
      · exact conjugate10_16
      · exact conjugate10_17
      · exact conjugate10_18
      · exact conjugate10_19
      · exact conjugate10_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 10)) hij)
      · exact False.elim ((by decide : ¬ ((11 : Fin 21) < 11)) hij)
      · exact conjugate11_12
      · exact conjugate11_13
      · exact conjugate11_14
      · exact conjugate11_15
      · exact conjugate11_16
      · exact conjugate11_17
      · exact conjugate11_18
      · exact conjugate11_19
      · exact conjugate11_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 10)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 11)) hij)
      · exact False.elim ((by decide : ¬ ((12 : Fin 21) < 12)) hij)
      · exact conjugate12_13
      · exact conjugate12_14
      · exact conjugate12_15
      · exact conjugate12_16
      · exact conjugate12_17
      · exact conjugate12_18
      · exact conjugate12_19
      · exact conjugate12_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 10)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 11)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 12)) hij)
      · exact False.elim ((by decide : ¬ ((13 : Fin 21) < 13)) hij)
      · exact conjugate13_14
      · exact conjugate13_15
      · exact conjugate13_16
      · exact conjugate13_17
      · exact conjugate13_18
      · exact conjugate13_19
      · exact conjugate13_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 10)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 11)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 12)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 13)) hij)
      · exact False.elim ((by decide : ¬ ((14 : Fin 21) < 14)) hij)
      · exact conjugate14_15
      · exact conjugate14_16
      · exact conjugate14_17
      · exact conjugate14_18
      · exact conjugate14_19
      · exact conjugate14_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 10)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 11)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 12)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 13)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 14)) hij)
      · exact False.elim ((by decide : ¬ ((15 : Fin 21) < 15)) hij)
      · exact conjugate15_16
      · exact conjugate15_17
      · exact conjugate15_18
      · exact conjugate15_19
      · exact conjugate15_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 10)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 11)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 12)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 13)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 14)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 15)) hij)
      · exact False.elim ((by decide : ¬ ((16 : Fin 21) < 16)) hij)
      · exact conjugate16_17
      · exact conjugate16_18
      · exact conjugate16_19
      · exact conjugate16_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 10)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 11)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 12)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 13)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 14)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 15)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 16)) hij)
      · exact False.elim ((by decide : ¬ ((17 : Fin 21) < 17)) hij)
      · exact conjugate17_18
      · exact conjugate17_19
      · exact conjugate17_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 10)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 11)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 12)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 13)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 14)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 15)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 16)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 17)) hij)
      · exact False.elim ((by decide : ¬ ((18 : Fin 21) < 18)) hij)
      · exact conjugate18_19
      · exact conjugate18_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 10)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 11)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 12)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 13)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 14)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 15)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 16)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 17)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 18)) hij)
      · exact False.elim ((by decide : ¬ ((19 : Fin 21) < 19)) hij)
      · exact conjugate19_20
    · fin_cases j
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 0)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 1)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 2)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 3)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 4)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 5)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 6)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 7)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 8)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 9)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 10)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 11)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 12)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 13)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 14)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 15)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 16)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 17)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 18)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 19)) hij)
      · exact False.elim ((by decide : ¬ ((20 : Fin 21) < 20)) hij)

private theorem pcWord_mem (w : List (Fin 21)) :
    (w.map pcGenerator).prod ∈ Subgroup.closure (Set.range pcGenerator) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  exact Subgroup.subset_closure (Set.mem_range_self i)

/-- The fixed PC words generate the exact intrinsic matrix two-subgroup. -/
theorem pcGenerator_closure : Subgroup.closure (Set.range pcGenerator) = ⊤ := by
  apply top_unique
  rw [← literalGenerator_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  rcases i with i | i
  · fin_cases i
    · exact literal0_word.symm ▸ pcWord_mem [0, 3, 5, 6, 8, 10, 14, 17, 18, 19, 20]
    · exact literal1_word.symm ▸ pcWord_mem [6, 11, 14, 16, 18, 20]
    · exact literal2_word.symm ▸ pcWord_mem [0, 5, 6, 8, 10, 12, 13, 15, 19, 20]
    · exact literal3_word.symm ▸ pcWord_mem [0, 5, 6, 8, 9, 10, 12, 13, 15, 18, 19]
    · exact literal4_word.symm ▸ pcWord_mem [3, 6, 11, 12, 13, 15, 16, 17, 18, 19, 20]
    · exact literal5_word.symm ▸ pcWord_mem [0, 3, 5, 6, 8, 9, 10, 11, 16, 19, 20]
    · exact literal6_word.symm ▸ pcWord_mem [0, 5, 8, 10, 11, 12, 13, 15, 16, 17, 19]
    · exact literal7_word.symm ▸ pcWord_mem [14, 17, 18, 20]
    · exact literal8_word.symm ▸ pcWord_mem [6, 9, 11, 14, 16, 17, 18, 19]
    · exact literal9_word.symm ▸ pcWord_mem [0, 3, 5, 6, 8, 10, 16, 17, 19, 20]
    · exact literal10_word.symm ▸ pcWord_mem [6, 9, 14, 17, 18, 20]
  · fin_cases i
    · exact literal11_word.symm ▸ pcWord_mem [3, 7, 9, 13, 15, 17]
    · exact literal12_word.symm ▸ pcWord_mem [1, 6, 14, 16]
    · exact literal13_word.symm ▸ pcWord_mem [0, 6]
    · exact literal14_word.symm ▸ pcWord_mem [2]

end Janko4.LocalStructure.SylowNormalEights.MatrixWords
