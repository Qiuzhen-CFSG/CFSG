module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.Packing
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.Tables
import Mathlib.Tactic.FinCases

/-!
# The fixed packed rows are the actual exterior-square matrices

The four bit-expansion arrays are checked against the structural triangular
packing functions. Each upper-index row family then checks the two binary
minors. The final matrix equalities use `pair_index`, so the row and column
markings are exactly those of Ambient. No basis alignment is assumed.

Source: R. A. Wilson et al., ATLAS HSG1-f2r56B0/HSG1-f2r1000B0;
`Binary/source/README.md` and the fixed `section1000.json`. Generated numerical
obligations are kernel-checked. Original code under Apache 2.0.
-/

@[expose] public section


namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining

open Thompson.BinaryMatrix

private theorem aHigh_0 : Tables.aHigh[0]! = highBits D56.aRows[0]! := by decide +kernel

private theorem aHigh_1 : Tables.aHigh[1]! = highBits D56.aRows[1]! := by decide +kernel

private theorem aHigh_2 : Tables.aHigh[2]! = highBits D56.aRows[2]! := by decide +kernel

private theorem aHigh_3 : Tables.aHigh[3]! = highBits D56.aRows[3]! := by decide +kernel

private theorem aHigh_4 : Tables.aHigh[4]! = highBits D56.aRows[4]! := by decide +kernel

private theorem aHigh_5 : Tables.aHigh[5]! = highBits D56.aRows[5]! := by decide +kernel

private theorem aHigh_6 : Tables.aHigh[6]! = highBits D56.aRows[6]! := by decide +kernel

private theorem aHigh_7 : Tables.aHigh[7]! = highBits D56.aRows[7]! := by decide +kernel

private theorem aHigh_8 : Tables.aHigh[8]! = highBits D56.aRows[8]! := by decide +kernel

private theorem aHigh_9 : Tables.aHigh[9]! = highBits D56.aRows[9]! := by decide +kernel

private theorem aHigh_10 : Tables.aHigh[10]! = highBits D56.aRows[10]! := by decide +kernel

private theorem aHigh_11 : Tables.aHigh[11]! = highBits D56.aRows[11]! := by decide +kernel

private theorem aHigh_12 : Tables.aHigh[12]! = highBits D56.aRows[12]! := by decide +kernel

private theorem aHigh_13 : Tables.aHigh[13]! = highBits D56.aRows[13]! := by decide +kernel

private theorem aHigh_14 : Tables.aHigh[14]! = highBits D56.aRows[14]! := by decide +kernel

private theorem aHigh_15 : Tables.aHigh[15]! = highBits D56.aRows[15]! := by decide +kernel

private theorem aHigh_16 : Tables.aHigh[16]! = highBits D56.aRows[16]! := by decide +kernel

private theorem aHigh_17 : Tables.aHigh[17]! = highBits D56.aRows[17]! := by decide +kernel

private theorem aHigh_18 : Tables.aHigh[18]! = highBits D56.aRows[18]! := by decide +kernel

private theorem aHigh_19 : Tables.aHigh[19]! = highBits D56.aRows[19]! := by decide +kernel

private theorem aHigh_20 : Tables.aHigh[20]! = highBits D56.aRows[20]! := by decide +kernel

private theorem aHigh_21 : Tables.aHigh[21]! = highBits D56.aRows[21]! := by decide +kernel

private theorem aHigh_22 : Tables.aHigh[22]! = highBits D56.aRows[22]! := by decide +kernel

private theorem aHigh_23 : Tables.aHigh[23]! = highBits D56.aRows[23]! := by decide +kernel

private theorem aHigh_24 : Tables.aHigh[24]! = highBits D56.aRows[24]! := by decide +kernel

private theorem aHigh_25 : Tables.aHigh[25]! = highBits D56.aRows[25]! := by decide +kernel

private theorem aHigh_26 : Tables.aHigh[26]! = highBits D56.aRows[26]! := by decide +kernel

private theorem aHigh_27 : Tables.aHigh[27]! = highBits D56.aRows[27]! := by decide +kernel

private theorem aHigh_28 : Tables.aHigh[28]! = highBits D56.aRows[28]! := by decide +kernel

private theorem aHigh_29 : Tables.aHigh[29]! = highBits D56.aRows[29]! := by decide +kernel

private theorem aHigh_30 : Tables.aHigh[30]! = highBits D56.aRows[30]! := by decide +kernel

private theorem aHigh_31 : Tables.aHigh[31]! = highBits D56.aRows[31]! := by decide +kernel

private theorem aHigh_32 : Tables.aHigh[32]! = highBits D56.aRows[32]! := by decide +kernel

private theorem aHigh_33 : Tables.aHigh[33]! = highBits D56.aRows[33]! := by decide +kernel

private theorem aHigh_34 : Tables.aHigh[34]! = highBits D56.aRows[34]! := by decide +kernel

private theorem aHigh_35 : Tables.aHigh[35]! = highBits D56.aRows[35]! := by decide +kernel

private theorem aHigh_36 : Tables.aHigh[36]! = highBits D56.aRows[36]! := by decide +kernel

private theorem aHigh_37 : Tables.aHigh[37]! = highBits D56.aRows[37]! := by decide +kernel

private theorem aHigh_38 : Tables.aHigh[38]! = highBits D56.aRows[38]! := by decide +kernel

private theorem aHigh_39 : Tables.aHigh[39]! = highBits D56.aRows[39]! := by decide +kernel

private theorem aHigh_40 : Tables.aHigh[40]! = highBits D56.aRows[40]! := by decide +kernel

private theorem aHigh_41 : Tables.aHigh[41]! = highBits D56.aRows[41]! := by decide +kernel

private theorem aHigh_42 : Tables.aHigh[42]! = highBits D56.aRows[42]! := by decide +kernel

private theorem aHigh_43 : Tables.aHigh[43]! = highBits D56.aRows[43]! := by decide +kernel

private theorem aHigh_44 : Tables.aHigh[44]! = highBits D56.aRows[44]! := by decide +kernel

private theorem aHigh_45 : Tables.aHigh[45]! = highBits D56.aRows[45]! := by decide +kernel

private theorem aHigh_46 : Tables.aHigh[46]! = highBits D56.aRows[46]! := by decide +kernel

private theorem aHigh_47 : Tables.aHigh[47]! = highBits D56.aRows[47]! := by decide +kernel

private theorem aHigh_48 : Tables.aHigh[48]! = highBits D56.aRows[48]! := by decide +kernel

private theorem aHigh_49 : Tables.aHigh[49]! = highBits D56.aRows[49]! := by decide +kernel

private theorem aHigh_50 : Tables.aHigh[50]! = highBits D56.aRows[50]! := by decide +kernel

private theorem aHigh_51 : Tables.aHigh[51]! = highBits D56.aRows[51]! := by decide +kernel

private theorem aHigh_52 : Tables.aHigh[52]! = highBits D56.aRows[52]! := by decide +kernel

private theorem aHigh_53 : Tables.aHigh[53]! = highBits D56.aRows[53]! := by decide +kernel

private theorem aHigh_54 : Tables.aHigh[54]! = highBits D56.aRows[54]! := by decide +kernel

private theorem aHigh_55 : Tables.aHigh[55]! = highBits D56.aRows[55]! := by decide +kernel

theorem aHigh_checked (i : Fin 56) : Tables.aHigh[i.val]! = highBits D56.aRows[i.val]! := by
  fin_cases i

  · exact aHigh_0

  · exact aHigh_1

  · exact aHigh_2

  · exact aHigh_3

  · exact aHigh_4

  · exact aHigh_5

  · exact aHigh_6

  · exact aHigh_7

  · exact aHigh_8

  · exact aHigh_9

  · exact aHigh_10

  · exact aHigh_11

  · exact aHigh_12

  · exact aHigh_13

  · exact aHigh_14

  · exact aHigh_15

  · exact aHigh_16

  · exact aHigh_17

  · exact aHigh_18

  · exact aHigh_19

  · exact aHigh_20

  · exact aHigh_21

  · exact aHigh_22

  · exact aHigh_23

  · exact aHigh_24

  · exact aHigh_25

  · exact aHigh_26

  · exact aHigh_27

  · exact aHigh_28

  · exact aHigh_29

  · exact aHigh_30

  · exact aHigh_31

  · exact aHigh_32

  · exact aHigh_33

  · exact aHigh_34

  · exact aHigh_35

  · exact aHigh_36

  · exact aHigh_37

  · exact aHigh_38

  · exact aHigh_39

  · exact aHigh_40

  · exact aHigh_41

  · exact aHigh_42

  · exact aHigh_43

  · exact aHigh_44

  · exact aHigh_45

  · exact aHigh_46

  · exact aHigh_47

  · exact aHigh_48

  · exact aHigh_49

  · exact aHigh_50

  · exact aHigh_51

  · exact aHigh_52

  · exact aHigh_53

  · exact aHigh_54

  · exact aHigh_55

private theorem aLow_0 : Tables.aLow[0]! = lowBits D56.aRows[0]! := by decide +kernel

private theorem aLow_1 : Tables.aLow[1]! = lowBits D56.aRows[1]! := by decide +kernel

private theorem aLow_2 : Tables.aLow[2]! = lowBits D56.aRows[2]! := by decide +kernel

private theorem aLow_3 : Tables.aLow[3]! = lowBits D56.aRows[3]! := by decide +kernel

private theorem aLow_4 : Tables.aLow[4]! = lowBits D56.aRows[4]! := by decide +kernel

private theorem aLow_5 : Tables.aLow[5]! = lowBits D56.aRows[5]! := by decide +kernel

private theorem aLow_6 : Tables.aLow[6]! = lowBits D56.aRows[6]! := by decide +kernel

private theorem aLow_7 : Tables.aLow[7]! = lowBits D56.aRows[7]! := by decide +kernel

private theorem aLow_8 : Tables.aLow[8]! = lowBits D56.aRows[8]! := by decide +kernel

private theorem aLow_9 : Tables.aLow[9]! = lowBits D56.aRows[9]! := by decide +kernel

private theorem aLow_10 : Tables.aLow[10]! = lowBits D56.aRows[10]! := by decide +kernel

private theorem aLow_11 : Tables.aLow[11]! = lowBits D56.aRows[11]! := by decide +kernel

private theorem aLow_12 : Tables.aLow[12]! = lowBits D56.aRows[12]! := by decide +kernel

private theorem aLow_13 : Tables.aLow[13]! = lowBits D56.aRows[13]! := by decide +kernel

private theorem aLow_14 : Tables.aLow[14]! = lowBits D56.aRows[14]! := by decide +kernel

private theorem aLow_15 : Tables.aLow[15]! = lowBits D56.aRows[15]! := by decide +kernel

private theorem aLow_16 : Tables.aLow[16]! = lowBits D56.aRows[16]! := by decide +kernel

private theorem aLow_17 : Tables.aLow[17]! = lowBits D56.aRows[17]! := by decide +kernel

private theorem aLow_18 : Tables.aLow[18]! = lowBits D56.aRows[18]! := by decide +kernel

private theorem aLow_19 : Tables.aLow[19]! = lowBits D56.aRows[19]! := by decide +kernel

private theorem aLow_20 : Tables.aLow[20]! = lowBits D56.aRows[20]! := by decide +kernel

private theorem aLow_21 : Tables.aLow[21]! = lowBits D56.aRows[21]! := by decide +kernel

private theorem aLow_22 : Tables.aLow[22]! = lowBits D56.aRows[22]! := by decide +kernel

private theorem aLow_23 : Tables.aLow[23]! = lowBits D56.aRows[23]! := by decide +kernel

private theorem aLow_24 : Tables.aLow[24]! = lowBits D56.aRows[24]! := by decide +kernel

private theorem aLow_25 : Tables.aLow[25]! = lowBits D56.aRows[25]! := by decide +kernel

private theorem aLow_26 : Tables.aLow[26]! = lowBits D56.aRows[26]! := by decide +kernel

private theorem aLow_27 : Tables.aLow[27]! = lowBits D56.aRows[27]! := by decide +kernel

private theorem aLow_28 : Tables.aLow[28]! = lowBits D56.aRows[28]! := by decide +kernel

private theorem aLow_29 : Tables.aLow[29]! = lowBits D56.aRows[29]! := by decide +kernel

private theorem aLow_30 : Tables.aLow[30]! = lowBits D56.aRows[30]! := by decide +kernel

private theorem aLow_31 : Tables.aLow[31]! = lowBits D56.aRows[31]! := by decide +kernel

private theorem aLow_32 : Tables.aLow[32]! = lowBits D56.aRows[32]! := by decide +kernel

private theorem aLow_33 : Tables.aLow[33]! = lowBits D56.aRows[33]! := by decide +kernel

private theorem aLow_34 : Tables.aLow[34]! = lowBits D56.aRows[34]! := by decide +kernel

private theorem aLow_35 : Tables.aLow[35]! = lowBits D56.aRows[35]! := by decide +kernel

private theorem aLow_36 : Tables.aLow[36]! = lowBits D56.aRows[36]! := by decide +kernel

private theorem aLow_37 : Tables.aLow[37]! = lowBits D56.aRows[37]! := by decide +kernel

private theorem aLow_38 : Tables.aLow[38]! = lowBits D56.aRows[38]! := by decide +kernel

private theorem aLow_39 : Tables.aLow[39]! = lowBits D56.aRows[39]! := by decide +kernel

private theorem aLow_40 : Tables.aLow[40]! = lowBits D56.aRows[40]! := by decide +kernel

private theorem aLow_41 : Tables.aLow[41]! = lowBits D56.aRows[41]! := by decide +kernel

private theorem aLow_42 : Tables.aLow[42]! = lowBits D56.aRows[42]! := by decide +kernel

private theorem aLow_43 : Tables.aLow[43]! = lowBits D56.aRows[43]! := by decide +kernel

private theorem aLow_44 : Tables.aLow[44]! = lowBits D56.aRows[44]! := by decide +kernel

private theorem aLow_45 : Tables.aLow[45]! = lowBits D56.aRows[45]! := by decide +kernel

private theorem aLow_46 : Tables.aLow[46]! = lowBits D56.aRows[46]! := by decide +kernel

private theorem aLow_47 : Tables.aLow[47]! = lowBits D56.aRows[47]! := by decide +kernel

private theorem aLow_48 : Tables.aLow[48]! = lowBits D56.aRows[48]! := by decide +kernel

private theorem aLow_49 : Tables.aLow[49]! = lowBits D56.aRows[49]! := by decide +kernel

private theorem aLow_50 : Tables.aLow[50]! = lowBits D56.aRows[50]! := by decide +kernel

private theorem aLow_51 : Tables.aLow[51]! = lowBits D56.aRows[51]! := by decide +kernel

private theorem aLow_52 : Tables.aLow[52]! = lowBits D56.aRows[52]! := by decide +kernel

private theorem aLow_53 : Tables.aLow[53]! = lowBits D56.aRows[53]! := by decide +kernel

private theorem aLow_54 : Tables.aLow[54]! = lowBits D56.aRows[54]! := by decide +kernel

private theorem aLow_55 : Tables.aLow[55]! = lowBits D56.aRows[55]! := by decide +kernel

theorem aLow_checked (i : Fin 56) : Tables.aLow[i.val]! = lowBits D56.aRows[i.val]! := by
  fin_cases i

  · exact aLow_0

  · exact aLow_1

  · exact aLow_2

  · exact aLow_3

  · exact aLow_4

  · exact aLow_5

  · exact aLow_6

  · exact aLow_7

  · exact aLow_8

  · exact aLow_9

  · exact aLow_10

  · exact aLow_11

  · exact aLow_12

  · exact aLow_13

  · exact aLow_14

  · exact aLow_15

  · exact aLow_16

  · exact aLow_17

  · exact aLow_18

  · exact aLow_19

  · exact aLow_20

  · exact aLow_21

  · exact aLow_22

  · exact aLow_23

  · exact aLow_24

  · exact aLow_25

  · exact aLow_26

  · exact aLow_27

  · exact aLow_28

  · exact aLow_29

  · exact aLow_30

  · exact aLow_31

  · exact aLow_32

  · exact aLow_33

  · exact aLow_34

  · exact aLow_35

  · exact aLow_36

  · exact aLow_37

  · exact aLow_38

  · exact aLow_39

  · exact aLow_40

  · exact aLow_41

  · exact aLow_42

  · exact aLow_43

  · exact aLow_44

  · exact aLow_45

  · exact aLow_46

  · exact aLow_47

  · exact aLow_48

  · exact aLow_49

  · exact aLow_50

  · exact aLow_51

  · exact aLow_52

  · exact aLow_53

  · exact aLow_54

  · exact aLow_55

private theorem a_row0 : ∀ k : Fin 0,
    Tables.a.get (triangular 0 + k.val) =
      (Tables.aHigh[0]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[0]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row1 : ∀ k : Fin 1,
    Tables.a.get (triangular 1 + k.val) =
      (Tables.aHigh[1]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[1]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row2 : ∀ k : Fin 2,
    Tables.a.get (triangular 2 + k.val) =
      (Tables.aHigh[2]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[2]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row3 : ∀ k : Fin 3,
    Tables.a.get (triangular 3 + k.val) =
      (Tables.aHigh[3]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[3]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row4 : ∀ k : Fin 4,
    Tables.a.get (triangular 4 + k.val) =
      (Tables.aHigh[4]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[4]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row5 : ∀ k : Fin 5,
    Tables.a.get (triangular 5 + k.val) =
      (Tables.aHigh[5]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[5]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row6 : ∀ k : Fin 6,
    Tables.a.get (triangular 6 + k.val) =
      (Tables.aHigh[6]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[6]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row7 : ∀ k : Fin 7,
    Tables.a.get (triangular 7 + k.val) =
      (Tables.aHigh[7]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[7]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row8 : ∀ k : Fin 8,
    Tables.a.get (triangular 8 + k.val) =
      (Tables.aHigh[8]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[8]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row9 : ∀ k : Fin 9,
    Tables.a.get (triangular 9 + k.val) =
      (Tables.aHigh[9]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[9]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row10 : ∀ k : Fin 10,
    Tables.a.get (triangular 10 + k.val) =
      (Tables.aHigh[10]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[10]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row11 : ∀ k : Fin 11,
    Tables.a.get (triangular 11 + k.val) =
      (Tables.aHigh[11]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[11]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row12 : ∀ k : Fin 12,
    Tables.a.get (triangular 12 + k.val) =
      (Tables.aHigh[12]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[12]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row13 : ∀ k : Fin 13,
    Tables.a.get (triangular 13 + k.val) =
      (Tables.aHigh[13]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[13]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row14 : ∀ k : Fin 14,
    Tables.a.get (triangular 14 + k.val) =
      (Tables.aHigh[14]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[14]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row15 : ∀ k : Fin 15,
    Tables.a.get (triangular 15 + k.val) =
      (Tables.aHigh[15]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[15]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row16 : ∀ k : Fin 16,
    Tables.a.get (triangular 16 + k.val) =
      (Tables.aHigh[16]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[16]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row17 : ∀ k : Fin 17,
    Tables.a.get (triangular 17 + k.val) =
      (Tables.aHigh[17]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[17]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row18 : ∀ k : Fin 18,
    Tables.a.get (triangular 18 + k.val) =
      (Tables.aHigh[18]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[18]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row19 : ∀ k : Fin 19,
    Tables.a.get (triangular 19 + k.val) =
      (Tables.aHigh[19]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[19]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row20 : ∀ k : Fin 20,
    Tables.a.get (triangular 20 + k.val) =
      (Tables.aHigh[20]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[20]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row21 : ∀ k : Fin 21,
    Tables.a.get (triangular 21 + k.val) =
      (Tables.aHigh[21]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[21]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row22 : ∀ k : Fin 22,
    Tables.a.get (triangular 22 + k.val) =
      (Tables.aHigh[22]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[22]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row23 : ∀ k : Fin 23,
    Tables.a.get (triangular 23 + k.val) =
      (Tables.aHigh[23]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[23]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row24 : ∀ k : Fin 24,
    Tables.a.get (triangular 24 + k.val) =
      (Tables.aHigh[24]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[24]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row25 : ∀ k : Fin 25,
    Tables.a.get (triangular 25 + k.val) =
      (Tables.aHigh[25]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[25]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row26 : ∀ k : Fin 26,
    Tables.a.get (triangular 26 + k.val) =
      (Tables.aHigh[26]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[26]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row27 : ∀ k : Fin 27,
    Tables.a.get (triangular 27 + k.val) =
      (Tables.aHigh[27]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[27]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row28 : ∀ k : Fin 28,
    Tables.a.get (triangular 28 + k.val) =
      (Tables.aHigh[28]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[28]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row29 : ∀ k : Fin 29,
    Tables.a.get (triangular 29 + k.val) =
      (Tables.aHigh[29]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[29]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row30 : ∀ k : Fin 30,
    Tables.a.get (triangular 30 + k.val) =
      (Tables.aHigh[30]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[30]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row31 : ∀ k : Fin 31,
    Tables.a.get (triangular 31 + k.val) =
      (Tables.aHigh[31]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[31]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row32 : ∀ k : Fin 32,
    Tables.a.get (triangular 32 + k.val) =
      (Tables.aHigh[32]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[32]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row33 : ∀ k : Fin 33,
    Tables.a.get (triangular 33 + k.val) =
      (Tables.aHigh[33]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[33]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row34 : ∀ k : Fin 34,
    Tables.a.get (triangular 34 + k.val) =
      (Tables.aHigh[34]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[34]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row35 : ∀ k : Fin 35,
    Tables.a.get (triangular 35 + k.val) =
      (Tables.aHigh[35]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[35]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row36 : ∀ k : Fin 36,
    Tables.a.get (triangular 36 + k.val) =
      (Tables.aHigh[36]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[36]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row37 : ∀ k : Fin 37,
    Tables.a.get (triangular 37 + k.val) =
      (Tables.aHigh[37]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[37]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row38 : ∀ k : Fin 38,
    Tables.a.get (triangular 38 + k.val) =
      (Tables.aHigh[38]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[38]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row39 : ∀ k : Fin 39,
    Tables.a.get (triangular 39 + k.val) =
      (Tables.aHigh[39]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[39]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row40 : ∀ k : Fin 40,
    Tables.a.get (triangular 40 + k.val) =
      (Tables.aHigh[40]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[40]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row41 : ∀ k : Fin 41,
    Tables.a.get (triangular 41 + k.val) =
      (Tables.aHigh[41]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[41]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row42 : ∀ k : Fin 42,
    Tables.a.get (triangular 42 + k.val) =
      (Tables.aHigh[42]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[42]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row43 : ∀ k : Fin 43,
    Tables.a.get (triangular 43 + k.val) =
      (Tables.aHigh[43]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[43]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row44 : ∀ k : Fin 44,
    Tables.a.get (triangular 44 + k.val) =
      (Tables.aHigh[44]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[44]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row45 : ∀ k : Fin 45,
    Tables.a.get (triangular 45 + k.val) =
      (Tables.aHigh[45]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[45]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row46 : ∀ k : Fin 46,
    Tables.a.get (triangular 46 + k.val) =
      (Tables.aHigh[46]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[46]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row47 : ∀ k : Fin 47,
    Tables.a.get (triangular 47 + k.val) =
      (Tables.aHigh[47]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[47]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row48 : ∀ k : Fin 48,
    Tables.a.get (triangular 48 + k.val) =
      (Tables.aHigh[48]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[48]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row49 : ∀ k : Fin 49,
    Tables.a.get (triangular 49 + k.val) =
      (Tables.aHigh[49]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[49]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row50 : ∀ k : Fin 50,
    Tables.a.get (triangular 50 + k.val) =
      (Tables.aHigh[50]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[50]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row51 : ∀ k : Fin 51,
    Tables.a.get (triangular 51 + k.val) =
      (Tables.aHigh[51]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[51]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row52 : ∀ k : Fin 52,
    Tables.a.get (triangular 52 + k.val) =
      (Tables.aHigh[52]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[52]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row53 : ∀ k : Fin 53,
    Tables.a.get (triangular 53 + k.val) =
      (Tables.aHigh[53]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[53]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row54 : ∀ k : Fin 54,
    Tables.a.get (triangular 54 + k.val) =
      (Tables.aHigh[54]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[54]! &&& Tables.aHigh[k.val]!) := by decide +kernel

private theorem a_row55 : ∀ k : Fin 55,
    Tables.a.get (triangular 55 + k.val) =
      (Tables.aHigh[55]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[55]! &&& Tables.aHigh[k.val]!) := by decide +kernel

theorem a_rows_checked (j : Fin 56) (k : Fin j.val) :
    Tables.a.get (triangular j.val + k.val) =
      (Tables.aHigh[j.val]! &&& Tables.aLow[k.val]!) ^^^
      (Tables.aLow[j.val]! &&& Tables.aHigh[k.val]!) := by
  fin_cases j

  · exact a_row0 k

  · exact a_row1 k

  · exact a_row2 k

  · exact a_row3 k

  · exact a_row4 k

  · exact a_row5 k

  · exact a_row6 k

  · exact a_row7 k

  · exact a_row8 k

  · exact a_row9 k

  · exact a_row10 k

  · exact a_row11 k

  · exact a_row12 k

  · exact a_row13 k

  · exact a_row14 k

  · exact a_row15 k

  · exact a_row16 k

  · exact a_row17 k

  · exact a_row18 k

  · exact a_row19 k

  · exact a_row20 k

  · exact a_row21 k

  · exact a_row22 k

  · exact a_row23 k

  · exact a_row24 k

  · exact a_row25 k

  · exact a_row26 k

  · exact a_row27 k

  · exact a_row28 k

  · exact a_row29 k

  · exact a_row30 k

  · exact a_row31 k

  · exact a_row32 k

  · exact a_row33 k

  · exact a_row34 k

  · exact a_row35 k

  · exact a_row36 k

  · exact a_row37 k

  · exact a_row38 k

  · exact a_row39 k

  · exact a_row40 k

  · exact a_row41 k

  · exact a_row42 k

  · exact a_row43 k

  · exact a_row44 k

  · exact a_row45 k

  · exact a_row46 k

  · exact a_row47 k

  · exact a_row48 k

  · exact a_row49 k

  · exact a_row50 k

  · exact a_row51 k

  · exact a_row52 k

  · exact a_row53 k

  · exact a_row54 k

  · exact a_row55 k

private theorem bHigh_0 : Tables.bHigh[0]! = highBits D56.bRows[0]! := by decide +kernel

private theorem bHigh_1 : Tables.bHigh[1]! = highBits D56.bRows[1]! := by decide +kernel

private theorem bHigh_2 : Tables.bHigh[2]! = highBits D56.bRows[2]! := by decide +kernel

private theorem bHigh_3 : Tables.bHigh[3]! = highBits D56.bRows[3]! := by decide +kernel

private theorem bHigh_4 : Tables.bHigh[4]! = highBits D56.bRows[4]! := by decide +kernel

private theorem bHigh_5 : Tables.bHigh[5]! = highBits D56.bRows[5]! := by decide +kernel

private theorem bHigh_6 : Tables.bHigh[6]! = highBits D56.bRows[6]! := by decide +kernel

private theorem bHigh_7 : Tables.bHigh[7]! = highBits D56.bRows[7]! := by decide +kernel

private theorem bHigh_8 : Tables.bHigh[8]! = highBits D56.bRows[8]! := by decide +kernel

private theorem bHigh_9 : Tables.bHigh[9]! = highBits D56.bRows[9]! := by decide +kernel

private theorem bHigh_10 : Tables.bHigh[10]! = highBits D56.bRows[10]! := by decide +kernel

private theorem bHigh_11 : Tables.bHigh[11]! = highBits D56.bRows[11]! := by decide +kernel

private theorem bHigh_12 : Tables.bHigh[12]! = highBits D56.bRows[12]! := by decide +kernel

private theorem bHigh_13 : Tables.bHigh[13]! = highBits D56.bRows[13]! := by decide +kernel

private theorem bHigh_14 : Tables.bHigh[14]! = highBits D56.bRows[14]! := by decide +kernel

private theorem bHigh_15 : Tables.bHigh[15]! = highBits D56.bRows[15]! := by decide +kernel

private theorem bHigh_16 : Tables.bHigh[16]! = highBits D56.bRows[16]! := by decide +kernel

private theorem bHigh_17 : Tables.bHigh[17]! = highBits D56.bRows[17]! := by decide +kernel

private theorem bHigh_18 : Tables.bHigh[18]! = highBits D56.bRows[18]! := by decide +kernel

private theorem bHigh_19 : Tables.bHigh[19]! = highBits D56.bRows[19]! := by decide +kernel

private theorem bHigh_20 : Tables.bHigh[20]! = highBits D56.bRows[20]! := by decide +kernel

private theorem bHigh_21 : Tables.bHigh[21]! = highBits D56.bRows[21]! := by decide +kernel

private theorem bHigh_22 : Tables.bHigh[22]! = highBits D56.bRows[22]! := by decide +kernel

private theorem bHigh_23 : Tables.bHigh[23]! = highBits D56.bRows[23]! := by decide +kernel

private theorem bHigh_24 : Tables.bHigh[24]! = highBits D56.bRows[24]! := by decide +kernel

private theorem bHigh_25 : Tables.bHigh[25]! = highBits D56.bRows[25]! := by decide +kernel

private theorem bHigh_26 : Tables.bHigh[26]! = highBits D56.bRows[26]! := by decide +kernel

private theorem bHigh_27 : Tables.bHigh[27]! = highBits D56.bRows[27]! := by decide +kernel

private theorem bHigh_28 : Tables.bHigh[28]! = highBits D56.bRows[28]! := by decide +kernel

private theorem bHigh_29 : Tables.bHigh[29]! = highBits D56.bRows[29]! := by decide +kernel

private theorem bHigh_30 : Tables.bHigh[30]! = highBits D56.bRows[30]! := by decide +kernel

private theorem bHigh_31 : Tables.bHigh[31]! = highBits D56.bRows[31]! := by decide +kernel

private theorem bHigh_32 : Tables.bHigh[32]! = highBits D56.bRows[32]! := by decide +kernel

private theorem bHigh_33 : Tables.bHigh[33]! = highBits D56.bRows[33]! := by decide +kernel

private theorem bHigh_34 : Tables.bHigh[34]! = highBits D56.bRows[34]! := by decide +kernel

private theorem bHigh_35 : Tables.bHigh[35]! = highBits D56.bRows[35]! := by decide +kernel

private theorem bHigh_36 : Tables.bHigh[36]! = highBits D56.bRows[36]! := by decide +kernel

private theorem bHigh_37 : Tables.bHigh[37]! = highBits D56.bRows[37]! := by decide +kernel

private theorem bHigh_38 : Tables.bHigh[38]! = highBits D56.bRows[38]! := by decide +kernel

private theorem bHigh_39 : Tables.bHigh[39]! = highBits D56.bRows[39]! := by decide +kernel

private theorem bHigh_40 : Tables.bHigh[40]! = highBits D56.bRows[40]! := by decide +kernel

private theorem bHigh_41 : Tables.bHigh[41]! = highBits D56.bRows[41]! := by decide +kernel

private theorem bHigh_42 : Tables.bHigh[42]! = highBits D56.bRows[42]! := by decide +kernel

private theorem bHigh_43 : Tables.bHigh[43]! = highBits D56.bRows[43]! := by decide +kernel

private theorem bHigh_44 : Tables.bHigh[44]! = highBits D56.bRows[44]! := by decide +kernel

private theorem bHigh_45 : Tables.bHigh[45]! = highBits D56.bRows[45]! := by decide +kernel

private theorem bHigh_46 : Tables.bHigh[46]! = highBits D56.bRows[46]! := by decide +kernel

private theorem bHigh_47 : Tables.bHigh[47]! = highBits D56.bRows[47]! := by decide +kernel

private theorem bHigh_48 : Tables.bHigh[48]! = highBits D56.bRows[48]! := by decide +kernel

private theorem bHigh_49 : Tables.bHigh[49]! = highBits D56.bRows[49]! := by decide +kernel

private theorem bHigh_50 : Tables.bHigh[50]! = highBits D56.bRows[50]! := by decide +kernel

private theorem bHigh_51 : Tables.bHigh[51]! = highBits D56.bRows[51]! := by decide +kernel

private theorem bHigh_52 : Tables.bHigh[52]! = highBits D56.bRows[52]! := by decide +kernel

private theorem bHigh_53 : Tables.bHigh[53]! = highBits D56.bRows[53]! := by decide +kernel

private theorem bHigh_54 : Tables.bHigh[54]! = highBits D56.bRows[54]! := by decide +kernel

private theorem bHigh_55 : Tables.bHigh[55]! = highBits D56.bRows[55]! := by decide +kernel

theorem bHigh_checked (i : Fin 56) : Tables.bHigh[i.val]! = highBits D56.bRows[i.val]! := by
  fin_cases i

  · exact bHigh_0

  · exact bHigh_1

  · exact bHigh_2

  · exact bHigh_3

  · exact bHigh_4

  · exact bHigh_5

  · exact bHigh_6

  · exact bHigh_7

  · exact bHigh_8

  · exact bHigh_9

  · exact bHigh_10

  · exact bHigh_11

  · exact bHigh_12

  · exact bHigh_13

  · exact bHigh_14

  · exact bHigh_15

  · exact bHigh_16

  · exact bHigh_17

  · exact bHigh_18

  · exact bHigh_19

  · exact bHigh_20

  · exact bHigh_21

  · exact bHigh_22

  · exact bHigh_23

  · exact bHigh_24

  · exact bHigh_25

  · exact bHigh_26

  · exact bHigh_27

  · exact bHigh_28

  · exact bHigh_29

  · exact bHigh_30

  · exact bHigh_31

  · exact bHigh_32

  · exact bHigh_33

  · exact bHigh_34

  · exact bHigh_35

  · exact bHigh_36

  · exact bHigh_37

  · exact bHigh_38

  · exact bHigh_39

  · exact bHigh_40

  · exact bHigh_41

  · exact bHigh_42

  · exact bHigh_43

  · exact bHigh_44

  · exact bHigh_45

  · exact bHigh_46

  · exact bHigh_47

  · exact bHigh_48

  · exact bHigh_49

  · exact bHigh_50

  · exact bHigh_51

  · exact bHigh_52

  · exact bHigh_53

  · exact bHigh_54

  · exact bHigh_55

private theorem bLow_0 : Tables.bLow[0]! = lowBits D56.bRows[0]! := by decide +kernel

private theorem bLow_1 : Tables.bLow[1]! = lowBits D56.bRows[1]! := by decide +kernel

private theorem bLow_2 : Tables.bLow[2]! = lowBits D56.bRows[2]! := by decide +kernel

private theorem bLow_3 : Tables.bLow[3]! = lowBits D56.bRows[3]! := by decide +kernel

private theorem bLow_4 : Tables.bLow[4]! = lowBits D56.bRows[4]! := by decide +kernel

private theorem bLow_5 : Tables.bLow[5]! = lowBits D56.bRows[5]! := by decide +kernel

private theorem bLow_6 : Tables.bLow[6]! = lowBits D56.bRows[6]! := by decide +kernel

private theorem bLow_7 : Tables.bLow[7]! = lowBits D56.bRows[7]! := by decide +kernel

private theorem bLow_8 : Tables.bLow[8]! = lowBits D56.bRows[8]! := by decide +kernel

private theorem bLow_9 : Tables.bLow[9]! = lowBits D56.bRows[9]! := by decide +kernel

private theorem bLow_10 : Tables.bLow[10]! = lowBits D56.bRows[10]! := by decide +kernel

private theorem bLow_11 : Tables.bLow[11]! = lowBits D56.bRows[11]! := by decide +kernel

private theorem bLow_12 : Tables.bLow[12]! = lowBits D56.bRows[12]! := by decide +kernel

private theorem bLow_13 : Tables.bLow[13]! = lowBits D56.bRows[13]! := by decide +kernel

private theorem bLow_14 : Tables.bLow[14]! = lowBits D56.bRows[14]! := by decide +kernel

private theorem bLow_15 : Tables.bLow[15]! = lowBits D56.bRows[15]! := by decide +kernel

private theorem bLow_16 : Tables.bLow[16]! = lowBits D56.bRows[16]! := by decide +kernel

private theorem bLow_17 : Tables.bLow[17]! = lowBits D56.bRows[17]! := by decide +kernel

private theorem bLow_18 : Tables.bLow[18]! = lowBits D56.bRows[18]! := by decide +kernel

private theorem bLow_19 : Tables.bLow[19]! = lowBits D56.bRows[19]! := by decide +kernel

private theorem bLow_20 : Tables.bLow[20]! = lowBits D56.bRows[20]! := by decide +kernel

private theorem bLow_21 : Tables.bLow[21]! = lowBits D56.bRows[21]! := by decide +kernel

private theorem bLow_22 : Tables.bLow[22]! = lowBits D56.bRows[22]! := by decide +kernel

private theorem bLow_23 : Tables.bLow[23]! = lowBits D56.bRows[23]! := by decide +kernel

private theorem bLow_24 : Tables.bLow[24]! = lowBits D56.bRows[24]! := by decide +kernel

private theorem bLow_25 : Tables.bLow[25]! = lowBits D56.bRows[25]! := by decide +kernel

private theorem bLow_26 : Tables.bLow[26]! = lowBits D56.bRows[26]! := by decide +kernel

private theorem bLow_27 : Tables.bLow[27]! = lowBits D56.bRows[27]! := by decide +kernel

private theorem bLow_28 : Tables.bLow[28]! = lowBits D56.bRows[28]! := by decide +kernel

private theorem bLow_29 : Tables.bLow[29]! = lowBits D56.bRows[29]! := by decide +kernel

private theorem bLow_30 : Tables.bLow[30]! = lowBits D56.bRows[30]! := by decide +kernel

private theorem bLow_31 : Tables.bLow[31]! = lowBits D56.bRows[31]! := by decide +kernel

private theorem bLow_32 : Tables.bLow[32]! = lowBits D56.bRows[32]! := by decide +kernel

private theorem bLow_33 : Tables.bLow[33]! = lowBits D56.bRows[33]! := by decide +kernel

private theorem bLow_34 : Tables.bLow[34]! = lowBits D56.bRows[34]! := by decide +kernel

private theorem bLow_35 : Tables.bLow[35]! = lowBits D56.bRows[35]! := by decide +kernel

private theorem bLow_36 : Tables.bLow[36]! = lowBits D56.bRows[36]! := by decide +kernel

private theorem bLow_37 : Tables.bLow[37]! = lowBits D56.bRows[37]! := by decide +kernel

private theorem bLow_38 : Tables.bLow[38]! = lowBits D56.bRows[38]! := by decide +kernel

private theorem bLow_39 : Tables.bLow[39]! = lowBits D56.bRows[39]! := by decide +kernel

private theorem bLow_40 : Tables.bLow[40]! = lowBits D56.bRows[40]! := by decide +kernel

private theorem bLow_41 : Tables.bLow[41]! = lowBits D56.bRows[41]! := by decide +kernel

private theorem bLow_42 : Tables.bLow[42]! = lowBits D56.bRows[42]! := by decide +kernel

private theorem bLow_43 : Tables.bLow[43]! = lowBits D56.bRows[43]! := by decide +kernel

private theorem bLow_44 : Tables.bLow[44]! = lowBits D56.bRows[44]! := by decide +kernel

private theorem bLow_45 : Tables.bLow[45]! = lowBits D56.bRows[45]! := by decide +kernel

private theorem bLow_46 : Tables.bLow[46]! = lowBits D56.bRows[46]! := by decide +kernel

private theorem bLow_47 : Tables.bLow[47]! = lowBits D56.bRows[47]! := by decide +kernel

private theorem bLow_48 : Tables.bLow[48]! = lowBits D56.bRows[48]! := by decide +kernel

private theorem bLow_49 : Tables.bLow[49]! = lowBits D56.bRows[49]! := by decide +kernel

private theorem bLow_50 : Tables.bLow[50]! = lowBits D56.bRows[50]! := by decide +kernel

private theorem bLow_51 : Tables.bLow[51]! = lowBits D56.bRows[51]! := by decide +kernel

private theorem bLow_52 : Tables.bLow[52]! = lowBits D56.bRows[52]! := by decide +kernel

private theorem bLow_53 : Tables.bLow[53]! = lowBits D56.bRows[53]! := by decide +kernel

private theorem bLow_54 : Tables.bLow[54]! = lowBits D56.bRows[54]! := by decide +kernel

private theorem bLow_55 : Tables.bLow[55]! = lowBits D56.bRows[55]! := by decide +kernel

theorem bLow_checked (i : Fin 56) : Tables.bLow[i.val]! = lowBits D56.bRows[i.val]! := by
  fin_cases i

  · exact bLow_0

  · exact bLow_1

  · exact bLow_2

  · exact bLow_3

  · exact bLow_4

  · exact bLow_5

  · exact bLow_6

  · exact bLow_7

  · exact bLow_8

  · exact bLow_9

  · exact bLow_10

  · exact bLow_11

  · exact bLow_12

  · exact bLow_13

  · exact bLow_14

  · exact bLow_15

  · exact bLow_16

  · exact bLow_17

  · exact bLow_18

  · exact bLow_19

  · exact bLow_20

  · exact bLow_21

  · exact bLow_22

  · exact bLow_23

  · exact bLow_24

  · exact bLow_25

  · exact bLow_26

  · exact bLow_27

  · exact bLow_28

  · exact bLow_29

  · exact bLow_30

  · exact bLow_31

  · exact bLow_32

  · exact bLow_33

  · exact bLow_34

  · exact bLow_35

  · exact bLow_36

  · exact bLow_37

  · exact bLow_38

  · exact bLow_39

  · exact bLow_40

  · exact bLow_41

  · exact bLow_42

  · exact bLow_43

  · exact bLow_44

  · exact bLow_45

  · exact bLow_46

  · exact bLow_47

  · exact bLow_48

  · exact bLow_49

  · exact bLow_50

  · exact bLow_51

  · exact bLow_52

  · exact bLow_53

  · exact bLow_54

  · exact bLow_55

private theorem b_row0 : ∀ k : Fin 0,
    Tables.b.get (triangular 0 + k.val) =
      (Tables.bHigh[0]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[0]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row1 : ∀ k : Fin 1,
    Tables.b.get (triangular 1 + k.val) =
      (Tables.bHigh[1]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[1]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row2 : ∀ k : Fin 2,
    Tables.b.get (triangular 2 + k.val) =
      (Tables.bHigh[2]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[2]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row3 : ∀ k : Fin 3,
    Tables.b.get (triangular 3 + k.val) =
      (Tables.bHigh[3]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[3]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row4 : ∀ k : Fin 4,
    Tables.b.get (triangular 4 + k.val) =
      (Tables.bHigh[4]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[4]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row5 : ∀ k : Fin 5,
    Tables.b.get (triangular 5 + k.val) =
      (Tables.bHigh[5]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[5]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row6 : ∀ k : Fin 6,
    Tables.b.get (triangular 6 + k.val) =
      (Tables.bHigh[6]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[6]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row7 : ∀ k : Fin 7,
    Tables.b.get (triangular 7 + k.val) =
      (Tables.bHigh[7]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[7]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row8 : ∀ k : Fin 8,
    Tables.b.get (triangular 8 + k.val) =
      (Tables.bHigh[8]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[8]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row9 : ∀ k : Fin 9,
    Tables.b.get (triangular 9 + k.val) =
      (Tables.bHigh[9]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[9]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row10 : ∀ k : Fin 10,
    Tables.b.get (triangular 10 + k.val) =
      (Tables.bHigh[10]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[10]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row11 : ∀ k : Fin 11,
    Tables.b.get (triangular 11 + k.val) =
      (Tables.bHigh[11]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[11]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row12 : ∀ k : Fin 12,
    Tables.b.get (triangular 12 + k.val) =
      (Tables.bHigh[12]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[12]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row13 : ∀ k : Fin 13,
    Tables.b.get (triangular 13 + k.val) =
      (Tables.bHigh[13]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[13]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row14 : ∀ k : Fin 14,
    Tables.b.get (triangular 14 + k.val) =
      (Tables.bHigh[14]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[14]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row15 : ∀ k : Fin 15,
    Tables.b.get (triangular 15 + k.val) =
      (Tables.bHigh[15]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[15]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row16 : ∀ k : Fin 16,
    Tables.b.get (triangular 16 + k.val) =
      (Tables.bHigh[16]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[16]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row17 : ∀ k : Fin 17,
    Tables.b.get (triangular 17 + k.val) =
      (Tables.bHigh[17]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[17]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row18 : ∀ k : Fin 18,
    Tables.b.get (triangular 18 + k.val) =
      (Tables.bHigh[18]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[18]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row19 : ∀ k : Fin 19,
    Tables.b.get (triangular 19 + k.val) =
      (Tables.bHigh[19]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[19]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row20 : ∀ k : Fin 20,
    Tables.b.get (triangular 20 + k.val) =
      (Tables.bHigh[20]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[20]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row21 : ∀ k : Fin 21,
    Tables.b.get (triangular 21 + k.val) =
      (Tables.bHigh[21]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[21]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row22 : ∀ k : Fin 22,
    Tables.b.get (triangular 22 + k.val) =
      (Tables.bHigh[22]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[22]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row23 : ∀ k : Fin 23,
    Tables.b.get (triangular 23 + k.val) =
      (Tables.bHigh[23]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[23]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row24 : ∀ k : Fin 24,
    Tables.b.get (triangular 24 + k.val) =
      (Tables.bHigh[24]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[24]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row25 : ∀ k : Fin 25,
    Tables.b.get (triangular 25 + k.val) =
      (Tables.bHigh[25]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[25]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row26 : ∀ k : Fin 26,
    Tables.b.get (triangular 26 + k.val) =
      (Tables.bHigh[26]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[26]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row27 : ∀ k : Fin 27,
    Tables.b.get (triangular 27 + k.val) =
      (Tables.bHigh[27]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[27]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row28 : ∀ k : Fin 28,
    Tables.b.get (triangular 28 + k.val) =
      (Tables.bHigh[28]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[28]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row29 : ∀ k : Fin 29,
    Tables.b.get (triangular 29 + k.val) =
      (Tables.bHigh[29]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[29]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row30 : ∀ k : Fin 30,
    Tables.b.get (triangular 30 + k.val) =
      (Tables.bHigh[30]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[30]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row31 : ∀ k : Fin 31,
    Tables.b.get (triangular 31 + k.val) =
      (Tables.bHigh[31]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[31]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row32 : ∀ k : Fin 32,
    Tables.b.get (triangular 32 + k.val) =
      (Tables.bHigh[32]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[32]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row33 : ∀ k : Fin 33,
    Tables.b.get (triangular 33 + k.val) =
      (Tables.bHigh[33]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[33]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row34 : ∀ k : Fin 34,
    Tables.b.get (triangular 34 + k.val) =
      (Tables.bHigh[34]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[34]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row35 : ∀ k : Fin 35,
    Tables.b.get (triangular 35 + k.val) =
      (Tables.bHigh[35]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[35]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row36 : ∀ k : Fin 36,
    Tables.b.get (triangular 36 + k.val) =
      (Tables.bHigh[36]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[36]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row37 : ∀ k : Fin 37,
    Tables.b.get (triangular 37 + k.val) =
      (Tables.bHigh[37]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[37]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row38 : ∀ k : Fin 38,
    Tables.b.get (triangular 38 + k.val) =
      (Tables.bHigh[38]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[38]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row39 : ∀ k : Fin 39,
    Tables.b.get (triangular 39 + k.val) =
      (Tables.bHigh[39]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[39]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row40 : ∀ k : Fin 40,
    Tables.b.get (triangular 40 + k.val) =
      (Tables.bHigh[40]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[40]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row41 : ∀ k : Fin 41,
    Tables.b.get (triangular 41 + k.val) =
      (Tables.bHigh[41]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[41]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row42 : ∀ k : Fin 42,
    Tables.b.get (triangular 42 + k.val) =
      (Tables.bHigh[42]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[42]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row43 : ∀ k : Fin 43,
    Tables.b.get (triangular 43 + k.val) =
      (Tables.bHigh[43]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[43]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row44 : ∀ k : Fin 44,
    Tables.b.get (triangular 44 + k.val) =
      (Tables.bHigh[44]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[44]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row45 : ∀ k : Fin 45,
    Tables.b.get (triangular 45 + k.val) =
      (Tables.bHigh[45]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[45]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row46 : ∀ k : Fin 46,
    Tables.b.get (triangular 46 + k.val) =
      (Tables.bHigh[46]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[46]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row47 : ∀ k : Fin 47,
    Tables.b.get (triangular 47 + k.val) =
      (Tables.bHigh[47]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[47]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row48 : ∀ k : Fin 48,
    Tables.b.get (triangular 48 + k.val) =
      (Tables.bHigh[48]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[48]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row49 : ∀ k : Fin 49,
    Tables.b.get (triangular 49 + k.val) =
      (Tables.bHigh[49]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[49]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row50 : ∀ k : Fin 50,
    Tables.b.get (triangular 50 + k.val) =
      (Tables.bHigh[50]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[50]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row51 : ∀ k : Fin 51,
    Tables.b.get (triangular 51 + k.val) =
      (Tables.bHigh[51]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[51]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row52 : ∀ k : Fin 52,
    Tables.b.get (triangular 52 + k.val) =
      (Tables.bHigh[52]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[52]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row53 : ∀ k : Fin 53,
    Tables.b.get (triangular 53 + k.val) =
      (Tables.bHigh[53]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[53]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row54 : ∀ k : Fin 54,
    Tables.b.get (triangular 54 + k.val) =
      (Tables.bHigh[54]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[54]! &&& Tables.bHigh[k.val]!) := by decide +kernel

private theorem b_row55 : ∀ k : Fin 55,
    Tables.b.get (triangular 55 + k.val) =
      (Tables.bHigh[55]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[55]! &&& Tables.bHigh[k.val]!) := by decide +kernel

theorem b_rows_checked (j : Fin 56) (k : Fin j.val) :
    Tables.b.get (triangular j.val + k.val) =
      (Tables.bHigh[j.val]! &&& Tables.bLow[k.val]!) ^^^
      (Tables.bLow[j.val]! &&& Tables.bHigh[k.val]!) := by
  fin_cases j

  · exact b_row0 k

  · exact b_row1 k

  · exact b_row2 k

  · exact b_row3 k

  · exact b_row4 k

  · exact b_row5 k

  · exact b_row6 k

  · exact b_row7 k

  · exact b_row8 k

  · exact b_row9 k

  · exact b_row10 k

  · exact b_row11 k

  · exact b_row12 k

  · exact b_row13 k

  · exact b_row14 k

  · exact b_row15 k

  · exact b_row16 k

  · exact b_row17 k

  · exact b_row18 k

  · exact b_row19 k

  · exact b_row20 k

  · exact b_row21 k

  · exact b_row22 k

  · exact b_row23 k

  · exact b_row24 k

  · exact b_row25 k

  · exact b_row26 k

  · exact b_row27 k

  · exact b_row28 k

  · exact b_row29 k

  · exact b_row30 k

  · exact b_row31 k

  · exact b_row32 k

  · exact b_row33 k

  · exact b_row34 k

  · exact b_row35 k

  · exact b_row36 k

  · exact b_row37 k

  · exact b_row38 k

  · exact b_row39 k

  · exact b_row40 k

  · exact b_row41 k

  · exact b_row42 k

  · exact b_row43 k

  · exact b_row44 k

  · exact b_row45 k

  · exact b_row46 k

  · exact b_row47 k

  · exact b_row48 k

  · exact b_row49 k

  · exact b_row50 k

  · exact b_row51 k

  · exact b_row52 k

  · exact b_row53 k

  · exact b_row54 k

  · exact b_row55 k

private theorem bit_and (a b j : ℕ) : bit (a &&& b) j = bit a j * bit b j := by
  simp only [bit, Nat.testBit_and]
  cases a.testBit j <;> cases b.testBit j <;> decide

theorem exterior_of_packed (t : RowTree) (src hi lo : Array ℕ)
    (ht : t.Valid)
    (hh : ∀ i : Fin 56, hi[i.val]! = highBits src[i.val]!)
    (hl : ∀ i : Fin 56, lo[i.val]! = lowBits src[i.val]!)
    (hr : ∀ j : Fin 56, ∀ k : Fin j.val,
      t.get (triangular j.val + k.val) =
        (hi[j.val]! &&& lo[k.val]!) ^^^ (lo[j.val]! &&& hi[k.val]!)) :
    RowArithmetic.matrix 1540 1540 t.rows = exteriorMatrix (decode 56 src) := by
  funext i j
  change bit t.rows[i.val]! j.val = _
  rw [← t.get_eq ht]
  have hrow := hr (pair i).1 ⟨(pair i).2.val, pair_lt i⟩
  rw [triangular_eq, pair_index] at hrow
  rw [hrow, bit_xor, bit_and, bit_and,
    hh (pair i).1, hl (pair i).2, hl (pair i).1, hh (pair i).2]
  simp only [exteriorMatrix, decode, bit, highBits_bit, lowBits_bit]

/-- Exact packing of the first ambient minor matrix, in the published basis. -/
theorem ambientA_packed : RowArithmetic.matrix 1540 1540 Tables.a.rows = ambientA := by
  change RowArithmetic.matrix 1540 1540 Tables.a.rows = exteriorMatrix (decode 56 D56.aRows)
  exact exterior_of_packed Tables.a D56.aRows Tables.aHigh Tables.aLow Tables.a_spec.2
    aHigh_checked aLow_checked a_rows_checked

/-- Exact packing of the second ambient minor matrix, in the published basis. -/
theorem ambientB_packed : RowArithmetic.matrix 1540 1540 Tables.b.rows = ambientB := by
  change RowArithmetic.matrix 1540 1540 Tables.b.rows = exteriorMatrix (decode 56 D56.bRows)
  exact exterior_of_packed Tables.b D56.bRows Tables.bHigh Tables.bLow Tables.b_spec.2
    bHigh_checked bLow_checked b_rows_checked


end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining
