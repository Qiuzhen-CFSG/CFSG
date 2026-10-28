module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: localB times ab2

Each of the 111 row products is compared with a canonical result row.
The carry-free arithmetic theorem then proves the matrix identity.

Source: GLS3, Lyons involution table (p.278); ATLAS LyG1-f5r111B0
and LyG1-max4W1. Attribution and reproducible candidate generation:
`source/README.md` and `source/GenerateCertificates.py`.
-/

namespace Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate

open Lyons.Atlas111WordCertificate
open Lyons.SimplicityCertificate.LocalCommutant.Words

set_option Elab.async false

set_option maxRecDepth 4096 in
private theorem yx2_row0 :
    digitsEq 111 (rowProduct (localBRows 0) ab2Rows 111) (yx2Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row1 :
    digitsEq 111 (rowProduct (localBRows 1) ab2Rows 111) (yx2Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row2 :
    digitsEq 111 (rowProduct (localBRows 2) ab2Rows 111) (yx2Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row3 :
    digitsEq 111 (rowProduct (localBRows 3) ab2Rows 111) (yx2Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row4 :
    digitsEq 111 (rowProduct (localBRows 4) ab2Rows 111) (yx2Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row5 :
    digitsEq 111 (rowProduct (localBRows 5) ab2Rows 111) (yx2Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row6 :
    digitsEq 111 (rowProduct (localBRows 6) ab2Rows 111) (yx2Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row7 :
    digitsEq 111 (rowProduct (localBRows 7) ab2Rows 111) (yx2Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row8 :
    digitsEq 111 (rowProduct (localBRows 8) ab2Rows 111) (yx2Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row9 :
    digitsEq 111 (rowProduct (localBRows 9) ab2Rows 111) (yx2Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row10 :
    digitsEq 111 (rowProduct (localBRows 10) ab2Rows 111) (yx2Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row11 :
    digitsEq 111 (rowProduct (localBRows 11) ab2Rows 111) (yx2Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row12 :
    digitsEq 111 (rowProduct (localBRows 12) ab2Rows 111) (yx2Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row13 :
    digitsEq 111 (rowProduct (localBRows 13) ab2Rows 111) (yx2Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row14 :
    digitsEq 111 (rowProduct (localBRows 14) ab2Rows 111) (yx2Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row15 :
    digitsEq 111 (rowProduct (localBRows 15) ab2Rows 111) (yx2Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row16 :
    digitsEq 111 (rowProduct (localBRows 16) ab2Rows 111) (yx2Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row17 :
    digitsEq 111 (rowProduct (localBRows 17) ab2Rows 111) (yx2Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row18 :
    digitsEq 111 (rowProduct (localBRows 18) ab2Rows 111) (yx2Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row19 :
    digitsEq 111 (rowProduct (localBRows 19) ab2Rows 111) (yx2Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row20 :
    digitsEq 111 (rowProduct (localBRows 20) ab2Rows 111) (yx2Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row21 :
    digitsEq 111 (rowProduct (localBRows 21) ab2Rows 111) (yx2Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row22 :
    digitsEq 111 (rowProduct (localBRows 22) ab2Rows 111) (yx2Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row23 :
    digitsEq 111 (rowProduct (localBRows 23) ab2Rows 111) (yx2Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row24 :
    digitsEq 111 (rowProduct (localBRows 24) ab2Rows 111) (yx2Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row25 :
    digitsEq 111 (rowProduct (localBRows 25) ab2Rows 111) (yx2Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row26 :
    digitsEq 111 (rowProduct (localBRows 26) ab2Rows 111) (yx2Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row27 :
    digitsEq 111 (rowProduct (localBRows 27) ab2Rows 111) (yx2Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row28 :
    digitsEq 111 (rowProduct (localBRows 28) ab2Rows 111) (yx2Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row29 :
    digitsEq 111 (rowProduct (localBRows 29) ab2Rows 111) (yx2Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row30 :
    digitsEq 111 (rowProduct (localBRows 30) ab2Rows 111) (yx2Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row31 :
    digitsEq 111 (rowProduct (localBRows 31) ab2Rows 111) (yx2Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row32 :
    digitsEq 111 (rowProduct (localBRows 32) ab2Rows 111) (yx2Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row33 :
    digitsEq 111 (rowProduct (localBRows 33) ab2Rows 111) (yx2Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row34 :
    digitsEq 111 (rowProduct (localBRows 34) ab2Rows 111) (yx2Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row35 :
    digitsEq 111 (rowProduct (localBRows 35) ab2Rows 111) (yx2Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row36 :
    digitsEq 111 (rowProduct (localBRows 36) ab2Rows 111) (yx2Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row37 :
    digitsEq 111 (rowProduct (localBRows 37) ab2Rows 111) (yx2Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row38 :
    digitsEq 111 (rowProduct (localBRows 38) ab2Rows 111) (yx2Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row39 :
    digitsEq 111 (rowProduct (localBRows 39) ab2Rows 111) (yx2Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row40 :
    digitsEq 111 (rowProduct (localBRows 40) ab2Rows 111) (yx2Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row41 :
    digitsEq 111 (rowProduct (localBRows 41) ab2Rows 111) (yx2Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row42 :
    digitsEq 111 (rowProduct (localBRows 42) ab2Rows 111) (yx2Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row43 :
    digitsEq 111 (rowProduct (localBRows 43) ab2Rows 111) (yx2Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row44 :
    digitsEq 111 (rowProduct (localBRows 44) ab2Rows 111) (yx2Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row45 :
    digitsEq 111 (rowProduct (localBRows 45) ab2Rows 111) (yx2Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row46 :
    digitsEq 111 (rowProduct (localBRows 46) ab2Rows 111) (yx2Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row47 :
    digitsEq 111 (rowProduct (localBRows 47) ab2Rows 111) (yx2Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row48 :
    digitsEq 111 (rowProduct (localBRows 48) ab2Rows 111) (yx2Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row49 :
    digitsEq 111 (rowProduct (localBRows 49) ab2Rows 111) (yx2Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row50 :
    digitsEq 111 (rowProduct (localBRows 50) ab2Rows 111) (yx2Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row51 :
    digitsEq 111 (rowProduct (localBRows 51) ab2Rows 111) (yx2Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row52 :
    digitsEq 111 (rowProduct (localBRows 52) ab2Rows 111) (yx2Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row53 :
    digitsEq 111 (rowProduct (localBRows 53) ab2Rows 111) (yx2Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row54 :
    digitsEq 111 (rowProduct (localBRows 54) ab2Rows 111) (yx2Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row55 :
    digitsEq 111 (rowProduct (localBRows 55) ab2Rows 111) (yx2Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row56 :
    digitsEq 111 (rowProduct (localBRows 56) ab2Rows 111) (yx2Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row57 :
    digitsEq 111 (rowProduct (localBRows 57) ab2Rows 111) (yx2Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row58 :
    digitsEq 111 (rowProduct (localBRows 58) ab2Rows 111) (yx2Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row59 :
    digitsEq 111 (rowProduct (localBRows 59) ab2Rows 111) (yx2Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row60 :
    digitsEq 111 (rowProduct (localBRows 60) ab2Rows 111) (yx2Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row61 :
    digitsEq 111 (rowProduct (localBRows 61) ab2Rows 111) (yx2Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row62 :
    digitsEq 111 (rowProduct (localBRows 62) ab2Rows 111) (yx2Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row63 :
    digitsEq 111 (rowProduct (localBRows 63) ab2Rows 111) (yx2Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row64 :
    digitsEq 111 (rowProduct (localBRows 64) ab2Rows 111) (yx2Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row65 :
    digitsEq 111 (rowProduct (localBRows 65) ab2Rows 111) (yx2Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row66 :
    digitsEq 111 (rowProduct (localBRows 66) ab2Rows 111) (yx2Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row67 :
    digitsEq 111 (rowProduct (localBRows 67) ab2Rows 111) (yx2Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row68 :
    digitsEq 111 (rowProduct (localBRows 68) ab2Rows 111) (yx2Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row69 :
    digitsEq 111 (rowProduct (localBRows 69) ab2Rows 111) (yx2Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row70 :
    digitsEq 111 (rowProduct (localBRows 70) ab2Rows 111) (yx2Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row71 :
    digitsEq 111 (rowProduct (localBRows 71) ab2Rows 111) (yx2Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row72 :
    digitsEq 111 (rowProduct (localBRows 72) ab2Rows 111) (yx2Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row73 :
    digitsEq 111 (rowProduct (localBRows 73) ab2Rows 111) (yx2Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row74 :
    digitsEq 111 (rowProduct (localBRows 74) ab2Rows 111) (yx2Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row75 :
    digitsEq 111 (rowProduct (localBRows 75) ab2Rows 111) (yx2Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row76 :
    digitsEq 111 (rowProduct (localBRows 76) ab2Rows 111) (yx2Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row77 :
    digitsEq 111 (rowProduct (localBRows 77) ab2Rows 111) (yx2Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row78 :
    digitsEq 111 (rowProduct (localBRows 78) ab2Rows 111) (yx2Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row79 :
    digitsEq 111 (rowProduct (localBRows 79) ab2Rows 111) (yx2Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row80 :
    digitsEq 111 (rowProduct (localBRows 80) ab2Rows 111) (yx2Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row81 :
    digitsEq 111 (rowProduct (localBRows 81) ab2Rows 111) (yx2Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row82 :
    digitsEq 111 (rowProduct (localBRows 82) ab2Rows 111) (yx2Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row83 :
    digitsEq 111 (rowProduct (localBRows 83) ab2Rows 111) (yx2Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row84 :
    digitsEq 111 (rowProduct (localBRows 84) ab2Rows 111) (yx2Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row85 :
    digitsEq 111 (rowProduct (localBRows 85) ab2Rows 111) (yx2Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row86 :
    digitsEq 111 (rowProduct (localBRows 86) ab2Rows 111) (yx2Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row87 :
    digitsEq 111 (rowProduct (localBRows 87) ab2Rows 111) (yx2Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row88 :
    digitsEq 111 (rowProduct (localBRows 88) ab2Rows 111) (yx2Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row89 :
    digitsEq 111 (rowProduct (localBRows 89) ab2Rows 111) (yx2Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row90 :
    digitsEq 111 (rowProduct (localBRows 90) ab2Rows 111) (yx2Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row91 :
    digitsEq 111 (rowProduct (localBRows 91) ab2Rows 111) (yx2Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row92 :
    digitsEq 111 (rowProduct (localBRows 92) ab2Rows 111) (yx2Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row93 :
    digitsEq 111 (rowProduct (localBRows 93) ab2Rows 111) (yx2Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row94 :
    digitsEq 111 (rowProduct (localBRows 94) ab2Rows 111) (yx2Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row95 :
    digitsEq 111 (rowProduct (localBRows 95) ab2Rows 111) (yx2Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row96 :
    digitsEq 111 (rowProduct (localBRows 96) ab2Rows 111) (yx2Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row97 :
    digitsEq 111 (rowProduct (localBRows 97) ab2Rows 111) (yx2Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row98 :
    digitsEq 111 (rowProduct (localBRows 98) ab2Rows 111) (yx2Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row99 :
    digitsEq 111 (rowProduct (localBRows 99) ab2Rows 111) (yx2Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row100 :
    digitsEq 111 (rowProduct (localBRows 100) ab2Rows 111) (yx2Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row101 :
    digitsEq 111 (rowProduct (localBRows 101) ab2Rows 111) (yx2Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row102 :
    digitsEq 111 (rowProduct (localBRows 102) ab2Rows 111) (yx2Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row103 :
    digitsEq 111 (rowProduct (localBRows 103) ab2Rows 111) (yx2Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row104 :
    digitsEq 111 (rowProduct (localBRows 104) ab2Rows 111) (yx2Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row105 :
    digitsEq 111 (rowProduct (localBRows 105) ab2Rows 111) (yx2Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row106 :
    digitsEq 111 (rowProduct (localBRows 106) ab2Rows 111) (yx2Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row107 :
    digitsEq 111 (rowProduct (localBRows 107) ab2Rows 111) (yx2Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row108 :
    digitsEq 111 (rowProduct (localBRows 108) ab2Rows 111) (yx2Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row109 :
    digitsEq 111 (rowProduct (localBRows 109) ab2Rows 111) (yx2Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_row110 :
    digitsEq 111 (rowProduct (localBRows 110) ab2Rows 111) (yx2Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2_rows : ∀ i,
    digitsEq 111 (rowProduct (localBRows i) ab2Rows 111) (yx2Rows i) = true :=
  (Fin.cases yx2_row0
    (Fin.cases yx2_row1
    (Fin.cases yx2_row2
    (Fin.cases yx2_row3
    (Fin.cases yx2_row4
    (Fin.cases yx2_row5
    (Fin.cases yx2_row6
    (Fin.cases yx2_row7
    (Fin.cases yx2_row8
    (Fin.cases yx2_row9
    (Fin.cases yx2_row10
    (Fin.cases yx2_row11
    (Fin.cases yx2_row12
    (Fin.cases yx2_row13
    (Fin.cases yx2_row14
    (Fin.cases yx2_row15
    (Fin.cases yx2_row16
    (Fin.cases yx2_row17
    (Fin.cases yx2_row18
    (Fin.cases yx2_row19
    (Fin.cases yx2_row20
    (Fin.cases yx2_row21
    (Fin.cases yx2_row22
    (Fin.cases yx2_row23
    (Fin.cases yx2_row24
    (Fin.cases yx2_row25
    (Fin.cases yx2_row26
    (Fin.cases yx2_row27
    (Fin.cases yx2_row28
    (Fin.cases yx2_row29
    (Fin.cases yx2_row30
    (Fin.cases yx2_row31
    (Fin.cases yx2_row32
    (Fin.cases yx2_row33
    (Fin.cases yx2_row34
    (Fin.cases yx2_row35
    (Fin.cases yx2_row36
    (Fin.cases yx2_row37
    (Fin.cases yx2_row38
    (Fin.cases yx2_row39
    (Fin.cases yx2_row40
    (Fin.cases yx2_row41
    (Fin.cases yx2_row42
    (Fin.cases yx2_row43
    (Fin.cases yx2_row44
    (Fin.cases yx2_row45
    (Fin.cases yx2_row46
    (Fin.cases yx2_row47
    (Fin.cases yx2_row48
    (Fin.cases yx2_row49
    (Fin.cases yx2_row50
    (Fin.cases yx2_row51
    (Fin.cases yx2_row52
    (Fin.cases yx2_row53
    (Fin.cases yx2_row54
    (Fin.cases yx2_row55
    (Fin.cases yx2_row56
    (Fin.cases yx2_row57
    (Fin.cases yx2_row58
    (Fin.cases yx2_row59
    (Fin.cases yx2_row60
    (Fin.cases yx2_row61
    (Fin.cases yx2_row62
    (Fin.cases yx2_row63
    (Fin.cases yx2_row64
    (Fin.cases yx2_row65
    (Fin.cases yx2_row66
    (Fin.cases yx2_row67
    (Fin.cases yx2_row68
    (Fin.cases yx2_row69
    (Fin.cases yx2_row70
    (Fin.cases yx2_row71
    (Fin.cases yx2_row72
    (Fin.cases yx2_row73
    (Fin.cases yx2_row74
    (Fin.cases yx2_row75
    (Fin.cases yx2_row76
    (Fin.cases yx2_row77
    (Fin.cases yx2_row78
    (Fin.cases yx2_row79
    (Fin.cases yx2_row80
    (Fin.cases yx2_row81
    (Fin.cases yx2_row82
    (Fin.cases yx2_row83
    (Fin.cases yx2_row84
    (Fin.cases yx2_row85
    (Fin.cases yx2_row86
    (Fin.cases yx2_row87
    (Fin.cases yx2_row88
    (Fin.cases yx2_row89
    (Fin.cases yx2_row90
    (Fin.cases yx2_row91
    (Fin.cases yx2_row92
    (Fin.cases yx2_row93
    (Fin.cases yx2_row94
    (Fin.cases yx2_row95
    (Fin.cases yx2_row96
    (Fin.cases yx2_row97
    (Fin.cases yx2_row98
    (Fin.cases yx2_row99
    (Fin.cases yx2_row100
    (Fin.cases yx2_row101
    (Fin.cases yx2_row102
    (Fin.cases yx2_row103
    (Fin.cases yx2_row104
    (Fin.cases yx2_row105
    (Fin.cases yx2_row106
    (Fin.cases yx2_row107
    (Fin.cases yx2_row108
    (Fin.cases yx2_row109
    (Fin.cases yx2_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_yx2 : localBMatrix * ab2Matrix = yx2Matrix :=
  decode_mul _ _ _ localB_small ab2_small yx2_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
