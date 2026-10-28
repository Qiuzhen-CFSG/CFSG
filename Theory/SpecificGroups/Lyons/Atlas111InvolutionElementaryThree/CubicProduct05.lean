module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: cubic times cubic

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
private theorem cubic2_row0 :
    digitsEq 111 (rowProduct (cubicRows 0) cubicRows 111) (cubic2Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row1 :
    digitsEq 111 (rowProduct (cubicRows 1) cubicRows 111) (cubic2Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row2 :
    digitsEq 111 (rowProduct (cubicRows 2) cubicRows 111) (cubic2Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row3 :
    digitsEq 111 (rowProduct (cubicRows 3) cubicRows 111) (cubic2Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row4 :
    digitsEq 111 (rowProduct (cubicRows 4) cubicRows 111) (cubic2Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row5 :
    digitsEq 111 (rowProduct (cubicRows 5) cubicRows 111) (cubic2Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row6 :
    digitsEq 111 (rowProduct (cubicRows 6) cubicRows 111) (cubic2Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row7 :
    digitsEq 111 (rowProduct (cubicRows 7) cubicRows 111) (cubic2Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row8 :
    digitsEq 111 (rowProduct (cubicRows 8) cubicRows 111) (cubic2Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row9 :
    digitsEq 111 (rowProduct (cubicRows 9) cubicRows 111) (cubic2Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row10 :
    digitsEq 111 (rowProduct (cubicRows 10) cubicRows 111) (cubic2Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row11 :
    digitsEq 111 (rowProduct (cubicRows 11) cubicRows 111) (cubic2Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row12 :
    digitsEq 111 (rowProduct (cubicRows 12) cubicRows 111) (cubic2Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row13 :
    digitsEq 111 (rowProduct (cubicRows 13) cubicRows 111) (cubic2Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row14 :
    digitsEq 111 (rowProduct (cubicRows 14) cubicRows 111) (cubic2Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row15 :
    digitsEq 111 (rowProduct (cubicRows 15) cubicRows 111) (cubic2Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row16 :
    digitsEq 111 (rowProduct (cubicRows 16) cubicRows 111) (cubic2Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row17 :
    digitsEq 111 (rowProduct (cubicRows 17) cubicRows 111) (cubic2Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row18 :
    digitsEq 111 (rowProduct (cubicRows 18) cubicRows 111) (cubic2Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row19 :
    digitsEq 111 (rowProduct (cubicRows 19) cubicRows 111) (cubic2Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row20 :
    digitsEq 111 (rowProduct (cubicRows 20) cubicRows 111) (cubic2Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row21 :
    digitsEq 111 (rowProduct (cubicRows 21) cubicRows 111) (cubic2Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row22 :
    digitsEq 111 (rowProduct (cubicRows 22) cubicRows 111) (cubic2Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row23 :
    digitsEq 111 (rowProduct (cubicRows 23) cubicRows 111) (cubic2Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row24 :
    digitsEq 111 (rowProduct (cubicRows 24) cubicRows 111) (cubic2Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row25 :
    digitsEq 111 (rowProduct (cubicRows 25) cubicRows 111) (cubic2Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row26 :
    digitsEq 111 (rowProduct (cubicRows 26) cubicRows 111) (cubic2Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row27 :
    digitsEq 111 (rowProduct (cubicRows 27) cubicRows 111) (cubic2Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row28 :
    digitsEq 111 (rowProduct (cubicRows 28) cubicRows 111) (cubic2Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row29 :
    digitsEq 111 (rowProduct (cubicRows 29) cubicRows 111) (cubic2Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row30 :
    digitsEq 111 (rowProduct (cubicRows 30) cubicRows 111) (cubic2Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row31 :
    digitsEq 111 (rowProduct (cubicRows 31) cubicRows 111) (cubic2Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row32 :
    digitsEq 111 (rowProduct (cubicRows 32) cubicRows 111) (cubic2Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row33 :
    digitsEq 111 (rowProduct (cubicRows 33) cubicRows 111) (cubic2Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row34 :
    digitsEq 111 (rowProduct (cubicRows 34) cubicRows 111) (cubic2Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row35 :
    digitsEq 111 (rowProduct (cubicRows 35) cubicRows 111) (cubic2Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row36 :
    digitsEq 111 (rowProduct (cubicRows 36) cubicRows 111) (cubic2Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row37 :
    digitsEq 111 (rowProduct (cubicRows 37) cubicRows 111) (cubic2Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row38 :
    digitsEq 111 (rowProduct (cubicRows 38) cubicRows 111) (cubic2Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row39 :
    digitsEq 111 (rowProduct (cubicRows 39) cubicRows 111) (cubic2Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row40 :
    digitsEq 111 (rowProduct (cubicRows 40) cubicRows 111) (cubic2Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row41 :
    digitsEq 111 (rowProduct (cubicRows 41) cubicRows 111) (cubic2Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row42 :
    digitsEq 111 (rowProduct (cubicRows 42) cubicRows 111) (cubic2Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row43 :
    digitsEq 111 (rowProduct (cubicRows 43) cubicRows 111) (cubic2Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row44 :
    digitsEq 111 (rowProduct (cubicRows 44) cubicRows 111) (cubic2Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row45 :
    digitsEq 111 (rowProduct (cubicRows 45) cubicRows 111) (cubic2Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row46 :
    digitsEq 111 (rowProduct (cubicRows 46) cubicRows 111) (cubic2Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row47 :
    digitsEq 111 (rowProduct (cubicRows 47) cubicRows 111) (cubic2Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row48 :
    digitsEq 111 (rowProduct (cubicRows 48) cubicRows 111) (cubic2Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row49 :
    digitsEq 111 (rowProduct (cubicRows 49) cubicRows 111) (cubic2Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row50 :
    digitsEq 111 (rowProduct (cubicRows 50) cubicRows 111) (cubic2Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row51 :
    digitsEq 111 (rowProduct (cubicRows 51) cubicRows 111) (cubic2Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row52 :
    digitsEq 111 (rowProduct (cubicRows 52) cubicRows 111) (cubic2Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row53 :
    digitsEq 111 (rowProduct (cubicRows 53) cubicRows 111) (cubic2Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row54 :
    digitsEq 111 (rowProduct (cubicRows 54) cubicRows 111) (cubic2Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row55 :
    digitsEq 111 (rowProduct (cubicRows 55) cubicRows 111) (cubic2Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row56 :
    digitsEq 111 (rowProduct (cubicRows 56) cubicRows 111) (cubic2Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row57 :
    digitsEq 111 (rowProduct (cubicRows 57) cubicRows 111) (cubic2Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row58 :
    digitsEq 111 (rowProduct (cubicRows 58) cubicRows 111) (cubic2Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row59 :
    digitsEq 111 (rowProduct (cubicRows 59) cubicRows 111) (cubic2Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row60 :
    digitsEq 111 (rowProduct (cubicRows 60) cubicRows 111) (cubic2Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row61 :
    digitsEq 111 (rowProduct (cubicRows 61) cubicRows 111) (cubic2Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row62 :
    digitsEq 111 (rowProduct (cubicRows 62) cubicRows 111) (cubic2Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row63 :
    digitsEq 111 (rowProduct (cubicRows 63) cubicRows 111) (cubic2Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row64 :
    digitsEq 111 (rowProduct (cubicRows 64) cubicRows 111) (cubic2Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row65 :
    digitsEq 111 (rowProduct (cubicRows 65) cubicRows 111) (cubic2Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row66 :
    digitsEq 111 (rowProduct (cubicRows 66) cubicRows 111) (cubic2Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row67 :
    digitsEq 111 (rowProduct (cubicRows 67) cubicRows 111) (cubic2Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row68 :
    digitsEq 111 (rowProduct (cubicRows 68) cubicRows 111) (cubic2Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row69 :
    digitsEq 111 (rowProduct (cubicRows 69) cubicRows 111) (cubic2Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row70 :
    digitsEq 111 (rowProduct (cubicRows 70) cubicRows 111) (cubic2Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row71 :
    digitsEq 111 (rowProduct (cubicRows 71) cubicRows 111) (cubic2Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row72 :
    digitsEq 111 (rowProduct (cubicRows 72) cubicRows 111) (cubic2Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row73 :
    digitsEq 111 (rowProduct (cubicRows 73) cubicRows 111) (cubic2Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row74 :
    digitsEq 111 (rowProduct (cubicRows 74) cubicRows 111) (cubic2Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row75 :
    digitsEq 111 (rowProduct (cubicRows 75) cubicRows 111) (cubic2Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row76 :
    digitsEq 111 (rowProduct (cubicRows 76) cubicRows 111) (cubic2Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row77 :
    digitsEq 111 (rowProduct (cubicRows 77) cubicRows 111) (cubic2Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row78 :
    digitsEq 111 (rowProduct (cubicRows 78) cubicRows 111) (cubic2Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row79 :
    digitsEq 111 (rowProduct (cubicRows 79) cubicRows 111) (cubic2Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row80 :
    digitsEq 111 (rowProduct (cubicRows 80) cubicRows 111) (cubic2Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row81 :
    digitsEq 111 (rowProduct (cubicRows 81) cubicRows 111) (cubic2Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row82 :
    digitsEq 111 (rowProduct (cubicRows 82) cubicRows 111) (cubic2Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row83 :
    digitsEq 111 (rowProduct (cubicRows 83) cubicRows 111) (cubic2Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row84 :
    digitsEq 111 (rowProduct (cubicRows 84) cubicRows 111) (cubic2Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row85 :
    digitsEq 111 (rowProduct (cubicRows 85) cubicRows 111) (cubic2Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row86 :
    digitsEq 111 (rowProduct (cubicRows 86) cubicRows 111) (cubic2Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row87 :
    digitsEq 111 (rowProduct (cubicRows 87) cubicRows 111) (cubic2Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row88 :
    digitsEq 111 (rowProduct (cubicRows 88) cubicRows 111) (cubic2Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row89 :
    digitsEq 111 (rowProduct (cubicRows 89) cubicRows 111) (cubic2Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row90 :
    digitsEq 111 (rowProduct (cubicRows 90) cubicRows 111) (cubic2Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row91 :
    digitsEq 111 (rowProduct (cubicRows 91) cubicRows 111) (cubic2Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row92 :
    digitsEq 111 (rowProduct (cubicRows 92) cubicRows 111) (cubic2Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row93 :
    digitsEq 111 (rowProduct (cubicRows 93) cubicRows 111) (cubic2Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row94 :
    digitsEq 111 (rowProduct (cubicRows 94) cubicRows 111) (cubic2Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row95 :
    digitsEq 111 (rowProduct (cubicRows 95) cubicRows 111) (cubic2Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row96 :
    digitsEq 111 (rowProduct (cubicRows 96) cubicRows 111) (cubic2Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row97 :
    digitsEq 111 (rowProduct (cubicRows 97) cubicRows 111) (cubic2Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row98 :
    digitsEq 111 (rowProduct (cubicRows 98) cubicRows 111) (cubic2Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row99 :
    digitsEq 111 (rowProduct (cubicRows 99) cubicRows 111) (cubic2Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row100 :
    digitsEq 111 (rowProduct (cubicRows 100) cubicRows 111) (cubic2Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row101 :
    digitsEq 111 (rowProduct (cubicRows 101) cubicRows 111) (cubic2Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row102 :
    digitsEq 111 (rowProduct (cubicRows 102) cubicRows 111) (cubic2Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row103 :
    digitsEq 111 (rowProduct (cubicRows 103) cubicRows 111) (cubic2Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row104 :
    digitsEq 111 (rowProduct (cubicRows 104) cubicRows 111) (cubic2Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row105 :
    digitsEq 111 (rowProduct (cubicRows 105) cubicRows 111) (cubic2Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row106 :
    digitsEq 111 (rowProduct (cubicRows 106) cubicRows 111) (cubic2Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row107 :
    digitsEq 111 (rowProduct (cubicRows 107) cubicRows 111) (cubic2Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row108 :
    digitsEq 111 (rowProduct (cubicRows 108) cubicRows 111) (cubic2Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row109 :
    digitsEq 111 (rowProduct (cubicRows 109) cubicRows 111) (cubic2Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_row110 :
    digitsEq 111 (rowProduct (cubicRows 110) cubicRows 111) (cubic2Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic2_rows : ∀ i,
    digitsEq 111 (rowProduct (cubicRows i) cubicRows 111) (cubic2Rows i) = true :=
  (Fin.cases cubic2_row0
    (Fin.cases cubic2_row1
    (Fin.cases cubic2_row2
    (Fin.cases cubic2_row3
    (Fin.cases cubic2_row4
    (Fin.cases cubic2_row5
    (Fin.cases cubic2_row6
    (Fin.cases cubic2_row7
    (Fin.cases cubic2_row8
    (Fin.cases cubic2_row9
    (Fin.cases cubic2_row10
    (Fin.cases cubic2_row11
    (Fin.cases cubic2_row12
    (Fin.cases cubic2_row13
    (Fin.cases cubic2_row14
    (Fin.cases cubic2_row15
    (Fin.cases cubic2_row16
    (Fin.cases cubic2_row17
    (Fin.cases cubic2_row18
    (Fin.cases cubic2_row19
    (Fin.cases cubic2_row20
    (Fin.cases cubic2_row21
    (Fin.cases cubic2_row22
    (Fin.cases cubic2_row23
    (Fin.cases cubic2_row24
    (Fin.cases cubic2_row25
    (Fin.cases cubic2_row26
    (Fin.cases cubic2_row27
    (Fin.cases cubic2_row28
    (Fin.cases cubic2_row29
    (Fin.cases cubic2_row30
    (Fin.cases cubic2_row31
    (Fin.cases cubic2_row32
    (Fin.cases cubic2_row33
    (Fin.cases cubic2_row34
    (Fin.cases cubic2_row35
    (Fin.cases cubic2_row36
    (Fin.cases cubic2_row37
    (Fin.cases cubic2_row38
    (Fin.cases cubic2_row39
    (Fin.cases cubic2_row40
    (Fin.cases cubic2_row41
    (Fin.cases cubic2_row42
    (Fin.cases cubic2_row43
    (Fin.cases cubic2_row44
    (Fin.cases cubic2_row45
    (Fin.cases cubic2_row46
    (Fin.cases cubic2_row47
    (Fin.cases cubic2_row48
    (Fin.cases cubic2_row49
    (Fin.cases cubic2_row50
    (Fin.cases cubic2_row51
    (Fin.cases cubic2_row52
    (Fin.cases cubic2_row53
    (Fin.cases cubic2_row54
    (Fin.cases cubic2_row55
    (Fin.cases cubic2_row56
    (Fin.cases cubic2_row57
    (Fin.cases cubic2_row58
    (Fin.cases cubic2_row59
    (Fin.cases cubic2_row60
    (Fin.cases cubic2_row61
    (Fin.cases cubic2_row62
    (Fin.cases cubic2_row63
    (Fin.cases cubic2_row64
    (Fin.cases cubic2_row65
    (Fin.cases cubic2_row66
    (Fin.cases cubic2_row67
    (Fin.cases cubic2_row68
    (Fin.cases cubic2_row69
    (Fin.cases cubic2_row70
    (Fin.cases cubic2_row71
    (Fin.cases cubic2_row72
    (Fin.cases cubic2_row73
    (Fin.cases cubic2_row74
    (Fin.cases cubic2_row75
    (Fin.cases cubic2_row76
    (Fin.cases cubic2_row77
    (Fin.cases cubic2_row78
    (Fin.cases cubic2_row79
    (Fin.cases cubic2_row80
    (Fin.cases cubic2_row81
    (Fin.cases cubic2_row82
    (Fin.cases cubic2_row83
    (Fin.cases cubic2_row84
    (Fin.cases cubic2_row85
    (Fin.cases cubic2_row86
    (Fin.cases cubic2_row87
    (Fin.cases cubic2_row88
    (Fin.cases cubic2_row89
    (Fin.cases cubic2_row90
    (Fin.cases cubic2_row91
    (Fin.cases cubic2_row92
    (Fin.cases cubic2_row93
    (Fin.cases cubic2_row94
    (Fin.cases cubic2_row95
    (Fin.cases cubic2_row96
    (Fin.cases cubic2_row97
    (Fin.cases cubic2_row98
    (Fin.cases cubic2_row99
    (Fin.cases cubic2_row100
    (Fin.cases cubic2_row101
    (Fin.cases cubic2_row102
    (Fin.cases cubic2_row103
    (Fin.cases cubic2_row104
    (Fin.cases cubic2_row105
    (Fin.cases cubic2_row106
    (Fin.cases cubic2_row107
    (Fin.cases cubic2_row108
    (Fin.cases cubic2_row109
    (Fin.cases cubic2_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_cubic2 : cubicMatrix * cubicMatrix = cubic2Matrix :=
  decode_mul _ _ _ cubic_small cubic_small cubic2_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
