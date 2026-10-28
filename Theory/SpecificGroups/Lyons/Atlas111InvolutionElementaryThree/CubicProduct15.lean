module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: second times cubic

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
private theorem pair01rev_row0 :
    digitsEq 111 (rowProduct (secondRows 0) cubicRows 111) (pair01Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row1 :
    digitsEq 111 (rowProduct (secondRows 1) cubicRows 111) (pair01Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row2 :
    digitsEq 111 (rowProduct (secondRows 2) cubicRows 111) (pair01Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row3 :
    digitsEq 111 (rowProduct (secondRows 3) cubicRows 111) (pair01Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row4 :
    digitsEq 111 (rowProduct (secondRows 4) cubicRows 111) (pair01Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row5 :
    digitsEq 111 (rowProduct (secondRows 5) cubicRows 111) (pair01Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row6 :
    digitsEq 111 (rowProduct (secondRows 6) cubicRows 111) (pair01Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row7 :
    digitsEq 111 (rowProduct (secondRows 7) cubicRows 111) (pair01Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row8 :
    digitsEq 111 (rowProduct (secondRows 8) cubicRows 111) (pair01Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row9 :
    digitsEq 111 (rowProduct (secondRows 9) cubicRows 111) (pair01Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row10 :
    digitsEq 111 (rowProduct (secondRows 10) cubicRows 111) (pair01Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row11 :
    digitsEq 111 (rowProduct (secondRows 11) cubicRows 111) (pair01Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row12 :
    digitsEq 111 (rowProduct (secondRows 12) cubicRows 111) (pair01Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row13 :
    digitsEq 111 (rowProduct (secondRows 13) cubicRows 111) (pair01Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row14 :
    digitsEq 111 (rowProduct (secondRows 14) cubicRows 111) (pair01Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row15 :
    digitsEq 111 (rowProduct (secondRows 15) cubicRows 111) (pair01Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row16 :
    digitsEq 111 (rowProduct (secondRows 16) cubicRows 111) (pair01Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row17 :
    digitsEq 111 (rowProduct (secondRows 17) cubicRows 111) (pair01Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row18 :
    digitsEq 111 (rowProduct (secondRows 18) cubicRows 111) (pair01Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row19 :
    digitsEq 111 (rowProduct (secondRows 19) cubicRows 111) (pair01Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row20 :
    digitsEq 111 (rowProduct (secondRows 20) cubicRows 111) (pair01Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row21 :
    digitsEq 111 (rowProduct (secondRows 21) cubicRows 111) (pair01Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row22 :
    digitsEq 111 (rowProduct (secondRows 22) cubicRows 111) (pair01Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row23 :
    digitsEq 111 (rowProduct (secondRows 23) cubicRows 111) (pair01Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row24 :
    digitsEq 111 (rowProduct (secondRows 24) cubicRows 111) (pair01Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row25 :
    digitsEq 111 (rowProduct (secondRows 25) cubicRows 111) (pair01Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row26 :
    digitsEq 111 (rowProduct (secondRows 26) cubicRows 111) (pair01Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row27 :
    digitsEq 111 (rowProduct (secondRows 27) cubicRows 111) (pair01Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row28 :
    digitsEq 111 (rowProduct (secondRows 28) cubicRows 111) (pair01Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row29 :
    digitsEq 111 (rowProduct (secondRows 29) cubicRows 111) (pair01Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row30 :
    digitsEq 111 (rowProduct (secondRows 30) cubicRows 111) (pair01Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row31 :
    digitsEq 111 (rowProduct (secondRows 31) cubicRows 111) (pair01Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row32 :
    digitsEq 111 (rowProduct (secondRows 32) cubicRows 111) (pair01Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row33 :
    digitsEq 111 (rowProduct (secondRows 33) cubicRows 111) (pair01Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row34 :
    digitsEq 111 (rowProduct (secondRows 34) cubicRows 111) (pair01Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row35 :
    digitsEq 111 (rowProduct (secondRows 35) cubicRows 111) (pair01Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row36 :
    digitsEq 111 (rowProduct (secondRows 36) cubicRows 111) (pair01Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row37 :
    digitsEq 111 (rowProduct (secondRows 37) cubicRows 111) (pair01Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row38 :
    digitsEq 111 (rowProduct (secondRows 38) cubicRows 111) (pair01Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row39 :
    digitsEq 111 (rowProduct (secondRows 39) cubicRows 111) (pair01Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row40 :
    digitsEq 111 (rowProduct (secondRows 40) cubicRows 111) (pair01Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row41 :
    digitsEq 111 (rowProduct (secondRows 41) cubicRows 111) (pair01Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row42 :
    digitsEq 111 (rowProduct (secondRows 42) cubicRows 111) (pair01Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row43 :
    digitsEq 111 (rowProduct (secondRows 43) cubicRows 111) (pair01Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row44 :
    digitsEq 111 (rowProduct (secondRows 44) cubicRows 111) (pair01Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row45 :
    digitsEq 111 (rowProduct (secondRows 45) cubicRows 111) (pair01Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row46 :
    digitsEq 111 (rowProduct (secondRows 46) cubicRows 111) (pair01Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row47 :
    digitsEq 111 (rowProduct (secondRows 47) cubicRows 111) (pair01Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row48 :
    digitsEq 111 (rowProduct (secondRows 48) cubicRows 111) (pair01Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row49 :
    digitsEq 111 (rowProduct (secondRows 49) cubicRows 111) (pair01Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row50 :
    digitsEq 111 (rowProduct (secondRows 50) cubicRows 111) (pair01Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row51 :
    digitsEq 111 (rowProduct (secondRows 51) cubicRows 111) (pair01Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row52 :
    digitsEq 111 (rowProduct (secondRows 52) cubicRows 111) (pair01Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row53 :
    digitsEq 111 (rowProduct (secondRows 53) cubicRows 111) (pair01Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row54 :
    digitsEq 111 (rowProduct (secondRows 54) cubicRows 111) (pair01Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row55 :
    digitsEq 111 (rowProduct (secondRows 55) cubicRows 111) (pair01Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row56 :
    digitsEq 111 (rowProduct (secondRows 56) cubicRows 111) (pair01Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row57 :
    digitsEq 111 (rowProduct (secondRows 57) cubicRows 111) (pair01Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row58 :
    digitsEq 111 (rowProduct (secondRows 58) cubicRows 111) (pair01Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row59 :
    digitsEq 111 (rowProduct (secondRows 59) cubicRows 111) (pair01Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row60 :
    digitsEq 111 (rowProduct (secondRows 60) cubicRows 111) (pair01Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row61 :
    digitsEq 111 (rowProduct (secondRows 61) cubicRows 111) (pair01Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row62 :
    digitsEq 111 (rowProduct (secondRows 62) cubicRows 111) (pair01Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row63 :
    digitsEq 111 (rowProduct (secondRows 63) cubicRows 111) (pair01Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row64 :
    digitsEq 111 (rowProduct (secondRows 64) cubicRows 111) (pair01Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row65 :
    digitsEq 111 (rowProduct (secondRows 65) cubicRows 111) (pair01Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row66 :
    digitsEq 111 (rowProduct (secondRows 66) cubicRows 111) (pair01Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row67 :
    digitsEq 111 (rowProduct (secondRows 67) cubicRows 111) (pair01Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row68 :
    digitsEq 111 (rowProduct (secondRows 68) cubicRows 111) (pair01Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row69 :
    digitsEq 111 (rowProduct (secondRows 69) cubicRows 111) (pair01Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row70 :
    digitsEq 111 (rowProduct (secondRows 70) cubicRows 111) (pair01Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row71 :
    digitsEq 111 (rowProduct (secondRows 71) cubicRows 111) (pair01Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row72 :
    digitsEq 111 (rowProduct (secondRows 72) cubicRows 111) (pair01Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row73 :
    digitsEq 111 (rowProduct (secondRows 73) cubicRows 111) (pair01Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row74 :
    digitsEq 111 (rowProduct (secondRows 74) cubicRows 111) (pair01Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row75 :
    digitsEq 111 (rowProduct (secondRows 75) cubicRows 111) (pair01Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row76 :
    digitsEq 111 (rowProduct (secondRows 76) cubicRows 111) (pair01Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row77 :
    digitsEq 111 (rowProduct (secondRows 77) cubicRows 111) (pair01Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row78 :
    digitsEq 111 (rowProduct (secondRows 78) cubicRows 111) (pair01Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row79 :
    digitsEq 111 (rowProduct (secondRows 79) cubicRows 111) (pair01Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row80 :
    digitsEq 111 (rowProduct (secondRows 80) cubicRows 111) (pair01Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row81 :
    digitsEq 111 (rowProduct (secondRows 81) cubicRows 111) (pair01Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row82 :
    digitsEq 111 (rowProduct (secondRows 82) cubicRows 111) (pair01Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row83 :
    digitsEq 111 (rowProduct (secondRows 83) cubicRows 111) (pair01Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row84 :
    digitsEq 111 (rowProduct (secondRows 84) cubicRows 111) (pair01Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row85 :
    digitsEq 111 (rowProduct (secondRows 85) cubicRows 111) (pair01Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row86 :
    digitsEq 111 (rowProduct (secondRows 86) cubicRows 111) (pair01Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row87 :
    digitsEq 111 (rowProduct (secondRows 87) cubicRows 111) (pair01Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row88 :
    digitsEq 111 (rowProduct (secondRows 88) cubicRows 111) (pair01Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row89 :
    digitsEq 111 (rowProduct (secondRows 89) cubicRows 111) (pair01Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row90 :
    digitsEq 111 (rowProduct (secondRows 90) cubicRows 111) (pair01Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row91 :
    digitsEq 111 (rowProduct (secondRows 91) cubicRows 111) (pair01Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row92 :
    digitsEq 111 (rowProduct (secondRows 92) cubicRows 111) (pair01Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row93 :
    digitsEq 111 (rowProduct (secondRows 93) cubicRows 111) (pair01Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row94 :
    digitsEq 111 (rowProduct (secondRows 94) cubicRows 111) (pair01Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row95 :
    digitsEq 111 (rowProduct (secondRows 95) cubicRows 111) (pair01Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row96 :
    digitsEq 111 (rowProduct (secondRows 96) cubicRows 111) (pair01Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row97 :
    digitsEq 111 (rowProduct (secondRows 97) cubicRows 111) (pair01Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row98 :
    digitsEq 111 (rowProduct (secondRows 98) cubicRows 111) (pair01Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row99 :
    digitsEq 111 (rowProduct (secondRows 99) cubicRows 111) (pair01Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row100 :
    digitsEq 111 (rowProduct (secondRows 100) cubicRows 111) (pair01Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row101 :
    digitsEq 111 (rowProduct (secondRows 101) cubicRows 111) (pair01Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row102 :
    digitsEq 111 (rowProduct (secondRows 102) cubicRows 111) (pair01Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row103 :
    digitsEq 111 (rowProduct (secondRows 103) cubicRows 111) (pair01Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row104 :
    digitsEq 111 (rowProduct (secondRows 104) cubicRows 111) (pair01Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row105 :
    digitsEq 111 (rowProduct (secondRows 105) cubicRows 111) (pair01Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row106 :
    digitsEq 111 (rowProduct (secondRows 106) cubicRows 111) (pair01Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row107 :
    digitsEq 111 (rowProduct (secondRows 107) cubicRows 111) (pair01Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row108 :
    digitsEq 111 (rowProduct (secondRows 108) cubicRows 111) (pair01Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row109 :
    digitsEq 111 (rowProduct (secondRows 109) cubicRows 111) (pair01Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_row110 :
    digitsEq 111 (rowProduct (secondRows 110) cubicRows 111) (pair01Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01rev_rows : ∀ i,
    digitsEq 111 (rowProduct (secondRows i) cubicRows 111) (pair01Rows i) = true :=
  (Fin.cases pair01rev_row0
    (Fin.cases pair01rev_row1
    (Fin.cases pair01rev_row2
    (Fin.cases pair01rev_row3
    (Fin.cases pair01rev_row4
    (Fin.cases pair01rev_row5
    (Fin.cases pair01rev_row6
    (Fin.cases pair01rev_row7
    (Fin.cases pair01rev_row8
    (Fin.cases pair01rev_row9
    (Fin.cases pair01rev_row10
    (Fin.cases pair01rev_row11
    (Fin.cases pair01rev_row12
    (Fin.cases pair01rev_row13
    (Fin.cases pair01rev_row14
    (Fin.cases pair01rev_row15
    (Fin.cases pair01rev_row16
    (Fin.cases pair01rev_row17
    (Fin.cases pair01rev_row18
    (Fin.cases pair01rev_row19
    (Fin.cases pair01rev_row20
    (Fin.cases pair01rev_row21
    (Fin.cases pair01rev_row22
    (Fin.cases pair01rev_row23
    (Fin.cases pair01rev_row24
    (Fin.cases pair01rev_row25
    (Fin.cases pair01rev_row26
    (Fin.cases pair01rev_row27
    (Fin.cases pair01rev_row28
    (Fin.cases pair01rev_row29
    (Fin.cases pair01rev_row30
    (Fin.cases pair01rev_row31
    (Fin.cases pair01rev_row32
    (Fin.cases pair01rev_row33
    (Fin.cases pair01rev_row34
    (Fin.cases pair01rev_row35
    (Fin.cases pair01rev_row36
    (Fin.cases pair01rev_row37
    (Fin.cases pair01rev_row38
    (Fin.cases pair01rev_row39
    (Fin.cases pair01rev_row40
    (Fin.cases pair01rev_row41
    (Fin.cases pair01rev_row42
    (Fin.cases pair01rev_row43
    (Fin.cases pair01rev_row44
    (Fin.cases pair01rev_row45
    (Fin.cases pair01rev_row46
    (Fin.cases pair01rev_row47
    (Fin.cases pair01rev_row48
    (Fin.cases pair01rev_row49
    (Fin.cases pair01rev_row50
    (Fin.cases pair01rev_row51
    (Fin.cases pair01rev_row52
    (Fin.cases pair01rev_row53
    (Fin.cases pair01rev_row54
    (Fin.cases pair01rev_row55
    (Fin.cases pair01rev_row56
    (Fin.cases pair01rev_row57
    (Fin.cases pair01rev_row58
    (Fin.cases pair01rev_row59
    (Fin.cases pair01rev_row60
    (Fin.cases pair01rev_row61
    (Fin.cases pair01rev_row62
    (Fin.cases pair01rev_row63
    (Fin.cases pair01rev_row64
    (Fin.cases pair01rev_row65
    (Fin.cases pair01rev_row66
    (Fin.cases pair01rev_row67
    (Fin.cases pair01rev_row68
    (Fin.cases pair01rev_row69
    (Fin.cases pair01rev_row70
    (Fin.cases pair01rev_row71
    (Fin.cases pair01rev_row72
    (Fin.cases pair01rev_row73
    (Fin.cases pair01rev_row74
    (Fin.cases pair01rev_row75
    (Fin.cases pair01rev_row76
    (Fin.cases pair01rev_row77
    (Fin.cases pair01rev_row78
    (Fin.cases pair01rev_row79
    (Fin.cases pair01rev_row80
    (Fin.cases pair01rev_row81
    (Fin.cases pair01rev_row82
    (Fin.cases pair01rev_row83
    (Fin.cases pair01rev_row84
    (Fin.cases pair01rev_row85
    (Fin.cases pair01rev_row86
    (Fin.cases pair01rev_row87
    (Fin.cases pair01rev_row88
    (Fin.cases pair01rev_row89
    (Fin.cases pair01rev_row90
    (Fin.cases pair01rev_row91
    (Fin.cases pair01rev_row92
    (Fin.cases pair01rev_row93
    (Fin.cases pair01rev_row94
    (Fin.cases pair01rev_row95
    (Fin.cases pair01rev_row96
    (Fin.cases pair01rev_row97
    (Fin.cases pair01rev_row98
    (Fin.cases pair01rev_row99
    (Fin.cases pair01rev_row100
    (Fin.cases pair01rev_row101
    (Fin.cases pair01rev_row102
    (Fin.cases pair01rev_row103
    (Fin.cases pair01rev_row104
    (Fin.cases pair01rev_row105
    (Fin.cases pair01rev_row106
    (Fin.cases pair01rev_row107
    (Fin.cases pair01rev_row108
    (Fin.cases pair01rev_row109
    (Fin.cases pair01rev_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_pair01rev : secondMatrix * cubicMatrix = pair01Matrix :=
  decode_mul _ _ _ second_small cubic_small pair01rev_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
