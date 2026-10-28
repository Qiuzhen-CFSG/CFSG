module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: cubic2 times cubic

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
private theorem cube_row0 :
    digitsEq 111 (rowProduct (cubic2Rows 0) cubicRows 111) (oneRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row1 :
    digitsEq 111 (rowProduct (cubic2Rows 1) cubicRows 111) (oneRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row2 :
    digitsEq 111 (rowProduct (cubic2Rows 2) cubicRows 111) (oneRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row3 :
    digitsEq 111 (rowProduct (cubic2Rows 3) cubicRows 111) (oneRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row4 :
    digitsEq 111 (rowProduct (cubic2Rows 4) cubicRows 111) (oneRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row5 :
    digitsEq 111 (rowProduct (cubic2Rows 5) cubicRows 111) (oneRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row6 :
    digitsEq 111 (rowProduct (cubic2Rows 6) cubicRows 111) (oneRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row7 :
    digitsEq 111 (rowProduct (cubic2Rows 7) cubicRows 111) (oneRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row8 :
    digitsEq 111 (rowProduct (cubic2Rows 8) cubicRows 111) (oneRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row9 :
    digitsEq 111 (rowProduct (cubic2Rows 9) cubicRows 111) (oneRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row10 :
    digitsEq 111 (rowProduct (cubic2Rows 10) cubicRows 111) (oneRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row11 :
    digitsEq 111 (rowProduct (cubic2Rows 11) cubicRows 111) (oneRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row12 :
    digitsEq 111 (rowProduct (cubic2Rows 12) cubicRows 111) (oneRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row13 :
    digitsEq 111 (rowProduct (cubic2Rows 13) cubicRows 111) (oneRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row14 :
    digitsEq 111 (rowProduct (cubic2Rows 14) cubicRows 111) (oneRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row15 :
    digitsEq 111 (rowProduct (cubic2Rows 15) cubicRows 111) (oneRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row16 :
    digitsEq 111 (rowProduct (cubic2Rows 16) cubicRows 111) (oneRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row17 :
    digitsEq 111 (rowProduct (cubic2Rows 17) cubicRows 111) (oneRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row18 :
    digitsEq 111 (rowProduct (cubic2Rows 18) cubicRows 111) (oneRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row19 :
    digitsEq 111 (rowProduct (cubic2Rows 19) cubicRows 111) (oneRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row20 :
    digitsEq 111 (rowProduct (cubic2Rows 20) cubicRows 111) (oneRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row21 :
    digitsEq 111 (rowProduct (cubic2Rows 21) cubicRows 111) (oneRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row22 :
    digitsEq 111 (rowProduct (cubic2Rows 22) cubicRows 111) (oneRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row23 :
    digitsEq 111 (rowProduct (cubic2Rows 23) cubicRows 111) (oneRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row24 :
    digitsEq 111 (rowProduct (cubic2Rows 24) cubicRows 111) (oneRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row25 :
    digitsEq 111 (rowProduct (cubic2Rows 25) cubicRows 111) (oneRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row26 :
    digitsEq 111 (rowProduct (cubic2Rows 26) cubicRows 111) (oneRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row27 :
    digitsEq 111 (rowProduct (cubic2Rows 27) cubicRows 111) (oneRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row28 :
    digitsEq 111 (rowProduct (cubic2Rows 28) cubicRows 111) (oneRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row29 :
    digitsEq 111 (rowProduct (cubic2Rows 29) cubicRows 111) (oneRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row30 :
    digitsEq 111 (rowProduct (cubic2Rows 30) cubicRows 111) (oneRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row31 :
    digitsEq 111 (rowProduct (cubic2Rows 31) cubicRows 111) (oneRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row32 :
    digitsEq 111 (rowProduct (cubic2Rows 32) cubicRows 111) (oneRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row33 :
    digitsEq 111 (rowProduct (cubic2Rows 33) cubicRows 111) (oneRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row34 :
    digitsEq 111 (rowProduct (cubic2Rows 34) cubicRows 111) (oneRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row35 :
    digitsEq 111 (rowProduct (cubic2Rows 35) cubicRows 111) (oneRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row36 :
    digitsEq 111 (rowProduct (cubic2Rows 36) cubicRows 111) (oneRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row37 :
    digitsEq 111 (rowProduct (cubic2Rows 37) cubicRows 111) (oneRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row38 :
    digitsEq 111 (rowProduct (cubic2Rows 38) cubicRows 111) (oneRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row39 :
    digitsEq 111 (rowProduct (cubic2Rows 39) cubicRows 111) (oneRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row40 :
    digitsEq 111 (rowProduct (cubic2Rows 40) cubicRows 111) (oneRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row41 :
    digitsEq 111 (rowProduct (cubic2Rows 41) cubicRows 111) (oneRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row42 :
    digitsEq 111 (rowProduct (cubic2Rows 42) cubicRows 111) (oneRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row43 :
    digitsEq 111 (rowProduct (cubic2Rows 43) cubicRows 111) (oneRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row44 :
    digitsEq 111 (rowProduct (cubic2Rows 44) cubicRows 111) (oneRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row45 :
    digitsEq 111 (rowProduct (cubic2Rows 45) cubicRows 111) (oneRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row46 :
    digitsEq 111 (rowProduct (cubic2Rows 46) cubicRows 111) (oneRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row47 :
    digitsEq 111 (rowProduct (cubic2Rows 47) cubicRows 111) (oneRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row48 :
    digitsEq 111 (rowProduct (cubic2Rows 48) cubicRows 111) (oneRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row49 :
    digitsEq 111 (rowProduct (cubic2Rows 49) cubicRows 111) (oneRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row50 :
    digitsEq 111 (rowProduct (cubic2Rows 50) cubicRows 111) (oneRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row51 :
    digitsEq 111 (rowProduct (cubic2Rows 51) cubicRows 111) (oneRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row52 :
    digitsEq 111 (rowProduct (cubic2Rows 52) cubicRows 111) (oneRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row53 :
    digitsEq 111 (rowProduct (cubic2Rows 53) cubicRows 111) (oneRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row54 :
    digitsEq 111 (rowProduct (cubic2Rows 54) cubicRows 111) (oneRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row55 :
    digitsEq 111 (rowProduct (cubic2Rows 55) cubicRows 111) (oneRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row56 :
    digitsEq 111 (rowProduct (cubic2Rows 56) cubicRows 111) (oneRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row57 :
    digitsEq 111 (rowProduct (cubic2Rows 57) cubicRows 111) (oneRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row58 :
    digitsEq 111 (rowProduct (cubic2Rows 58) cubicRows 111) (oneRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row59 :
    digitsEq 111 (rowProduct (cubic2Rows 59) cubicRows 111) (oneRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row60 :
    digitsEq 111 (rowProduct (cubic2Rows 60) cubicRows 111) (oneRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row61 :
    digitsEq 111 (rowProduct (cubic2Rows 61) cubicRows 111) (oneRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row62 :
    digitsEq 111 (rowProduct (cubic2Rows 62) cubicRows 111) (oneRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row63 :
    digitsEq 111 (rowProduct (cubic2Rows 63) cubicRows 111) (oneRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row64 :
    digitsEq 111 (rowProduct (cubic2Rows 64) cubicRows 111) (oneRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row65 :
    digitsEq 111 (rowProduct (cubic2Rows 65) cubicRows 111) (oneRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row66 :
    digitsEq 111 (rowProduct (cubic2Rows 66) cubicRows 111) (oneRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row67 :
    digitsEq 111 (rowProduct (cubic2Rows 67) cubicRows 111) (oneRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row68 :
    digitsEq 111 (rowProduct (cubic2Rows 68) cubicRows 111) (oneRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row69 :
    digitsEq 111 (rowProduct (cubic2Rows 69) cubicRows 111) (oneRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row70 :
    digitsEq 111 (rowProduct (cubic2Rows 70) cubicRows 111) (oneRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row71 :
    digitsEq 111 (rowProduct (cubic2Rows 71) cubicRows 111) (oneRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row72 :
    digitsEq 111 (rowProduct (cubic2Rows 72) cubicRows 111) (oneRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row73 :
    digitsEq 111 (rowProduct (cubic2Rows 73) cubicRows 111) (oneRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row74 :
    digitsEq 111 (rowProduct (cubic2Rows 74) cubicRows 111) (oneRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row75 :
    digitsEq 111 (rowProduct (cubic2Rows 75) cubicRows 111) (oneRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row76 :
    digitsEq 111 (rowProduct (cubic2Rows 76) cubicRows 111) (oneRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row77 :
    digitsEq 111 (rowProduct (cubic2Rows 77) cubicRows 111) (oneRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row78 :
    digitsEq 111 (rowProduct (cubic2Rows 78) cubicRows 111) (oneRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row79 :
    digitsEq 111 (rowProduct (cubic2Rows 79) cubicRows 111) (oneRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row80 :
    digitsEq 111 (rowProduct (cubic2Rows 80) cubicRows 111) (oneRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row81 :
    digitsEq 111 (rowProduct (cubic2Rows 81) cubicRows 111) (oneRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row82 :
    digitsEq 111 (rowProduct (cubic2Rows 82) cubicRows 111) (oneRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row83 :
    digitsEq 111 (rowProduct (cubic2Rows 83) cubicRows 111) (oneRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row84 :
    digitsEq 111 (rowProduct (cubic2Rows 84) cubicRows 111) (oneRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row85 :
    digitsEq 111 (rowProduct (cubic2Rows 85) cubicRows 111) (oneRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row86 :
    digitsEq 111 (rowProduct (cubic2Rows 86) cubicRows 111) (oneRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row87 :
    digitsEq 111 (rowProduct (cubic2Rows 87) cubicRows 111) (oneRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row88 :
    digitsEq 111 (rowProduct (cubic2Rows 88) cubicRows 111) (oneRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row89 :
    digitsEq 111 (rowProduct (cubic2Rows 89) cubicRows 111) (oneRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row90 :
    digitsEq 111 (rowProduct (cubic2Rows 90) cubicRows 111) (oneRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row91 :
    digitsEq 111 (rowProduct (cubic2Rows 91) cubicRows 111) (oneRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row92 :
    digitsEq 111 (rowProduct (cubic2Rows 92) cubicRows 111) (oneRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row93 :
    digitsEq 111 (rowProduct (cubic2Rows 93) cubicRows 111) (oneRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row94 :
    digitsEq 111 (rowProduct (cubic2Rows 94) cubicRows 111) (oneRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row95 :
    digitsEq 111 (rowProduct (cubic2Rows 95) cubicRows 111) (oneRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row96 :
    digitsEq 111 (rowProduct (cubic2Rows 96) cubicRows 111) (oneRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row97 :
    digitsEq 111 (rowProduct (cubic2Rows 97) cubicRows 111) (oneRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row98 :
    digitsEq 111 (rowProduct (cubic2Rows 98) cubicRows 111) (oneRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row99 :
    digitsEq 111 (rowProduct (cubic2Rows 99) cubicRows 111) (oneRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row100 :
    digitsEq 111 (rowProduct (cubic2Rows 100) cubicRows 111) (oneRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row101 :
    digitsEq 111 (rowProduct (cubic2Rows 101) cubicRows 111) (oneRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row102 :
    digitsEq 111 (rowProduct (cubic2Rows 102) cubicRows 111) (oneRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row103 :
    digitsEq 111 (rowProduct (cubic2Rows 103) cubicRows 111) (oneRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row104 :
    digitsEq 111 (rowProduct (cubic2Rows 104) cubicRows 111) (oneRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row105 :
    digitsEq 111 (rowProduct (cubic2Rows 105) cubicRows 111) (oneRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row106 :
    digitsEq 111 (rowProduct (cubic2Rows 106) cubicRows 111) (oneRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row107 :
    digitsEq 111 (rowProduct (cubic2Rows 107) cubicRows 111) (oneRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row108 :
    digitsEq 111 (rowProduct (cubic2Rows 108) cubicRows 111) (oneRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row109 :
    digitsEq 111 (rowProduct (cubic2Rows 109) cubicRows 111) (oneRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_row110 :
    digitsEq 111 (rowProduct (cubic2Rows 110) cubicRows 111) (oneRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cube_rows : ∀ i,
    digitsEq 111 (rowProduct (cubic2Rows i) cubicRows 111) (oneRows i) = true :=
  (Fin.cases cube_row0
    (Fin.cases cube_row1
    (Fin.cases cube_row2
    (Fin.cases cube_row3
    (Fin.cases cube_row4
    (Fin.cases cube_row5
    (Fin.cases cube_row6
    (Fin.cases cube_row7
    (Fin.cases cube_row8
    (Fin.cases cube_row9
    (Fin.cases cube_row10
    (Fin.cases cube_row11
    (Fin.cases cube_row12
    (Fin.cases cube_row13
    (Fin.cases cube_row14
    (Fin.cases cube_row15
    (Fin.cases cube_row16
    (Fin.cases cube_row17
    (Fin.cases cube_row18
    (Fin.cases cube_row19
    (Fin.cases cube_row20
    (Fin.cases cube_row21
    (Fin.cases cube_row22
    (Fin.cases cube_row23
    (Fin.cases cube_row24
    (Fin.cases cube_row25
    (Fin.cases cube_row26
    (Fin.cases cube_row27
    (Fin.cases cube_row28
    (Fin.cases cube_row29
    (Fin.cases cube_row30
    (Fin.cases cube_row31
    (Fin.cases cube_row32
    (Fin.cases cube_row33
    (Fin.cases cube_row34
    (Fin.cases cube_row35
    (Fin.cases cube_row36
    (Fin.cases cube_row37
    (Fin.cases cube_row38
    (Fin.cases cube_row39
    (Fin.cases cube_row40
    (Fin.cases cube_row41
    (Fin.cases cube_row42
    (Fin.cases cube_row43
    (Fin.cases cube_row44
    (Fin.cases cube_row45
    (Fin.cases cube_row46
    (Fin.cases cube_row47
    (Fin.cases cube_row48
    (Fin.cases cube_row49
    (Fin.cases cube_row50
    (Fin.cases cube_row51
    (Fin.cases cube_row52
    (Fin.cases cube_row53
    (Fin.cases cube_row54
    (Fin.cases cube_row55
    (Fin.cases cube_row56
    (Fin.cases cube_row57
    (Fin.cases cube_row58
    (Fin.cases cube_row59
    (Fin.cases cube_row60
    (Fin.cases cube_row61
    (Fin.cases cube_row62
    (Fin.cases cube_row63
    (Fin.cases cube_row64
    (Fin.cases cube_row65
    (Fin.cases cube_row66
    (Fin.cases cube_row67
    (Fin.cases cube_row68
    (Fin.cases cube_row69
    (Fin.cases cube_row70
    (Fin.cases cube_row71
    (Fin.cases cube_row72
    (Fin.cases cube_row73
    (Fin.cases cube_row74
    (Fin.cases cube_row75
    (Fin.cases cube_row76
    (Fin.cases cube_row77
    (Fin.cases cube_row78
    (Fin.cases cube_row79
    (Fin.cases cube_row80
    (Fin.cases cube_row81
    (Fin.cases cube_row82
    (Fin.cases cube_row83
    (Fin.cases cube_row84
    (Fin.cases cube_row85
    (Fin.cases cube_row86
    (Fin.cases cube_row87
    (Fin.cases cube_row88
    (Fin.cases cube_row89
    (Fin.cases cube_row90
    (Fin.cases cube_row91
    (Fin.cases cube_row92
    (Fin.cases cube_row93
    (Fin.cases cube_row94
    (Fin.cases cube_row95
    (Fin.cases cube_row96
    (Fin.cases cube_row97
    (Fin.cases cube_row98
    (Fin.cases cube_row99
    (Fin.cases cube_row100
    (Fin.cases cube_row101
    (Fin.cases cube_row102
    (Fin.cases cube_row103
    (Fin.cases cube_row104
    (Fin.cases cube_row105
    (Fin.cases cube_row106
    (Fin.cases cube_row107
    (Fin.cases cube_row108
    (Fin.cases cube_row109
    (Fin.cases cube_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_cube : cubic2Matrix * cubicMatrix = oneMatrix :=
  decode_mul _ _ _ cubic2_small cubic_small cube_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
