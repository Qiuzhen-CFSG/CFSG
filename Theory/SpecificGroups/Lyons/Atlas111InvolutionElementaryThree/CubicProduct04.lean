module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: seed2 times seed2

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
private theorem cubic_row0 :
    digitsEq 111 (rowProduct (seed2Rows 0) seed2Rows 111) (cubicRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row1 :
    digitsEq 111 (rowProduct (seed2Rows 1) seed2Rows 111) (cubicRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row2 :
    digitsEq 111 (rowProduct (seed2Rows 2) seed2Rows 111) (cubicRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row3 :
    digitsEq 111 (rowProduct (seed2Rows 3) seed2Rows 111) (cubicRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row4 :
    digitsEq 111 (rowProduct (seed2Rows 4) seed2Rows 111) (cubicRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row5 :
    digitsEq 111 (rowProduct (seed2Rows 5) seed2Rows 111) (cubicRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row6 :
    digitsEq 111 (rowProduct (seed2Rows 6) seed2Rows 111) (cubicRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row7 :
    digitsEq 111 (rowProduct (seed2Rows 7) seed2Rows 111) (cubicRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row8 :
    digitsEq 111 (rowProduct (seed2Rows 8) seed2Rows 111) (cubicRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row9 :
    digitsEq 111 (rowProduct (seed2Rows 9) seed2Rows 111) (cubicRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row10 :
    digitsEq 111 (rowProduct (seed2Rows 10) seed2Rows 111) (cubicRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row11 :
    digitsEq 111 (rowProduct (seed2Rows 11) seed2Rows 111) (cubicRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row12 :
    digitsEq 111 (rowProduct (seed2Rows 12) seed2Rows 111) (cubicRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row13 :
    digitsEq 111 (rowProduct (seed2Rows 13) seed2Rows 111) (cubicRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row14 :
    digitsEq 111 (rowProduct (seed2Rows 14) seed2Rows 111) (cubicRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row15 :
    digitsEq 111 (rowProduct (seed2Rows 15) seed2Rows 111) (cubicRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row16 :
    digitsEq 111 (rowProduct (seed2Rows 16) seed2Rows 111) (cubicRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row17 :
    digitsEq 111 (rowProduct (seed2Rows 17) seed2Rows 111) (cubicRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row18 :
    digitsEq 111 (rowProduct (seed2Rows 18) seed2Rows 111) (cubicRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row19 :
    digitsEq 111 (rowProduct (seed2Rows 19) seed2Rows 111) (cubicRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row20 :
    digitsEq 111 (rowProduct (seed2Rows 20) seed2Rows 111) (cubicRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row21 :
    digitsEq 111 (rowProduct (seed2Rows 21) seed2Rows 111) (cubicRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row22 :
    digitsEq 111 (rowProduct (seed2Rows 22) seed2Rows 111) (cubicRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row23 :
    digitsEq 111 (rowProduct (seed2Rows 23) seed2Rows 111) (cubicRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row24 :
    digitsEq 111 (rowProduct (seed2Rows 24) seed2Rows 111) (cubicRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row25 :
    digitsEq 111 (rowProduct (seed2Rows 25) seed2Rows 111) (cubicRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row26 :
    digitsEq 111 (rowProduct (seed2Rows 26) seed2Rows 111) (cubicRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row27 :
    digitsEq 111 (rowProduct (seed2Rows 27) seed2Rows 111) (cubicRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row28 :
    digitsEq 111 (rowProduct (seed2Rows 28) seed2Rows 111) (cubicRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row29 :
    digitsEq 111 (rowProduct (seed2Rows 29) seed2Rows 111) (cubicRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row30 :
    digitsEq 111 (rowProduct (seed2Rows 30) seed2Rows 111) (cubicRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row31 :
    digitsEq 111 (rowProduct (seed2Rows 31) seed2Rows 111) (cubicRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row32 :
    digitsEq 111 (rowProduct (seed2Rows 32) seed2Rows 111) (cubicRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row33 :
    digitsEq 111 (rowProduct (seed2Rows 33) seed2Rows 111) (cubicRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row34 :
    digitsEq 111 (rowProduct (seed2Rows 34) seed2Rows 111) (cubicRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row35 :
    digitsEq 111 (rowProduct (seed2Rows 35) seed2Rows 111) (cubicRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row36 :
    digitsEq 111 (rowProduct (seed2Rows 36) seed2Rows 111) (cubicRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row37 :
    digitsEq 111 (rowProduct (seed2Rows 37) seed2Rows 111) (cubicRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row38 :
    digitsEq 111 (rowProduct (seed2Rows 38) seed2Rows 111) (cubicRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row39 :
    digitsEq 111 (rowProduct (seed2Rows 39) seed2Rows 111) (cubicRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row40 :
    digitsEq 111 (rowProduct (seed2Rows 40) seed2Rows 111) (cubicRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row41 :
    digitsEq 111 (rowProduct (seed2Rows 41) seed2Rows 111) (cubicRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row42 :
    digitsEq 111 (rowProduct (seed2Rows 42) seed2Rows 111) (cubicRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row43 :
    digitsEq 111 (rowProduct (seed2Rows 43) seed2Rows 111) (cubicRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row44 :
    digitsEq 111 (rowProduct (seed2Rows 44) seed2Rows 111) (cubicRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row45 :
    digitsEq 111 (rowProduct (seed2Rows 45) seed2Rows 111) (cubicRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row46 :
    digitsEq 111 (rowProduct (seed2Rows 46) seed2Rows 111) (cubicRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row47 :
    digitsEq 111 (rowProduct (seed2Rows 47) seed2Rows 111) (cubicRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row48 :
    digitsEq 111 (rowProduct (seed2Rows 48) seed2Rows 111) (cubicRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row49 :
    digitsEq 111 (rowProduct (seed2Rows 49) seed2Rows 111) (cubicRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row50 :
    digitsEq 111 (rowProduct (seed2Rows 50) seed2Rows 111) (cubicRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row51 :
    digitsEq 111 (rowProduct (seed2Rows 51) seed2Rows 111) (cubicRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row52 :
    digitsEq 111 (rowProduct (seed2Rows 52) seed2Rows 111) (cubicRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row53 :
    digitsEq 111 (rowProduct (seed2Rows 53) seed2Rows 111) (cubicRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row54 :
    digitsEq 111 (rowProduct (seed2Rows 54) seed2Rows 111) (cubicRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row55 :
    digitsEq 111 (rowProduct (seed2Rows 55) seed2Rows 111) (cubicRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row56 :
    digitsEq 111 (rowProduct (seed2Rows 56) seed2Rows 111) (cubicRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row57 :
    digitsEq 111 (rowProduct (seed2Rows 57) seed2Rows 111) (cubicRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row58 :
    digitsEq 111 (rowProduct (seed2Rows 58) seed2Rows 111) (cubicRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row59 :
    digitsEq 111 (rowProduct (seed2Rows 59) seed2Rows 111) (cubicRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row60 :
    digitsEq 111 (rowProduct (seed2Rows 60) seed2Rows 111) (cubicRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row61 :
    digitsEq 111 (rowProduct (seed2Rows 61) seed2Rows 111) (cubicRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row62 :
    digitsEq 111 (rowProduct (seed2Rows 62) seed2Rows 111) (cubicRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row63 :
    digitsEq 111 (rowProduct (seed2Rows 63) seed2Rows 111) (cubicRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row64 :
    digitsEq 111 (rowProduct (seed2Rows 64) seed2Rows 111) (cubicRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row65 :
    digitsEq 111 (rowProduct (seed2Rows 65) seed2Rows 111) (cubicRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row66 :
    digitsEq 111 (rowProduct (seed2Rows 66) seed2Rows 111) (cubicRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row67 :
    digitsEq 111 (rowProduct (seed2Rows 67) seed2Rows 111) (cubicRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row68 :
    digitsEq 111 (rowProduct (seed2Rows 68) seed2Rows 111) (cubicRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row69 :
    digitsEq 111 (rowProduct (seed2Rows 69) seed2Rows 111) (cubicRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row70 :
    digitsEq 111 (rowProduct (seed2Rows 70) seed2Rows 111) (cubicRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row71 :
    digitsEq 111 (rowProduct (seed2Rows 71) seed2Rows 111) (cubicRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row72 :
    digitsEq 111 (rowProduct (seed2Rows 72) seed2Rows 111) (cubicRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row73 :
    digitsEq 111 (rowProduct (seed2Rows 73) seed2Rows 111) (cubicRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row74 :
    digitsEq 111 (rowProduct (seed2Rows 74) seed2Rows 111) (cubicRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row75 :
    digitsEq 111 (rowProduct (seed2Rows 75) seed2Rows 111) (cubicRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row76 :
    digitsEq 111 (rowProduct (seed2Rows 76) seed2Rows 111) (cubicRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row77 :
    digitsEq 111 (rowProduct (seed2Rows 77) seed2Rows 111) (cubicRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row78 :
    digitsEq 111 (rowProduct (seed2Rows 78) seed2Rows 111) (cubicRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row79 :
    digitsEq 111 (rowProduct (seed2Rows 79) seed2Rows 111) (cubicRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row80 :
    digitsEq 111 (rowProduct (seed2Rows 80) seed2Rows 111) (cubicRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row81 :
    digitsEq 111 (rowProduct (seed2Rows 81) seed2Rows 111) (cubicRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row82 :
    digitsEq 111 (rowProduct (seed2Rows 82) seed2Rows 111) (cubicRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row83 :
    digitsEq 111 (rowProduct (seed2Rows 83) seed2Rows 111) (cubicRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row84 :
    digitsEq 111 (rowProduct (seed2Rows 84) seed2Rows 111) (cubicRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row85 :
    digitsEq 111 (rowProduct (seed2Rows 85) seed2Rows 111) (cubicRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row86 :
    digitsEq 111 (rowProduct (seed2Rows 86) seed2Rows 111) (cubicRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row87 :
    digitsEq 111 (rowProduct (seed2Rows 87) seed2Rows 111) (cubicRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row88 :
    digitsEq 111 (rowProduct (seed2Rows 88) seed2Rows 111) (cubicRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row89 :
    digitsEq 111 (rowProduct (seed2Rows 89) seed2Rows 111) (cubicRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row90 :
    digitsEq 111 (rowProduct (seed2Rows 90) seed2Rows 111) (cubicRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row91 :
    digitsEq 111 (rowProduct (seed2Rows 91) seed2Rows 111) (cubicRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row92 :
    digitsEq 111 (rowProduct (seed2Rows 92) seed2Rows 111) (cubicRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row93 :
    digitsEq 111 (rowProduct (seed2Rows 93) seed2Rows 111) (cubicRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row94 :
    digitsEq 111 (rowProduct (seed2Rows 94) seed2Rows 111) (cubicRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row95 :
    digitsEq 111 (rowProduct (seed2Rows 95) seed2Rows 111) (cubicRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row96 :
    digitsEq 111 (rowProduct (seed2Rows 96) seed2Rows 111) (cubicRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row97 :
    digitsEq 111 (rowProduct (seed2Rows 97) seed2Rows 111) (cubicRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row98 :
    digitsEq 111 (rowProduct (seed2Rows 98) seed2Rows 111) (cubicRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row99 :
    digitsEq 111 (rowProduct (seed2Rows 99) seed2Rows 111) (cubicRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row100 :
    digitsEq 111 (rowProduct (seed2Rows 100) seed2Rows 111) (cubicRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row101 :
    digitsEq 111 (rowProduct (seed2Rows 101) seed2Rows 111) (cubicRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row102 :
    digitsEq 111 (rowProduct (seed2Rows 102) seed2Rows 111) (cubicRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row103 :
    digitsEq 111 (rowProduct (seed2Rows 103) seed2Rows 111) (cubicRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row104 :
    digitsEq 111 (rowProduct (seed2Rows 104) seed2Rows 111) (cubicRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row105 :
    digitsEq 111 (rowProduct (seed2Rows 105) seed2Rows 111) (cubicRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row106 :
    digitsEq 111 (rowProduct (seed2Rows 106) seed2Rows 111) (cubicRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row107 :
    digitsEq 111 (rowProduct (seed2Rows 107) seed2Rows 111) (cubicRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row108 :
    digitsEq 111 (rowProduct (seed2Rows 108) seed2Rows 111) (cubicRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row109 :
    digitsEq 111 (rowProduct (seed2Rows 109) seed2Rows 111) (cubicRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_row110 :
    digitsEq 111 (rowProduct (seed2Rows 110) seed2Rows 111) (cubicRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cubic_rows : ∀ i,
    digitsEq 111 (rowProduct (seed2Rows i) seed2Rows 111) (cubicRows i) = true :=
  (Fin.cases cubic_row0
    (Fin.cases cubic_row1
    (Fin.cases cubic_row2
    (Fin.cases cubic_row3
    (Fin.cases cubic_row4
    (Fin.cases cubic_row5
    (Fin.cases cubic_row6
    (Fin.cases cubic_row7
    (Fin.cases cubic_row8
    (Fin.cases cubic_row9
    (Fin.cases cubic_row10
    (Fin.cases cubic_row11
    (Fin.cases cubic_row12
    (Fin.cases cubic_row13
    (Fin.cases cubic_row14
    (Fin.cases cubic_row15
    (Fin.cases cubic_row16
    (Fin.cases cubic_row17
    (Fin.cases cubic_row18
    (Fin.cases cubic_row19
    (Fin.cases cubic_row20
    (Fin.cases cubic_row21
    (Fin.cases cubic_row22
    (Fin.cases cubic_row23
    (Fin.cases cubic_row24
    (Fin.cases cubic_row25
    (Fin.cases cubic_row26
    (Fin.cases cubic_row27
    (Fin.cases cubic_row28
    (Fin.cases cubic_row29
    (Fin.cases cubic_row30
    (Fin.cases cubic_row31
    (Fin.cases cubic_row32
    (Fin.cases cubic_row33
    (Fin.cases cubic_row34
    (Fin.cases cubic_row35
    (Fin.cases cubic_row36
    (Fin.cases cubic_row37
    (Fin.cases cubic_row38
    (Fin.cases cubic_row39
    (Fin.cases cubic_row40
    (Fin.cases cubic_row41
    (Fin.cases cubic_row42
    (Fin.cases cubic_row43
    (Fin.cases cubic_row44
    (Fin.cases cubic_row45
    (Fin.cases cubic_row46
    (Fin.cases cubic_row47
    (Fin.cases cubic_row48
    (Fin.cases cubic_row49
    (Fin.cases cubic_row50
    (Fin.cases cubic_row51
    (Fin.cases cubic_row52
    (Fin.cases cubic_row53
    (Fin.cases cubic_row54
    (Fin.cases cubic_row55
    (Fin.cases cubic_row56
    (Fin.cases cubic_row57
    (Fin.cases cubic_row58
    (Fin.cases cubic_row59
    (Fin.cases cubic_row60
    (Fin.cases cubic_row61
    (Fin.cases cubic_row62
    (Fin.cases cubic_row63
    (Fin.cases cubic_row64
    (Fin.cases cubic_row65
    (Fin.cases cubic_row66
    (Fin.cases cubic_row67
    (Fin.cases cubic_row68
    (Fin.cases cubic_row69
    (Fin.cases cubic_row70
    (Fin.cases cubic_row71
    (Fin.cases cubic_row72
    (Fin.cases cubic_row73
    (Fin.cases cubic_row74
    (Fin.cases cubic_row75
    (Fin.cases cubic_row76
    (Fin.cases cubic_row77
    (Fin.cases cubic_row78
    (Fin.cases cubic_row79
    (Fin.cases cubic_row80
    (Fin.cases cubic_row81
    (Fin.cases cubic_row82
    (Fin.cases cubic_row83
    (Fin.cases cubic_row84
    (Fin.cases cubic_row85
    (Fin.cases cubic_row86
    (Fin.cases cubic_row87
    (Fin.cases cubic_row88
    (Fin.cases cubic_row89
    (Fin.cases cubic_row90
    (Fin.cases cubic_row91
    (Fin.cases cubic_row92
    (Fin.cases cubic_row93
    (Fin.cases cubic_row94
    (Fin.cases cubic_row95
    (Fin.cases cubic_row96
    (Fin.cases cubic_row97
    (Fin.cases cubic_row98
    (Fin.cases cubic_row99
    (Fin.cases cubic_row100
    (Fin.cases cubic_row101
    (Fin.cases cubic_row102
    (Fin.cases cubic_row103
    (Fin.cases cubic_row104
    (Fin.cases cubic_row105
    (Fin.cases cubic_row106
    (Fin.cases cubic_row107
    (Fin.cases cubic_row108
    (Fin.cases cubic_row109
    (Fin.cases cubic_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_cubic : seed2Matrix * seed2Matrix = cubicMatrix :=
  decode_mul _ _ _ seed2_small seed2_small cubic_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
