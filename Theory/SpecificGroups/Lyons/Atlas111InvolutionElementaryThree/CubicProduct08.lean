module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: yx2 times localB

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
private theorem yx2y_row0 :
    digitsEq 111 (rowProduct (yx2Rows 0) localBRows 111) (yx2yRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row1 :
    digitsEq 111 (rowProduct (yx2Rows 1) localBRows 111) (yx2yRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row2 :
    digitsEq 111 (rowProduct (yx2Rows 2) localBRows 111) (yx2yRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row3 :
    digitsEq 111 (rowProduct (yx2Rows 3) localBRows 111) (yx2yRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row4 :
    digitsEq 111 (rowProduct (yx2Rows 4) localBRows 111) (yx2yRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row5 :
    digitsEq 111 (rowProduct (yx2Rows 5) localBRows 111) (yx2yRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row6 :
    digitsEq 111 (rowProduct (yx2Rows 6) localBRows 111) (yx2yRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row7 :
    digitsEq 111 (rowProduct (yx2Rows 7) localBRows 111) (yx2yRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row8 :
    digitsEq 111 (rowProduct (yx2Rows 8) localBRows 111) (yx2yRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row9 :
    digitsEq 111 (rowProduct (yx2Rows 9) localBRows 111) (yx2yRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row10 :
    digitsEq 111 (rowProduct (yx2Rows 10) localBRows 111) (yx2yRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row11 :
    digitsEq 111 (rowProduct (yx2Rows 11) localBRows 111) (yx2yRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row12 :
    digitsEq 111 (rowProduct (yx2Rows 12) localBRows 111) (yx2yRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row13 :
    digitsEq 111 (rowProduct (yx2Rows 13) localBRows 111) (yx2yRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row14 :
    digitsEq 111 (rowProduct (yx2Rows 14) localBRows 111) (yx2yRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row15 :
    digitsEq 111 (rowProduct (yx2Rows 15) localBRows 111) (yx2yRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row16 :
    digitsEq 111 (rowProduct (yx2Rows 16) localBRows 111) (yx2yRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row17 :
    digitsEq 111 (rowProduct (yx2Rows 17) localBRows 111) (yx2yRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row18 :
    digitsEq 111 (rowProduct (yx2Rows 18) localBRows 111) (yx2yRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row19 :
    digitsEq 111 (rowProduct (yx2Rows 19) localBRows 111) (yx2yRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row20 :
    digitsEq 111 (rowProduct (yx2Rows 20) localBRows 111) (yx2yRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row21 :
    digitsEq 111 (rowProduct (yx2Rows 21) localBRows 111) (yx2yRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row22 :
    digitsEq 111 (rowProduct (yx2Rows 22) localBRows 111) (yx2yRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row23 :
    digitsEq 111 (rowProduct (yx2Rows 23) localBRows 111) (yx2yRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row24 :
    digitsEq 111 (rowProduct (yx2Rows 24) localBRows 111) (yx2yRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row25 :
    digitsEq 111 (rowProduct (yx2Rows 25) localBRows 111) (yx2yRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row26 :
    digitsEq 111 (rowProduct (yx2Rows 26) localBRows 111) (yx2yRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row27 :
    digitsEq 111 (rowProduct (yx2Rows 27) localBRows 111) (yx2yRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row28 :
    digitsEq 111 (rowProduct (yx2Rows 28) localBRows 111) (yx2yRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row29 :
    digitsEq 111 (rowProduct (yx2Rows 29) localBRows 111) (yx2yRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row30 :
    digitsEq 111 (rowProduct (yx2Rows 30) localBRows 111) (yx2yRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row31 :
    digitsEq 111 (rowProduct (yx2Rows 31) localBRows 111) (yx2yRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row32 :
    digitsEq 111 (rowProduct (yx2Rows 32) localBRows 111) (yx2yRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row33 :
    digitsEq 111 (rowProduct (yx2Rows 33) localBRows 111) (yx2yRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row34 :
    digitsEq 111 (rowProduct (yx2Rows 34) localBRows 111) (yx2yRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row35 :
    digitsEq 111 (rowProduct (yx2Rows 35) localBRows 111) (yx2yRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row36 :
    digitsEq 111 (rowProduct (yx2Rows 36) localBRows 111) (yx2yRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row37 :
    digitsEq 111 (rowProduct (yx2Rows 37) localBRows 111) (yx2yRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row38 :
    digitsEq 111 (rowProduct (yx2Rows 38) localBRows 111) (yx2yRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row39 :
    digitsEq 111 (rowProduct (yx2Rows 39) localBRows 111) (yx2yRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row40 :
    digitsEq 111 (rowProduct (yx2Rows 40) localBRows 111) (yx2yRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row41 :
    digitsEq 111 (rowProduct (yx2Rows 41) localBRows 111) (yx2yRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row42 :
    digitsEq 111 (rowProduct (yx2Rows 42) localBRows 111) (yx2yRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row43 :
    digitsEq 111 (rowProduct (yx2Rows 43) localBRows 111) (yx2yRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row44 :
    digitsEq 111 (rowProduct (yx2Rows 44) localBRows 111) (yx2yRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row45 :
    digitsEq 111 (rowProduct (yx2Rows 45) localBRows 111) (yx2yRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row46 :
    digitsEq 111 (rowProduct (yx2Rows 46) localBRows 111) (yx2yRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row47 :
    digitsEq 111 (rowProduct (yx2Rows 47) localBRows 111) (yx2yRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row48 :
    digitsEq 111 (rowProduct (yx2Rows 48) localBRows 111) (yx2yRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row49 :
    digitsEq 111 (rowProduct (yx2Rows 49) localBRows 111) (yx2yRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row50 :
    digitsEq 111 (rowProduct (yx2Rows 50) localBRows 111) (yx2yRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row51 :
    digitsEq 111 (rowProduct (yx2Rows 51) localBRows 111) (yx2yRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row52 :
    digitsEq 111 (rowProduct (yx2Rows 52) localBRows 111) (yx2yRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row53 :
    digitsEq 111 (rowProduct (yx2Rows 53) localBRows 111) (yx2yRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row54 :
    digitsEq 111 (rowProduct (yx2Rows 54) localBRows 111) (yx2yRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row55 :
    digitsEq 111 (rowProduct (yx2Rows 55) localBRows 111) (yx2yRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row56 :
    digitsEq 111 (rowProduct (yx2Rows 56) localBRows 111) (yx2yRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row57 :
    digitsEq 111 (rowProduct (yx2Rows 57) localBRows 111) (yx2yRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row58 :
    digitsEq 111 (rowProduct (yx2Rows 58) localBRows 111) (yx2yRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row59 :
    digitsEq 111 (rowProduct (yx2Rows 59) localBRows 111) (yx2yRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row60 :
    digitsEq 111 (rowProduct (yx2Rows 60) localBRows 111) (yx2yRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row61 :
    digitsEq 111 (rowProduct (yx2Rows 61) localBRows 111) (yx2yRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row62 :
    digitsEq 111 (rowProduct (yx2Rows 62) localBRows 111) (yx2yRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row63 :
    digitsEq 111 (rowProduct (yx2Rows 63) localBRows 111) (yx2yRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row64 :
    digitsEq 111 (rowProduct (yx2Rows 64) localBRows 111) (yx2yRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row65 :
    digitsEq 111 (rowProduct (yx2Rows 65) localBRows 111) (yx2yRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row66 :
    digitsEq 111 (rowProduct (yx2Rows 66) localBRows 111) (yx2yRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row67 :
    digitsEq 111 (rowProduct (yx2Rows 67) localBRows 111) (yx2yRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row68 :
    digitsEq 111 (rowProduct (yx2Rows 68) localBRows 111) (yx2yRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row69 :
    digitsEq 111 (rowProduct (yx2Rows 69) localBRows 111) (yx2yRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row70 :
    digitsEq 111 (rowProduct (yx2Rows 70) localBRows 111) (yx2yRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row71 :
    digitsEq 111 (rowProduct (yx2Rows 71) localBRows 111) (yx2yRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row72 :
    digitsEq 111 (rowProduct (yx2Rows 72) localBRows 111) (yx2yRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row73 :
    digitsEq 111 (rowProduct (yx2Rows 73) localBRows 111) (yx2yRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row74 :
    digitsEq 111 (rowProduct (yx2Rows 74) localBRows 111) (yx2yRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row75 :
    digitsEq 111 (rowProduct (yx2Rows 75) localBRows 111) (yx2yRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row76 :
    digitsEq 111 (rowProduct (yx2Rows 76) localBRows 111) (yx2yRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row77 :
    digitsEq 111 (rowProduct (yx2Rows 77) localBRows 111) (yx2yRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row78 :
    digitsEq 111 (rowProduct (yx2Rows 78) localBRows 111) (yx2yRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row79 :
    digitsEq 111 (rowProduct (yx2Rows 79) localBRows 111) (yx2yRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row80 :
    digitsEq 111 (rowProduct (yx2Rows 80) localBRows 111) (yx2yRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row81 :
    digitsEq 111 (rowProduct (yx2Rows 81) localBRows 111) (yx2yRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row82 :
    digitsEq 111 (rowProduct (yx2Rows 82) localBRows 111) (yx2yRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row83 :
    digitsEq 111 (rowProduct (yx2Rows 83) localBRows 111) (yx2yRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row84 :
    digitsEq 111 (rowProduct (yx2Rows 84) localBRows 111) (yx2yRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row85 :
    digitsEq 111 (rowProduct (yx2Rows 85) localBRows 111) (yx2yRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row86 :
    digitsEq 111 (rowProduct (yx2Rows 86) localBRows 111) (yx2yRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row87 :
    digitsEq 111 (rowProduct (yx2Rows 87) localBRows 111) (yx2yRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row88 :
    digitsEq 111 (rowProduct (yx2Rows 88) localBRows 111) (yx2yRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row89 :
    digitsEq 111 (rowProduct (yx2Rows 89) localBRows 111) (yx2yRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row90 :
    digitsEq 111 (rowProduct (yx2Rows 90) localBRows 111) (yx2yRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row91 :
    digitsEq 111 (rowProduct (yx2Rows 91) localBRows 111) (yx2yRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row92 :
    digitsEq 111 (rowProduct (yx2Rows 92) localBRows 111) (yx2yRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row93 :
    digitsEq 111 (rowProduct (yx2Rows 93) localBRows 111) (yx2yRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row94 :
    digitsEq 111 (rowProduct (yx2Rows 94) localBRows 111) (yx2yRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row95 :
    digitsEq 111 (rowProduct (yx2Rows 95) localBRows 111) (yx2yRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row96 :
    digitsEq 111 (rowProduct (yx2Rows 96) localBRows 111) (yx2yRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row97 :
    digitsEq 111 (rowProduct (yx2Rows 97) localBRows 111) (yx2yRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row98 :
    digitsEq 111 (rowProduct (yx2Rows 98) localBRows 111) (yx2yRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row99 :
    digitsEq 111 (rowProduct (yx2Rows 99) localBRows 111) (yx2yRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row100 :
    digitsEq 111 (rowProduct (yx2Rows 100) localBRows 111) (yx2yRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row101 :
    digitsEq 111 (rowProduct (yx2Rows 101) localBRows 111) (yx2yRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row102 :
    digitsEq 111 (rowProduct (yx2Rows 102) localBRows 111) (yx2yRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row103 :
    digitsEq 111 (rowProduct (yx2Rows 103) localBRows 111) (yx2yRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row104 :
    digitsEq 111 (rowProduct (yx2Rows 104) localBRows 111) (yx2yRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row105 :
    digitsEq 111 (rowProduct (yx2Rows 105) localBRows 111) (yx2yRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row106 :
    digitsEq 111 (rowProduct (yx2Rows 106) localBRows 111) (yx2yRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row107 :
    digitsEq 111 (rowProduct (yx2Rows 107) localBRows 111) (yx2yRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row108 :
    digitsEq 111 (rowProduct (yx2Rows 108) localBRows 111) (yx2yRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row109 :
    digitsEq 111 (rowProduct (yx2Rows 109) localBRows 111) (yx2yRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_row110 :
    digitsEq 111 (rowProduct (yx2Rows 110) localBRows 111) (yx2yRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem yx2y_rows : ∀ i,
    digitsEq 111 (rowProduct (yx2Rows i) localBRows 111) (yx2yRows i) = true :=
  (Fin.cases yx2y_row0
    (Fin.cases yx2y_row1
    (Fin.cases yx2y_row2
    (Fin.cases yx2y_row3
    (Fin.cases yx2y_row4
    (Fin.cases yx2y_row5
    (Fin.cases yx2y_row6
    (Fin.cases yx2y_row7
    (Fin.cases yx2y_row8
    (Fin.cases yx2y_row9
    (Fin.cases yx2y_row10
    (Fin.cases yx2y_row11
    (Fin.cases yx2y_row12
    (Fin.cases yx2y_row13
    (Fin.cases yx2y_row14
    (Fin.cases yx2y_row15
    (Fin.cases yx2y_row16
    (Fin.cases yx2y_row17
    (Fin.cases yx2y_row18
    (Fin.cases yx2y_row19
    (Fin.cases yx2y_row20
    (Fin.cases yx2y_row21
    (Fin.cases yx2y_row22
    (Fin.cases yx2y_row23
    (Fin.cases yx2y_row24
    (Fin.cases yx2y_row25
    (Fin.cases yx2y_row26
    (Fin.cases yx2y_row27
    (Fin.cases yx2y_row28
    (Fin.cases yx2y_row29
    (Fin.cases yx2y_row30
    (Fin.cases yx2y_row31
    (Fin.cases yx2y_row32
    (Fin.cases yx2y_row33
    (Fin.cases yx2y_row34
    (Fin.cases yx2y_row35
    (Fin.cases yx2y_row36
    (Fin.cases yx2y_row37
    (Fin.cases yx2y_row38
    (Fin.cases yx2y_row39
    (Fin.cases yx2y_row40
    (Fin.cases yx2y_row41
    (Fin.cases yx2y_row42
    (Fin.cases yx2y_row43
    (Fin.cases yx2y_row44
    (Fin.cases yx2y_row45
    (Fin.cases yx2y_row46
    (Fin.cases yx2y_row47
    (Fin.cases yx2y_row48
    (Fin.cases yx2y_row49
    (Fin.cases yx2y_row50
    (Fin.cases yx2y_row51
    (Fin.cases yx2y_row52
    (Fin.cases yx2y_row53
    (Fin.cases yx2y_row54
    (Fin.cases yx2y_row55
    (Fin.cases yx2y_row56
    (Fin.cases yx2y_row57
    (Fin.cases yx2y_row58
    (Fin.cases yx2y_row59
    (Fin.cases yx2y_row60
    (Fin.cases yx2y_row61
    (Fin.cases yx2y_row62
    (Fin.cases yx2y_row63
    (Fin.cases yx2y_row64
    (Fin.cases yx2y_row65
    (Fin.cases yx2y_row66
    (Fin.cases yx2y_row67
    (Fin.cases yx2y_row68
    (Fin.cases yx2y_row69
    (Fin.cases yx2y_row70
    (Fin.cases yx2y_row71
    (Fin.cases yx2y_row72
    (Fin.cases yx2y_row73
    (Fin.cases yx2y_row74
    (Fin.cases yx2y_row75
    (Fin.cases yx2y_row76
    (Fin.cases yx2y_row77
    (Fin.cases yx2y_row78
    (Fin.cases yx2y_row79
    (Fin.cases yx2y_row80
    (Fin.cases yx2y_row81
    (Fin.cases yx2y_row82
    (Fin.cases yx2y_row83
    (Fin.cases yx2y_row84
    (Fin.cases yx2y_row85
    (Fin.cases yx2y_row86
    (Fin.cases yx2y_row87
    (Fin.cases yx2y_row88
    (Fin.cases yx2y_row89
    (Fin.cases yx2y_row90
    (Fin.cases yx2y_row91
    (Fin.cases yx2y_row92
    (Fin.cases yx2y_row93
    (Fin.cases yx2y_row94
    (Fin.cases yx2y_row95
    (Fin.cases yx2y_row96
    (Fin.cases yx2y_row97
    (Fin.cases yx2y_row98
    (Fin.cases yx2y_row99
    (Fin.cases yx2y_row100
    (Fin.cases yx2y_row101
    (Fin.cases yx2y_row102
    (Fin.cases yx2y_row103
    (Fin.cases yx2y_row104
    (Fin.cases yx2y_row105
    (Fin.cases yx2y_row106
    (Fin.cases yx2y_row107
    (Fin.cases yx2y_row108
    (Fin.cases yx2y_row109
    (Fin.cases yx2y_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_yx2y : yx2Matrix * localBMatrix = yx2yMatrix :=
  decode_mul _ _ _ yx2_small localB_small yx2y_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
