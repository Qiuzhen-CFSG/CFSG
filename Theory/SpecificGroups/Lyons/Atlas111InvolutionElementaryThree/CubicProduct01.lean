module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: xy times ab6

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
private theorem xyx6_row0 :
    digitsEq 111 (rowProduct (xyRows 0) ab6Rows 111) (xyx6Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row1 :
    digitsEq 111 (rowProduct (xyRows 1) ab6Rows 111) (xyx6Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row2 :
    digitsEq 111 (rowProduct (xyRows 2) ab6Rows 111) (xyx6Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row3 :
    digitsEq 111 (rowProduct (xyRows 3) ab6Rows 111) (xyx6Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row4 :
    digitsEq 111 (rowProduct (xyRows 4) ab6Rows 111) (xyx6Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row5 :
    digitsEq 111 (rowProduct (xyRows 5) ab6Rows 111) (xyx6Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row6 :
    digitsEq 111 (rowProduct (xyRows 6) ab6Rows 111) (xyx6Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row7 :
    digitsEq 111 (rowProduct (xyRows 7) ab6Rows 111) (xyx6Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row8 :
    digitsEq 111 (rowProduct (xyRows 8) ab6Rows 111) (xyx6Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row9 :
    digitsEq 111 (rowProduct (xyRows 9) ab6Rows 111) (xyx6Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row10 :
    digitsEq 111 (rowProduct (xyRows 10) ab6Rows 111) (xyx6Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row11 :
    digitsEq 111 (rowProduct (xyRows 11) ab6Rows 111) (xyx6Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row12 :
    digitsEq 111 (rowProduct (xyRows 12) ab6Rows 111) (xyx6Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row13 :
    digitsEq 111 (rowProduct (xyRows 13) ab6Rows 111) (xyx6Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row14 :
    digitsEq 111 (rowProduct (xyRows 14) ab6Rows 111) (xyx6Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row15 :
    digitsEq 111 (rowProduct (xyRows 15) ab6Rows 111) (xyx6Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row16 :
    digitsEq 111 (rowProduct (xyRows 16) ab6Rows 111) (xyx6Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row17 :
    digitsEq 111 (rowProduct (xyRows 17) ab6Rows 111) (xyx6Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row18 :
    digitsEq 111 (rowProduct (xyRows 18) ab6Rows 111) (xyx6Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row19 :
    digitsEq 111 (rowProduct (xyRows 19) ab6Rows 111) (xyx6Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row20 :
    digitsEq 111 (rowProduct (xyRows 20) ab6Rows 111) (xyx6Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row21 :
    digitsEq 111 (rowProduct (xyRows 21) ab6Rows 111) (xyx6Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row22 :
    digitsEq 111 (rowProduct (xyRows 22) ab6Rows 111) (xyx6Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row23 :
    digitsEq 111 (rowProduct (xyRows 23) ab6Rows 111) (xyx6Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row24 :
    digitsEq 111 (rowProduct (xyRows 24) ab6Rows 111) (xyx6Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row25 :
    digitsEq 111 (rowProduct (xyRows 25) ab6Rows 111) (xyx6Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row26 :
    digitsEq 111 (rowProduct (xyRows 26) ab6Rows 111) (xyx6Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row27 :
    digitsEq 111 (rowProduct (xyRows 27) ab6Rows 111) (xyx6Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row28 :
    digitsEq 111 (rowProduct (xyRows 28) ab6Rows 111) (xyx6Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row29 :
    digitsEq 111 (rowProduct (xyRows 29) ab6Rows 111) (xyx6Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row30 :
    digitsEq 111 (rowProduct (xyRows 30) ab6Rows 111) (xyx6Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row31 :
    digitsEq 111 (rowProduct (xyRows 31) ab6Rows 111) (xyx6Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row32 :
    digitsEq 111 (rowProduct (xyRows 32) ab6Rows 111) (xyx6Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row33 :
    digitsEq 111 (rowProduct (xyRows 33) ab6Rows 111) (xyx6Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row34 :
    digitsEq 111 (rowProduct (xyRows 34) ab6Rows 111) (xyx6Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row35 :
    digitsEq 111 (rowProduct (xyRows 35) ab6Rows 111) (xyx6Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row36 :
    digitsEq 111 (rowProduct (xyRows 36) ab6Rows 111) (xyx6Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row37 :
    digitsEq 111 (rowProduct (xyRows 37) ab6Rows 111) (xyx6Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row38 :
    digitsEq 111 (rowProduct (xyRows 38) ab6Rows 111) (xyx6Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row39 :
    digitsEq 111 (rowProduct (xyRows 39) ab6Rows 111) (xyx6Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row40 :
    digitsEq 111 (rowProduct (xyRows 40) ab6Rows 111) (xyx6Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row41 :
    digitsEq 111 (rowProduct (xyRows 41) ab6Rows 111) (xyx6Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row42 :
    digitsEq 111 (rowProduct (xyRows 42) ab6Rows 111) (xyx6Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row43 :
    digitsEq 111 (rowProduct (xyRows 43) ab6Rows 111) (xyx6Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row44 :
    digitsEq 111 (rowProduct (xyRows 44) ab6Rows 111) (xyx6Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row45 :
    digitsEq 111 (rowProduct (xyRows 45) ab6Rows 111) (xyx6Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row46 :
    digitsEq 111 (rowProduct (xyRows 46) ab6Rows 111) (xyx6Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row47 :
    digitsEq 111 (rowProduct (xyRows 47) ab6Rows 111) (xyx6Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row48 :
    digitsEq 111 (rowProduct (xyRows 48) ab6Rows 111) (xyx6Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row49 :
    digitsEq 111 (rowProduct (xyRows 49) ab6Rows 111) (xyx6Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row50 :
    digitsEq 111 (rowProduct (xyRows 50) ab6Rows 111) (xyx6Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row51 :
    digitsEq 111 (rowProduct (xyRows 51) ab6Rows 111) (xyx6Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row52 :
    digitsEq 111 (rowProduct (xyRows 52) ab6Rows 111) (xyx6Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row53 :
    digitsEq 111 (rowProduct (xyRows 53) ab6Rows 111) (xyx6Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row54 :
    digitsEq 111 (rowProduct (xyRows 54) ab6Rows 111) (xyx6Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row55 :
    digitsEq 111 (rowProduct (xyRows 55) ab6Rows 111) (xyx6Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row56 :
    digitsEq 111 (rowProduct (xyRows 56) ab6Rows 111) (xyx6Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row57 :
    digitsEq 111 (rowProduct (xyRows 57) ab6Rows 111) (xyx6Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row58 :
    digitsEq 111 (rowProduct (xyRows 58) ab6Rows 111) (xyx6Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row59 :
    digitsEq 111 (rowProduct (xyRows 59) ab6Rows 111) (xyx6Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row60 :
    digitsEq 111 (rowProduct (xyRows 60) ab6Rows 111) (xyx6Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row61 :
    digitsEq 111 (rowProduct (xyRows 61) ab6Rows 111) (xyx6Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row62 :
    digitsEq 111 (rowProduct (xyRows 62) ab6Rows 111) (xyx6Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row63 :
    digitsEq 111 (rowProduct (xyRows 63) ab6Rows 111) (xyx6Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row64 :
    digitsEq 111 (rowProduct (xyRows 64) ab6Rows 111) (xyx6Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row65 :
    digitsEq 111 (rowProduct (xyRows 65) ab6Rows 111) (xyx6Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row66 :
    digitsEq 111 (rowProduct (xyRows 66) ab6Rows 111) (xyx6Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row67 :
    digitsEq 111 (rowProduct (xyRows 67) ab6Rows 111) (xyx6Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row68 :
    digitsEq 111 (rowProduct (xyRows 68) ab6Rows 111) (xyx6Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row69 :
    digitsEq 111 (rowProduct (xyRows 69) ab6Rows 111) (xyx6Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row70 :
    digitsEq 111 (rowProduct (xyRows 70) ab6Rows 111) (xyx6Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row71 :
    digitsEq 111 (rowProduct (xyRows 71) ab6Rows 111) (xyx6Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row72 :
    digitsEq 111 (rowProduct (xyRows 72) ab6Rows 111) (xyx6Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row73 :
    digitsEq 111 (rowProduct (xyRows 73) ab6Rows 111) (xyx6Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row74 :
    digitsEq 111 (rowProduct (xyRows 74) ab6Rows 111) (xyx6Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row75 :
    digitsEq 111 (rowProduct (xyRows 75) ab6Rows 111) (xyx6Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row76 :
    digitsEq 111 (rowProduct (xyRows 76) ab6Rows 111) (xyx6Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row77 :
    digitsEq 111 (rowProduct (xyRows 77) ab6Rows 111) (xyx6Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row78 :
    digitsEq 111 (rowProduct (xyRows 78) ab6Rows 111) (xyx6Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row79 :
    digitsEq 111 (rowProduct (xyRows 79) ab6Rows 111) (xyx6Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row80 :
    digitsEq 111 (rowProduct (xyRows 80) ab6Rows 111) (xyx6Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row81 :
    digitsEq 111 (rowProduct (xyRows 81) ab6Rows 111) (xyx6Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row82 :
    digitsEq 111 (rowProduct (xyRows 82) ab6Rows 111) (xyx6Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row83 :
    digitsEq 111 (rowProduct (xyRows 83) ab6Rows 111) (xyx6Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row84 :
    digitsEq 111 (rowProduct (xyRows 84) ab6Rows 111) (xyx6Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row85 :
    digitsEq 111 (rowProduct (xyRows 85) ab6Rows 111) (xyx6Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row86 :
    digitsEq 111 (rowProduct (xyRows 86) ab6Rows 111) (xyx6Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row87 :
    digitsEq 111 (rowProduct (xyRows 87) ab6Rows 111) (xyx6Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row88 :
    digitsEq 111 (rowProduct (xyRows 88) ab6Rows 111) (xyx6Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row89 :
    digitsEq 111 (rowProduct (xyRows 89) ab6Rows 111) (xyx6Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row90 :
    digitsEq 111 (rowProduct (xyRows 90) ab6Rows 111) (xyx6Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row91 :
    digitsEq 111 (rowProduct (xyRows 91) ab6Rows 111) (xyx6Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row92 :
    digitsEq 111 (rowProduct (xyRows 92) ab6Rows 111) (xyx6Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row93 :
    digitsEq 111 (rowProduct (xyRows 93) ab6Rows 111) (xyx6Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row94 :
    digitsEq 111 (rowProduct (xyRows 94) ab6Rows 111) (xyx6Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row95 :
    digitsEq 111 (rowProduct (xyRows 95) ab6Rows 111) (xyx6Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row96 :
    digitsEq 111 (rowProduct (xyRows 96) ab6Rows 111) (xyx6Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row97 :
    digitsEq 111 (rowProduct (xyRows 97) ab6Rows 111) (xyx6Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row98 :
    digitsEq 111 (rowProduct (xyRows 98) ab6Rows 111) (xyx6Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row99 :
    digitsEq 111 (rowProduct (xyRows 99) ab6Rows 111) (xyx6Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row100 :
    digitsEq 111 (rowProduct (xyRows 100) ab6Rows 111) (xyx6Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row101 :
    digitsEq 111 (rowProduct (xyRows 101) ab6Rows 111) (xyx6Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row102 :
    digitsEq 111 (rowProduct (xyRows 102) ab6Rows 111) (xyx6Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row103 :
    digitsEq 111 (rowProduct (xyRows 103) ab6Rows 111) (xyx6Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row104 :
    digitsEq 111 (rowProduct (xyRows 104) ab6Rows 111) (xyx6Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row105 :
    digitsEq 111 (rowProduct (xyRows 105) ab6Rows 111) (xyx6Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row106 :
    digitsEq 111 (rowProduct (xyRows 106) ab6Rows 111) (xyx6Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row107 :
    digitsEq 111 (rowProduct (xyRows 107) ab6Rows 111) (xyx6Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row108 :
    digitsEq 111 (rowProduct (xyRows 108) ab6Rows 111) (xyx6Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row109 :
    digitsEq 111 (rowProduct (xyRows 109) ab6Rows 111) (xyx6Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_row110 :
    digitsEq 111 (rowProduct (xyRows 110) ab6Rows 111) (xyx6Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xyx6_rows : ∀ i,
    digitsEq 111 (rowProduct (xyRows i) ab6Rows 111) (xyx6Rows i) = true :=
  (Fin.cases xyx6_row0
    (Fin.cases xyx6_row1
    (Fin.cases xyx6_row2
    (Fin.cases xyx6_row3
    (Fin.cases xyx6_row4
    (Fin.cases xyx6_row5
    (Fin.cases xyx6_row6
    (Fin.cases xyx6_row7
    (Fin.cases xyx6_row8
    (Fin.cases xyx6_row9
    (Fin.cases xyx6_row10
    (Fin.cases xyx6_row11
    (Fin.cases xyx6_row12
    (Fin.cases xyx6_row13
    (Fin.cases xyx6_row14
    (Fin.cases xyx6_row15
    (Fin.cases xyx6_row16
    (Fin.cases xyx6_row17
    (Fin.cases xyx6_row18
    (Fin.cases xyx6_row19
    (Fin.cases xyx6_row20
    (Fin.cases xyx6_row21
    (Fin.cases xyx6_row22
    (Fin.cases xyx6_row23
    (Fin.cases xyx6_row24
    (Fin.cases xyx6_row25
    (Fin.cases xyx6_row26
    (Fin.cases xyx6_row27
    (Fin.cases xyx6_row28
    (Fin.cases xyx6_row29
    (Fin.cases xyx6_row30
    (Fin.cases xyx6_row31
    (Fin.cases xyx6_row32
    (Fin.cases xyx6_row33
    (Fin.cases xyx6_row34
    (Fin.cases xyx6_row35
    (Fin.cases xyx6_row36
    (Fin.cases xyx6_row37
    (Fin.cases xyx6_row38
    (Fin.cases xyx6_row39
    (Fin.cases xyx6_row40
    (Fin.cases xyx6_row41
    (Fin.cases xyx6_row42
    (Fin.cases xyx6_row43
    (Fin.cases xyx6_row44
    (Fin.cases xyx6_row45
    (Fin.cases xyx6_row46
    (Fin.cases xyx6_row47
    (Fin.cases xyx6_row48
    (Fin.cases xyx6_row49
    (Fin.cases xyx6_row50
    (Fin.cases xyx6_row51
    (Fin.cases xyx6_row52
    (Fin.cases xyx6_row53
    (Fin.cases xyx6_row54
    (Fin.cases xyx6_row55
    (Fin.cases xyx6_row56
    (Fin.cases xyx6_row57
    (Fin.cases xyx6_row58
    (Fin.cases xyx6_row59
    (Fin.cases xyx6_row60
    (Fin.cases xyx6_row61
    (Fin.cases xyx6_row62
    (Fin.cases xyx6_row63
    (Fin.cases xyx6_row64
    (Fin.cases xyx6_row65
    (Fin.cases xyx6_row66
    (Fin.cases xyx6_row67
    (Fin.cases xyx6_row68
    (Fin.cases xyx6_row69
    (Fin.cases xyx6_row70
    (Fin.cases xyx6_row71
    (Fin.cases xyx6_row72
    (Fin.cases xyx6_row73
    (Fin.cases xyx6_row74
    (Fin.cases xyx6_row75
    (Fin.cases xyx6_row76
    (Fin.cases xyx6_row77
    (Fin.cases xyx6_row78
    (Fin.cases xyx6_row79
    (Fin.cases xyx6_row80
    (Fin.cases xyx6_row81
    (Fin.cases xyx6_row82
    (Fin.cases xyx6_row83
    (Fin.cases xyx6_row84
    (Fin.cases xyx6_row85
    (Fin.cases xyx6_row86
    (Fin.cases xyx6_row87
    (Fin.cases xyx6_row88
    (Fin.cases xyx6_row89
    (Fin.cases xyx6_row90
    (Fin.cases xyx6_row91
    (Fin.cases xyx6_row92
    (Fin.cases xyx6_row93
    (Fin.cases xyx6_row94
    (Fin.cases xyx6_row95
    (Fin.cases xyx6_row96
    (Fin.cases xyx6_row97
    (Fin.cases xyx6_row98
    (Fin.cases xyx6_row99
    (Fin.cases xyx6_row100
    (Fin.cases xyx6_row101
    (Fin.cases xyx6_row102
    (Fin.cases xyx6_row103
    (Fin.cases xyx6_row104
    (Fin.cases xyx6_row105
    (Fin.cases xyx6_row106
    (Fin.cases xyx6_row107
    (Fin.cases xyx6_row108
    (Fin.cases xyx6_row109
    (Fin.cases xyx6_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_xyx6 : xyMatrix * ab6Matrix = xyx6Matrix :=
  decode_mul _ _ _ xy_small ab6_small xyx6_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
