module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: third times cubic

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
private theorem pair02rev_row0 :
    digitsEq 111 (rowProduct (thirdRows 0) cubicRows 111) (pair02Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row1 :
    digitsEq 111 (rowProduct (thirdRows 1) cubicRows 111) (pair02Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row2 :
    digitsEq 111 (rowProduct (thirdRows 2) cubicRows 111) (pair02Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row3 :
    digitsEq 111 (rowProduct (thirdRows 3) cubicRows 111) (pair02Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row4 :
    digitsEq 111 (rowProduct (thirdRows 4) cubicRows 111) (pair02Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row5 :
    digitsEq 111 (rowProduct (thirdRows 5) cubicRows 111) (pair02Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row6 :
    digitsEq 111 (rowProduct (thirdRows 6) cubicRows 111) (pair02Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row7 :
    digitsEq 111 (rowProduct (thirdRows 7) cubicRows 111) (pair02Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row8 :
    digitsEq 111 (rowProduct (thirdRows 8) cubicRows 111) (pair02Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row9 :
    digitsEq 111 (rowProduct (thirdRows 9) cubicRows 111) (pair02Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row10 :
    digitsEq 111 (rowProduct (thirdRows 10) cubicRows 111) (pair02Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row11 :
    digitsEq 111 (rowProduct (thirdRows 11) cubicRows 111) (pair02Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row12 :
    digitsEq 111 (rowProduct (thirdRows 12) cubicRows 111) (pair02Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row13 :
    digitsEq 111 (rowProduct (thirdRows 13) cubicRows 111) (pair02Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row14 :
    digitsEq 111 (rowProduct (thirdRows 14) cubicRows 111) (pair02Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row15 :
    digitsEq 111 (rowProduct (thirdRows 15) cubicRows 111) (pair02Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row16 :
    digitsEq 111 (rowProduct (thirdRows 16) cubicRows 111) (pair02Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row17 :
    digitsEq 111 (rowProduct (thirdRows 17) cubicRows 111) (pair02Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row18 :
    digitsEq 111 (rowProduct (thirdRows 18) cubicRows 111) (pair02Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row19 :
    digitsEq 111 (rowProduct (thirdRows 19) cubicRows 111) (pair02Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row20 :
    digitsEq 111 (rowProduct (thirdRows 20) cubicRows 111) (pair02Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row21 :
    digitsEq 111 (rowProduct (thirdRows 21) cubicRows 111) (pair02Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row22 :
    digitsEq 111 (rowProduct (thirdRows 22) cubicRows 111) (pair02Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row23 :
    digitsEq 111 (rowProduct (thirdRows 23) cubicRows 111) (pair02Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row24 :
    digitsEq 111 (rowProduct (thirdRows 24) cubicRows 111) (pair02Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row25 :
    digitsEq 111 (rowProduct (thirdRows 25) cubicRows 111) (pair02Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row26 :
    digitsEq 111 (rowProduct (thirdRows 26) cubicRows 111) (pair02Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row27 :
    digitsEq 111 (rowProduct (thirdRows 27) cubicRows 111) (pair02Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row28 :
    digitsEq 111 (rowProduct (thirdRows 28) cubicRows 111) (pair02Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row29 :
    digitsEq 111 (rowProduct (thirdRows 29) cubicRows 111) (pair02Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row30 :
    digitsEq 111 (rowProduct (thirdRows 30) cubicRows 111) (pair02Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row31 :
    digitsEq 111 (rowProduct (thirdRows 31) cubicRows 111) (pair02Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row32 :
    digitsEq 111 (rowProduct (thirdRows 32) cubicRows 111) (pair02Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row33 :
    digitsEq 111 (rowProduct (thirdRows 33) cubicRows 111) (pair02Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row34 :
    digitsEq 111 (rowProduct (thirdRows 34) cubicRows 111) (pair02Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row35 :
    digitsEq 111 (rowProduct (thirdRows 35) cubicRows 111) (pair02Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row36 :
    digitsEq 111 (rowProduct (thirdRows 36) cubicRows 111) (pair02Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row37 :
    digitsEq 111 (rowProduct (thirdRows 37) cubicRows 111) (pair02Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row38 :
    digitsEq 111 (rowProduct (thirdRows 38) cubicRows 111) (pair02Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row39 :
    digitsEq 111 (rowProduct (thirdRows 39) cubicRows 111) (pair02Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row40 :
    digitsEq 111 (rowProduct (thirdRows 40) cubicRows 111) (pair02Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row41 :
    digitsEq 111 (rowProduct (thirdRows 41) cubicRows 111) (pair02Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row42 :
    digitsEq 111 (rowProduct (thirdRows 42) cubicRows 111) (pair02Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row43 :
    digitsEq 111 (rowProduct (thirdRows 43) cubicRows 111) (pair02Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row44 :
    digitsEq 111 (rowProduct (thirdRows 44) cubicRows 111) (pair02Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row45 :
    digitsEq 111 (rowProduct (thirdRows 45) cubicRows 111) (pair02Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row46 :
    digitsEq 111 (rowProduct (thirdRows 46) cubicRows 111) (pair02Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row47 :
    digitsEq 111 (rowProduct (thirdRows 47) cubicRows 111) (pair02Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row48 :
    digitsEq 111 (rowProduct (thirdRows 48) cubicRows 111) (pair02Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row49 :
    digitsEq 111 (rowProduct (thirdRows 49) cubicRows 111) (pair02Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row50 :
    digitsEq 111 (rowProduct (thirdRows 50) cubicRows 111) (pair02Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row51 :
    digitsEq 111 (rowProduct (thirdRows 51) cubicRows 111) (pair02Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row52 :
    digitsEq 111 (rowProduct (thirdRows 52) cubicRows 111) (pair02Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row53 :
    digitsEq 111 (rowProduct (thirdRows 53) cubicRows 111) (pair02Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row54 :
    digitsEq 111 (rowProduct (thirdRows 54) cubicRows 111) (pair02Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row55 :
    digitsEq 111 (rowProduct (thirdRows 55) cubicRows 111) (pair02Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row56 :
    digitsEq 111 (rowProduct (thirdRows 56) cubicRows 111) (pair02Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row57 :
    digitsEq 111 (rowProduct (thirdRows 57) cubicRows 111) (pair02Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row58 :
    digitsEq 111 (rowProduct (thirdRows 58) cubicRows 111) (pair02Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row59 :
    digitsEq 111 (rowProduct (thirdRows 59) cubicRows 111) (pair02Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row60 :
    digitsEq 111 (rowProduct (thirdRows 60) cubicRows 111) (pair02Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row61 :
    digitsEq 111 (rowProduct (thirdRows 61) cubicRows 111) (pair02Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row62 :
    digitsEq 111 (rowProduct (thirdRows 62) cubicRows 111) (pair02Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row63 :
    digitsEq 111 (rowProduct (thirdRows 63) cubicRows 111) (pair02Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row64 :
    digitsEq 111 (rowProduct (thirdRows 64) cubicRows 111) (pair02Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row65 :
    digitsEq 111 (rowProduct (thirdRows 65) cubicRows 111) (pair02Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row66 :
    digitsEq 111 (rowProduct (thirdRows 66) cubicRows 111) (pair02Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row67 :
    digitsEq 111 (rowProduct (thirdRows 67) cubicRows 111) (pair02Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row68 :
    digitsEq 111 (rowProduct (thirdRows 68) cubicRows 111) (pair02Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row69 :
    digitsEq 111 (rowProduct (thirdRows 69) cubicRows 111) (pair02Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row70 :
    digitsEq 111 (rowProduct (thirdRows 70) cubicRows 111) (pair02Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row71 :
    digitsEq 111 (rowProduct (thirdRows 71) cubicRows 111) (pair02Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row72 :
    digitsEq 111 (rowProduct (thirdRows 72) cubicRows 111) (pair02Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row73 :
    digitsEq 111 (rowProduct (thirdRows 73) cubicRows 111) (pair02Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row74 :
    digitsEq 111 (rowProduct (thirdRows 74) cubicRows 111) (pair02Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row75 :
    digitsEq 111 (rowProduct (thirdRows 75) cubicRows 111) (pair02Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row76 :
    digitsEq 111 (rowProduct (thirdRows 76) cubicRows 111) (pair02Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row77 :
    digitsEq 111 (rowProduct (thirdRows 77) cubicRows 111) (pair02Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row78 :
    digitsEq 111 (rowProduct (thirdRows 78) cubicRows 111) (pair02Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row79 :
    digitsEq 111 (rowProduct (thirdRows 79) cubicRows 111) (pair02Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row80 :
    digitsEq 111 (rowProduct (thirdRows 80) cubicRows 111) (pair02Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row81 :
    digitsEq 111 (rowProduct (thirdRows 81) cubicRows 111) (pair02Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row82 :
    digitsEq 111 (rowProduct (thirdRows 82) cubicRows 111) (pair02Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row83 :
    digitsEq 111 (rowProduct (thirdRows 83) cubicRows 111) (pair02Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row84 :
    digitsEq 111 (rowProduct (thirdRows 84) cubicRows 111) (pair02Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row85 :
    digitsEq 111 (rowProduct (thirdRows 85) cubicRows 111) (pair02Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row86 :
    digitsEq 111 (rowProduct (thirdRows 86) cubicRows 111) (pair02Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row87 :
    digitsEq 111 (rowProduct (thirdRows 87) cubicRows 111) (pair02Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row88 :
    digitsEq 111 (rowProduct (thirdRows 88) cubicRows 111) (pair02Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row89 :
    digitsEq 111 (rowProduct (thirdRows 89) cubicRows 111) (pair02Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row90 :
    digitsEq 111 (rowProduct (thirdRows 90) cubicRows 111) (pair02Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row91 :
    digitsEq 111 (rowProduct (thirdRows 91) cubicRows 111) (pair02Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row92 :
    digitsEq 111 (rowProduct (thirdRows 92) cubicRows 111) (pair02Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row93 :
    digitsEq 111 (rowProduct (thirdRows 93) cubicRows 111) (pair02Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row94 :
    digitsEq 111 (rowProduct (thirdRows 94) cubicRows 111) (pair02Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row95 :
    digitsEq 111 (rowProduct (thirdRows 95) cubicRows 111) (pair02Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row96 :
    digitsEq 111 (rowProduct (thirdRows 96) cubicRows 111) (pair02Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row97 :
    digitsEq 111 (rowProduct (thirdRows 97) cubicRows 111) (pair02Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row98 :
    digitsEq 111 (rowProduct (thirdRows 98) cubicRows 111) (pair02Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row99 :
    digitsEq 111 (rowProduct (thirdRows 99) cubicRows 111) (pair02Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row100 :
    digitsEq 111 (rowProduct (thirdRows 100) cubicRows 111) (pair02Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row101 :
    digitsEq 111 (rowProduct (thirdRows 101) cubicRows 111) (pair02Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row102 :
    digitsEq 111 (rowProduct (thirdRows 102) cubicRows 111) (pair02Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row103 :
    digitsEq 111 (rowProduct (thirdRows 103) cubicRows 111) (pair02Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row104 :
    digitsEq 111 (rowProduct (thirdRows 104) cubicRows 111) (pair02Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row105 :
    digitsEq 111 (rowProduct (thirdRows 105) cubicRows 111) (pair02Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row106 :
    digitsEq 111 (rowProduct (thirdRows 106) cubicRows 111) (pair02Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row107 :
    digitsEq 111 (rowProduct (thirdRows 107) cubicRows 111) (pair02Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row108 :
    digitsEq 111 (rowProduct (thirdRows 108) cubicRows 111) (pair02Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row109 :
    digitsEq 111 (rowProduct (thirdRows 109) cubicRows 111) (pair02Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_row110 :
    digitsEq 111 (rowProduct (thirdRows 110) cubicRows 111) (pair02Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02rev_rows : ∀ i,
    digitsEq 111 (rowProduct (thirdRows i) cubicRows 111) (pair02Rows i) = true :=
  (Fin.cases pair02rev_row0
    (Fin.cases pair02rev_row1
    (Fin.cases pair02rev_row2
    (Fin.cases pair02rev_row3
    (Fin.cases pair02rev_row4
    (Fin.cases pair02rev_row5
    (Fin.cases pair02rev_row6
    (Fin.cases pair02rev_row7
    (Fin.cases pair02rev_row8
    (Fin.cases pair02rev_row9
    (Fin.cases pair02rev_row10
    (Fin.cases pair02rev_row11
    (Fin.cases pair02rev_row12
    (Fin.cases pair02rev_row13
    (Fin.cases pair02rev_row14
    (Fin.cases pair02rev_row15
    (Fin.cases pair02rev_row16
    (Fin.cases pair02rev_row17
    (Fin.cases pair02rev_row18
    (Fin.cases pair02rev_row19
    (Fin.cases pair02rev_row20
    (Fin.cases pair02rev_row21
    (Fin.cases pair02rev_row22
    (Fin.cases pair02rev_row23
    (Fin.cases pair02rev_row24
    (Fin.cases pair02rev_row25
    (Fin.cases pair02rev_row26
    (Fin.cases pair02rev_row27
    (Fin.cases pair02rev_row28
    (Fin.cases pair02rev_row29
    (Fin.cases pair02rev_row30
    (Fin.cases pair02rev_row31
    (Fin.cases pair02rev_row32
    (Fin.cases pair02rev_row33
    (Fin.cases pair02rev_row34
    (Fin.cases pair02rev_row35
    (Fin.cases pair02rev_row36
    (Fin.cases pair02rev_row37
    (Fin.cases pair02rev_row38
    (Fin.cases pair02rev_row39
    (Fin.cases pair02rev_row40
    (Fin.cases pair02rev_row41
    (Fin.cases pair02rev_row42
    (Fin.cases pair02rev_row43
    (Fin.cases pair02rev_row44
    (Fin.cases pair02rev_row45
    (Fin.cases pair02rev_row46
    (Fin.cases pair02rev_row47
    (Fin.cases pair02rev_row48
    (Fin.cases pair02rev_row49
    (Fin.cases pair02rev_row50
    (Fin.cases pair02rev_row51
    (Fin.cases pair02rev_row52
    (Fin.cases pair02rev_row53
    (Fin.cases pair02rev_row54
    (Fin.cases pair02rev_row55
    (Fin.cases pair02rev_row56
    (Fin.cases pair02rev_row57
    (Fin.cases pair02rev_row58
    (Fin.cases pair02rev_row59
    (Fin.cases pair02rev_row60
    (Fin.cases pair02rev_row61
    (Fin.cases pair02rev_row62
    (Fin.cases pair02rev_row63
    (Fin.cases pair02rev_row64
    (Fin.cases pair02rev_row65
    (Fin.cases pair02rev_row66
    (Fin.cases pair02rev_row67
    (Fin.cases pair02rev_row68
    (Fin.cases pair02rev_row69
    (Fin.cases pair02rev_row70
    (Fin.cases pair02rev_row71
    (Fin.cases pair02rev_row72
    (Fin.cases pair02rev_row73
    (Fin.cases pair02rev_row74
    (Fin.cases pair02rev_row75
    (Fin.cases pair02rev_row76
    (Fin.cases pair02rev_row77
    (Fin.cases pair02rev_row78
    (Fin.cases pair02rev_row79
    (Fin.cases pair02rev_row80
    (Fin.cases pair02rev_row81
    (Fin.cases pair02rev_row82
    (Fin.cases pair02rev_row83
    (Fin.cases pair02rev_row84
    (Fin.cases pair02rev_row85
    (Fin.cases pair02rev_row86
    (Fin.cases pair02rev_row87
    (Fin.cases pair02rev_row88
    (Fin.cases pair02rev_row89
    (Fin.cases pair02rev_row90
    (Fin.cases pair02rev_row91
    (Fin.cases pair02rev_row92
    (Fin.cases pair02rev_row93
    (Fin.cases pair02rev_row94
    (Fin.cases pair02rev_row95
    (Fin.cases pair02rev_row96
    (Fin.cases pair02rev_row97
    (Fin.cases pair02rev_row98
    (Fin.cases pair02rev_row99
    (Fin.cases pair02rev_row100
    (Fin.cases pair02rev_row101
    (Fin.cases pair02rev_row102
    (Fin.cases pair02rev_row103
    (Fin.cases pair02rev_row104
    (Fin.cases pair02rev_row105
    (Fin.cases pair02rev_row106
    (Fin.cases pair02rev_row107
    (Fin.cases pair02rev_row108
    (Fin.cases pair02rev_row109
    (Fin.cases pair02rev_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_pair02rev : thirdMatrix * cubicMatrix = pair02Matrix :=
  decode_mul _ _ _ third_small cubic_small pair02rev_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
