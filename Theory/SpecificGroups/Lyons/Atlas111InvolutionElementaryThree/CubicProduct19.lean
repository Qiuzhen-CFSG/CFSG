module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: third times second

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
private theorem pair12rev_row0 :
    digitsEq 111 (rowProduct (thirdRows 0) secondRows 111) (pair12Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row1 :
    digitsEq 111 (rowProduct (thirdRows 1) secondRows 111) (pair12Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row2 :
    digitsEq 111 (rowProduct (thirdRows 2) secondRows 111) (pair12Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row3 :
    digitsEq 111 (rowProduct (thirdRows 3) secondRows 111) (pair12Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row4 :
    digitsEq 111 (rowProduct (thirdRows 4) secondRows 111) (pair12Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row5 :
    digitsEq 111 (rowProduct (thirdRows 5) secondRows 111) (pair12Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row6 :
    digitsEq 111 (rowProduct (thirdRows 6) secondRows 111) (pair12Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row7 :
    digitsEq 111 (rowProduct (thirdRows 7) secondRows 111) (pair12Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row8 :
    digitsEq 111 (rowProduct (thirdRows 8) secondRows 111) (pair12Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row9 :
    digitsEq 111 (rowProduct (thirdRows 9) secondRows 111) (pair12Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row10 :
    digitsEq 111 (rowProduct (thirdRows 10) secondRows 111) (pair12Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row11 :
    digitsEq 111 (rowProduct (thirdRows 11) secondRows 111) (pair12Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row12 :
    digitsEq 111 (rowProduct (thirdRows 12) secondRows 111) (pair12Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row13 :
    digitsEq 111 (rowProduct (thirdRows 13) secondRows 111) (pair12Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row14 :
    digitsEq 111 (rowProduct (thirdRows 14) secondRows 111) (pair12Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row15 :
    digitsEq 111 (rowProduct (thirdRows 15) secondRows 111) (pair12Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row16 :
    digitsEq 111 (rowProduct (thirdRows 16) secondRows 111) (pair12Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row17 :
    digitsEq 111 (rowProduct (thirdRows 17) secondRows 111) (pair12Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row18 :
    digitsEq 111 (rowProduct (thirdRows 18) secondRows 111) (pair12Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row19 :
    digitsEq 111 (rowProduct (thirdRows 19) secondRows 111) (pair12Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row20 :
    digitsEq 111 (rowProduct (thirdRows 20) secondRows 111) (pair12Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row21 :
    digitsEq 111 (rowProduct (thirdRows 21) secondRows 111) (pair12Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row22 :
    digitsEq 111 (rowProduct (thirdRows 22) secondRows 111) (pair12Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row23 :
    digitsEq 111 (rowProduct (thirdRows 23) secondRows 111) (pair12Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row24 :
    digitsEq 111 (rowProduct (thirdRows 24) secondRows 111) (pair12Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row25 :
    digitsEq 111 (rowProduct (thirdRows 25) secondRows 111) (pair12Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row26 :
    digitsEq 111 (rowProduct (thirdRows 26) secondRows 111) (pair12Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row27 :
    digitsEq 111 (rowProduct (thirdRows 27) secondRows 111) (pair12Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row28 :
    digitsEq 111 (rowProduct (thirdRows 28) secondRows 111) (pair12Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row29 :
    digitsEq 111 (rowProduct (thirdRows 29) secondRows 111) (pair12Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row30 :
    digitsEq 111 (rowProduct (thirdRows 30) secondRows 111) (pair12Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row31 :
    digitsEq 111 (rowProduct (thirdRows 31) secondRows 111) (pair12Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row32 :
    digitsEq 111 (rowProduct (thirdRows 32) secondRows 111) (pair12Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row33 :
    digitsEq 111 (rowProduct (thirdRows 33) secondRows 111) (pair12Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row34 :
    digitsEq 111 (rowProduct (thirdRows 34) secondRows 111) (pair12Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row35 :
    digitsEq 111 (rowProduct (thirdRows 35) secondRows 111) (pair12Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row36 :
    digitsEq 111 (rowProduct (thirdRows 36) secondRows 111) (pair12Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row37 :
    digitsEq 111 (rowProduct (thirdRows 37) secondRows 111) (pair12Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row38 :
    digitsEq 111 (rowProduct (thirdRows 38) secondRows 111) (pair12Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row39 :
    digitsEq 111 (rowProduct (thirdRows 39) secondRows 111) (pair12Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row40 :
    digitsEq 111 (rowProduct (thirdRows 40) secondRows 111) (pair12Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row41 :
    digitsEq 111 (rowProduct (thirdRows 41) secondRows 111) (pair12Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row42 :
    digitsEq 111 (rowProduct (thirdRows 42) secondRows 111) (pair12Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row43 :
    digitsEq 111 (rowProduct (thirdRows 43) secondRows 111) (pair12Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row44 :
    digitsEq 111 (rowProduct (thirdRows 44) secondRows 111) (pair12Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row45 :
    digitsEq 111 (rowProduct (thirdRows 45) secondRows 111) (pair12Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row46 :
    digitsEq 111 (rowProduct (thirdRows 46) secondRows 111) (pair12Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row47 :
    digitsEq 111 (rowProduct (thirdRows 47) secondRows 111) (pair12Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row48 :
    digitsEq 111 (rowProduct (thirdRows 48) secondRows 111) (pair12Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row49 :
    digitsEq 111 (rowProduct (thirdRows 49) secondRows 111) (pair12Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row50 :
    digitsEq 111 (rowProduct (thirdRows 50) secondRows 111) (pair12Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row51 :
    digitsEq 111 (rowProduct (thirdRows 51) secondRows 111) (pair12Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row52 :
    digitsEq 111 (rowProduct (thirdRows 52) secondRows 111) (pair12Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row53 :
    digitsEq 111 (rowProduct (thirdRows 53) secondRows 111) (pair12Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row54 :
    digitsEq 111 (rowProduct (thirdRows 54) secondRows 111) (pair12Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row55 :
    digitsEq 111 (rowProduct (thirdRows 55) secondRows 111) (pair12Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row56 :
    digitsEq 111 (rowProduct (thirdRows 56) secondRows 111) (pair12Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row57 :
    digitsEq 111 (rowProduct (thirdRows 57) secondRows 111) (pair12Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row58 :
    digitsEq 111 (rowProduct (thirdRows 58) secondRows 111) (pair12Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row59 :
    digitsEq 111 (rowProduct (thirdRows 59) secondRows 111) (pair12Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row60 :
    digitsEq 111 (rowProduct (thirdRows 60) secondRows 111) (pair12Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row61 :
    digitsEq 111 (rowProduct (thirdRows 61) secondRows 111) (pair12Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row62 :
    digitsEq 111 (rowProduct (thirdRows 62) secondRows 111) (pair12Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row63 :
    digitsEq 111 (rowProduct (thirdRows 63) secondRows 111) (pair12Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row64 :
    digitsEq 111 (rowProduct (thirdRows 64) secondRows 111) (pair12Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row65 :
    digitsEq 111 (rowProduct (thirdRows 65) secondRows 111) (pair12Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row66 :
    digitsEq 111 (rowProduct (thirdRows 66) secondRows 111) (pair12Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row67 :
    digitsEq 111 (rowProduct (thirdRows 67) secondRows 111) (pair12Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row68 :
    digitsEq 111 (rowProduct (thirdRows 68) secondRows 111) (pair12Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row69 :
    digitsEq 111 (rowProduct (thirdRows 69) secondRows 111) (pair12Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row70 :
    digitsEq 111 (rowProduct (thirdRows 70) secondRows 111) (pair12Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row71 :
    digitsEq 111 (rowProduct (thirdRows 71) secondRows 111) (pair12Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row72 :
    digitsEq 111 (rowProduct (thirdRows 72) secondRows 111) (pair12Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row73 :
    digitsEq 111 (rowProduct (thirdRows 73) secondRows 111) (pair12Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row74 :
    digitsEq 111 (rowProduct (thirdRows 74) secondRows 111) (pair12Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row75 :
    digitsEq 111 (rowProduct (thirdRows 75) secondRows 111) (pair12Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row76 :
    digitsEq 111 (rowProduct (thirdRows 76) secondRows 111) (pair12Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row77 :
    digitsEq 111 (rowProduct (thirdRows 77) secondRows 111) (pair12Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row78 :
    digitsEq 111 (rowProduct (thirdRows 78) secondRows 111) (pair12Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row79 :
    digitsEq 111 (rowProduct (thirdRows 79) secondRows 111) (pair12Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row80 :
    digitsEq 111 (rowProduct (thirdRows 80) secondRows 111) (pair12Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row81 :
    digitsEq 111 (rowProduct (thirdRows 81) secondRows 111) (pair12Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row82 :
    digitsEq 111 (rowProduct (thirdRows 82) secondRows 111) (pair12Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row83 :
    digitsEq 111 (rowProduct (thirdRows 83) secondRows 111) (pair12Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row84 :
    digitsEq 111 (rowProduct (thirdRows 84) secondRows 111) (pair12Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row85 :
    digitsEq 111 (rowProduct (thirdRows 85) secondRows 111) (pair12Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row86 :
    digitsEq 111 (rowProduct (thirdRows 86) secondRows 111) (pair12Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row87 :
    digitsEq 111 (rowProduct (thirdRows 87) secondRows 111) (pair12Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row88 :
    digitsEq 111 (rowProduct (thirdRows 88) secondRows 111) (pair12Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row89 :
    digitsEq 111 (rowProduct (thirdRows 89) secondRows 111) (pair12Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row90 :
    digitsEq 111 (rowProduct (thirdRows 90) secondRows 111) (pair12Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row91 :
    digitsEq 111 (rowProduct (thirdRows 91) secondRows 111) (pair12Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row92 :
    digitsEq 111 (rowProduct (thirdRows 92) secondRows 111) (pair12Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row93 :
    digitsEq 111 (rowProduct (thirdRows 93) secondRows 111) (pair12Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row94 :
    digitsEq 111 (rowProduct (thirdRows 94) secondRows 111) (pair12Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row95 :
    digitsEq 111 (rowProduct (thirdRows 95) secondRows 111) (pair12Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row96 :
    digitsEq 111 (rowProduct (thirdRows 96) secondRows 111) (pair12Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row97 :
    digitsEq 111 (rowProduct (thirdRows 97) secondRows 111) (pair12Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row98 :
    digitsEq 111 (rowProduct (thirdRows 98) secondRows 111) (pair12Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row99 :
    digitsEq 111 (rowProduct (thirdRows 99) secondRows 111) (pair12Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row100 :
    digitsEq 111 (rowProduct (thirdRows 100) secondRows 111) (pair12Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row101 :
    digitsEq 111 (rowProduct (thirdRows 101) secondRows 111) (pair12Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row102 :
    digitsEq 111 (rowProduct (thirdRows 102) secondRows 111) (pair12Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row103 :
    digitsEq 111 (rowProduct (thirdRows 103) secondRows 111) (pair12Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row104 :
    digitsEq 111 (rowProduct (thirdRows 104) secondRows 111) (pair12Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row105 :
    digitsEq 111 (rowProduct (thirdRows 105) secondRows 111) (pair12Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row106 :
    digitsEq 111 (rowProduct (thirdRows 106) secondRows 111) (pair12Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row107 :
    digitsEq 111 (rowProduct (thirdRows 107) secondRows 111) (pair12Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row108 :
    digitsEq 111 (rowProduct (thirdRows 108) secondRows 111) (pair12Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row109 :
    digitsEq 111 (rowProduct (thirdRows 109) secondRows 111) (pair12Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_row110 :
    digitsEq 111 (rowProduct (thirdRows 110) secondRows 111) (pair12Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12rev_rows : ∀ i,
    digitsEq 111 (rowProduct (thirdRows i) secondRows 111) (pair12Rows i) = true :=
  (Fin.cases pair12rev_row0
    (Fin.cases pair12rev_row1
    (Fin.cases pair12rev_row2
    (Fin.cases pair12rev_row3
    (Fin.cases pair12rev_row4
    (Fin.cases pair12rev_row5
    (Fin.cases pair12rev_row6
    (Fin.cases pair12rev_row7
    (Fin.cases pair12rev_row8
    (Fin.cases pair12rev_row9
    (Fin.cases pair12rev_row10
    (Fin.cases pair12rev_row11
    (Fin.cases pair12rev_row12
    (Fin.cases pair12rev_row13
    (Fin.cases pair12rev_row14
    (Fin.cases pair12rev_row15
    (Fin.cases pair12rev_row16
    (Fin.cases pair12rev_row17
    (Fin.cases pair12rev_row18
    (Fin.cases pair12rev_row19
    (Fin.cases pair12rev_row20
    (Fin.cases pair12rev_row21
    (Fin.cases pair12rev_row22
    (Fin.cases pair12rev_row23
    (Fin.cases pair12rev_row24
    (Fin.cases pair12rev_row25
    (Fin.cases pair12rev_row26
    (Fin.cases pair12rev_row27
    (Fin.cases pair12rev_row28
    (Fin.cases pair12rev_row29
    (Fin.cases pair12rev_row30
    (Fin.cases pair12rev_row31
    (Fin.cases pair12rev_row32
    (Fin.cases pair12rev_row33
    (Fin.cases pair12rev_row34
    (Fin.cases pair12rev_row35
    (Fin.cases pair12rev_row36
    (Fin.cases pair12rev_row37
    (Fin.cases pair12rev_row38
    (Fin.cases pair12rev_row39
    (Fin.cases pair12rev_row40
    (Fin.cases pair12rev_row41
    (Fin.cases pair12rev_row42
    (Fin.cases pair12rev_row43
    (Fin.cases pair12rev_row44
    (Fin.cases pair12rev_row45
    (Fin.cases pair12rev_row46
    (Fin.cases pair12rev_row47
    (Fin.cases pair12rev_row48
    (Fin.cases pair12rev_row49
    (Fin.cases pair12rev_row50
    (Fin.cases pair12rev_row51
    (Fin.cases pair12rev_row52
    (Fin.cases pair12rev_row53
    (Fin.cases pair12rev_row54
    (Fin.cases pair12rev_row55
    (Fin.cases pair12rev_row56
    (Fin.cases pair12rev_row57
    (Fin.cases pair12rev_row58
    (Fin.cases pair12rev_row59
    (Fin.cases pair12rev_row60
    (Fin.cases pair12rev_row61
    (Fin.cases pair12rev_row62
    (Fin.cases pair12rev_row63
    (Fin.cases pair12rev_row64
    (Fin.cases pair12rev_row65
    (Fin.cases pair12rev_row66
    (Fin.cases pair12rev_row67
    (Fin.cases pair12rev_row68
    (Fin.cases pair12rev_row69
    (Fin.cases pair12rev_row70
    (Fin.cases pair12rev_row71
    (Fin.cases pair12rev_row72
    (Fin.cases pair12rev_row73
    (Fin.cases pair12rev_row74
    (Fin.cases pair12rev_row75
    (Fin.cases pair12rev_row76
    (Fin.cases pair12rev_row77
    (Fin.cases pair12rev_row78
    (Fin.cases pair12rev_row79
    (Fin.cases pair12rev_row80
    (Fin.cases pair12rev_row81
    (Fin.cases pair12rev_row82
    (Fin.cases pair12rev_row83
    (Fin.cases pair12rev_row84
    (Fin.cases pair12rev_row85
    (Fin.cases pair12rev_row86
    (Fin.cases pair12rev_row87
    (Fin.cases pair12rev_row88
    (Fin.cases pair12rev_row89
    (Fin.cases pair12rev_row90
    (Fin.cases pair12rev_row91
    (Fin.cases pair12rev_row92
    (Fin.cases pair12rev_row93
    (Fin.cases pair12rev_row94
    (Fin.cases pair12rev_row95
    (Fin.cases pair12rev_row96
    (Fin.cases pair12rev_row97
    (Fin.cases pair12rev_row98
    (Fin.cases pair12rev_row99
    (Fin.cases pair12rev_row100
    (Fin.cases pair12rev_row101
    (Fin.cases pair12rev_row102
    (Fin.cases pair12rev_row103
    (Fin.cases pair12rev_row104
    (Fin.cases pair12rev_row105
    (Fin.cases pair12rev_row106
    (Fin.cases pair12rev_row107
    (Fin.cases pair12rev_row108
    (Fin.cases pair12rev_row109
    (Fin.cases pair12rev_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_pair12rev : thirdMatrix * secondMatrix = pair12Matrix :=
  decode_mul _ _ _ third_small second_small pair12rev_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
