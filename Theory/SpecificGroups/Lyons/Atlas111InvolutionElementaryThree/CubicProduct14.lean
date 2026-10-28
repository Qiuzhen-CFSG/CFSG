module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: cubic times second

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
private theorem pair01_row0 :
    digitsEq 111 (rowProduct (cubicRows 0) secondRows 111) (pair01Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row1 :
    digitsEq 111 (rowProduct (cubicRows 1) secondRows 111) (pair01Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row2 :
    digitsEq 111 (rowProduct (cubicRows 2) secondRows 111) (pair01Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row3 :
    digitsEq 111 (rowProduct (cubicRows 3) secondRows 111) (pair01Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row4 :
    digitsEq 111 (rowProduct (cubicRows 4) secondRows 111) (pair01Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row5 :
    digitsEq 111 (rowProduct (cubicRows 5) secondRows 111) (pair01Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row6 :
    digitsEq 111 (rowProduct (cubicRows 6) secondRows 111) (pair01Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row7 :
    digitsEq 111 (rowProduct (cubicRows 7) secondRows 111) (pair01Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row8 :
    digitsEq 111 (rowProduct (cubicRows 8) secondRows 111) (pair01Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row9 :
    digitsEq 111 (rowProduct (cubicRows 9) secondRows 111) (pair01Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row10 :
    digitsEq 111 (rowProduct (cubicRows 10) secondRows 111) (pair01Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row11 :
    digitsEq 111 (rowProduct (cubicRows 11) secondRows 111) (pair01Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row12 :
    digitsEq 111 (rowProduct (cubicRows 12) secondRows 111) (pair01Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row13 :
    digitsEq 111 (rowProduct (cubicRows 13) secondRows 111) (pair01Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row14 :
    digitsEq 111 (rowProduct (cubicRows 14) secondRows 111) (pair01Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row15 :
    digitsEq 111 (rowProduct (cubicRows 15) secondRows 111) (pair01Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row16 :
    digitsEq 111 (rowProduct (cubicRows 16) secondRows 111) (pair01Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row17 :
    digitsEq 111 (rowProduct (cubicRows 17) secondRows 111) (pair01Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row18 :
    digitsEq 111 (rowProduct (cubicRows 18) secondRows 111) (pair01Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row19 :
    digitsEq 111 (rowProduct (cubicRows 19) secondRows 111) (pair01Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row20 :
    digitsEq 111 (rowProduct (cubicRows 20) secondRows 111) (pair01Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row21 :
    digitsEq 111 (rowProduct (cubicRows 21) secondRows 111) (pair01Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row22 :
    digitsEq 111 (rowProduct (cubicRows 22) secondRows 111) (pair01Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row23 :
    digitsEq 111 (rowProduct (cubicRows 23) secondRows 111) (pair01Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row24 :
    digitsEq 111 (rowProduct (cubicRows 24) secondRows 111) (pair01Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row25 :
    digitsEq 111 (rowProduct (cubicRows 25) secondRows 111) (pair01Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row26 :
    digitsEq 111 (rowProduct (cubicRows 26) secondRows 111) (pair01Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row27 :
    digitsEq 111 (rowProduct (cubicRows 27) secondRows 111) (pair01Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row28 :
    digitsEq 111 (rowProduct (cubicRows 28) secondRows 111) (pair01Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row29 :
    digitsEq 111 (rowProduct (cubicRows 29) secondRows 111) (pair01Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row30 :
    digitsEq 111 (rowProduct (cubicRows 30) secondRows 111) (pair01Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row31 :
    digitsEq 111 (rowProduct (cubicRows 31) secondRows 111) (pair01Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row32 :
    digitsEq 111 (rowProduct (cubicRows 32) secondRows 111) (pair01Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row33 :
    digitsEq 111 (rowProduct (cubicRows 33) secondRows 111) (pair01Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row34 :
    digitsEq 111 (rowProduct (cubicRows 34) secondRows 111) (pair01Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row35 :
    digitsEq 111 (rowProduct (cubicRows 35) secondRows 111) (pair01Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row36 :
    digitsEq 111 (rowProduct (cubicRows 36) secondRows 111) (pair01Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row37 :
    digitsEq 111 (rowProduct (cubicRows 37) secondRows 111) (pair01Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row38 :
    digitsEq 111 (rowProduct (cubicRows 38) secondRows 111) (pair01Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row39 :
    digitsEq 111 (rowProduct (cubicRows 39) secondRows 111) (pair01Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row40 :
    digitsEq 111 (rowProduct (cubicRows 40) secondRows 111) (pair01Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row41 :
    digitsEq 111 (rowProduct (cubicRows 41) secondRows 111) (pair01Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row42 :
    digitsEq 111 (rowProduct (cubicRows 42) secondRows 111) (pair01Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row43 :
    digitsEq 111 (rowProduct (cubicRows 43) secondRows 111) (pair01Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row44 :
    digitsEq 111 (rowProduct (cubicRows 44) secondRows 111) (pair01Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row45 :
    digitsEq 111 (rowProduct (cubicRows 45) secondRows 111) (pair01Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row46 :
    digitsEq 111 (rowProduct (cubicRows 46) secondRows 111) (pair01Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row47 :
    digitsEq 111 (rowProduct (cubicRows 47) secondRows 111) (pair01Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row48 :
    digitsEq 111 (rowProduct (cubicRows 48) secondRows 111) (pair01Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row49 :
    digitsEq 111 (rowProduct (cubicRows 49) secondRows 111) (pair01Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row50 :
    digitsEq 111 (rowProduct (cubicRows 50) secondRows 111) (pair01Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row51 :
    digitsEq 111 (rowProduct (cubicRows 51) secondRows 111) (pair01Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row52 :
    digitsEq 111 (rowProduct (cubicRows 52) secondRows 111) (pair01Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row53 :
    digitsEq 111 (rowProduct (cubicRows 53) secondRows 111) (pair01Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row54 :
    digitsEq 111 (rowProduct (cubicRows 54) secondRows 111) (pair01Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row55 :
    digitsEq 111 (rowProduct (cubicRows 55) secondRows 111) (pair01Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row56 :
    digitsEq 111 (rowProduct (cubicRows 56) secondRows 111) (pair01Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row57 :
    digitsEq 111 (rowProduct (cubicRows 57) secondRows 111) (pair01Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row58 :
    digitsEq 111 (rowProduct (cubicRows 58) secondRows 111) (pair01Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row59 :
    digitsEq 111 (rowProduct (cubicRows 59) secondRows 111) (pair01Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row60 :
    digitsEq 111 (rowProduct (cubicRows 60) secondRows 111) (pair01Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row61 :
    digitsEq 111 (rowProduct (cubicRows 61) secondRows 111) (pair01Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row62 :
    digitsEq 111 (rowProduct (cubicRows 62) secondRows 111) (pair01Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row63 :
    digitsEq 111 (rowProduct (cubicRows 63) secondRows 111) (pair01Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row64 :
    digitsEq 111 (rowProduct (cubicRows 64) secondRows 111) (pair01Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row65 :
    digitsEq 111 (rowProduct (cubicRows 65) secondRows 111) (pair01Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row66 :
    digitsEq 111 (rowProduct (cubicRows 66) secondRows 111) (pair01Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row67 :
    digitsEq 111 (rowProduct (cubicRows 67) secondRows 111) (pair01Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row68 :
    digitsEq 111 (rowProduct (cubicRows 68) secondRows 111) (pair01Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row69 :
    digitsEq 111 (rowProduct (cubicRows 69) secondRows 111) (pair01Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row70 :
    digitsEq 111 (rowProduct (cubicRows 70) secondRows 111) (pair01Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row71 :
    digitsEq 111 (rowProduct (cubicRows 71) secondRows 111) (pair01Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row72 :
    digitsEq 111 (rowProduct (cubicRows 72) secondRows 111) (pair01Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row73 :
    digitsEq 111 (rowProduct (cubicRows 73) secondRows 111) (pair01Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row74 :
    digitsEq 111 (rowProduct (cubicRows 74) secondRows 111) (pair01Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row75 :
    digitsEq 111 (rowProduct (cubicRows 75) secondRows 111) (pair01Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row76 :
    digitsEq 111 (rowProduct (cubicRows 76) secondRows 111) (pair01Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row77 :
    digitsEq 111 (rowProduct (cubicRows 77) secondRows 111) (pair01Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row78 :
    digitsEq 111 (rowProduct (cubicRows 78) secondRows 111) (pair01Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row79 :
    digitsEq 111 (rowProduct (cubicRows 79) secondRows 111) (pair01Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row80 :
    digitsEq 111 (rowProduct (cubicRows 80) secondRows 111) (pair01Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row81 :
    digitsEq 111 (rowProduct (cubicRows 81) secondRows 111) (pair01Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row82 :
    digitsEq 111 (rowProduct (cubicRows 82) secondRows 111) (pair01Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row83 :
    digitsEq 111 (rowProduct (cubicRows 83) secondRows 111) (pair01Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row84 :
    digitsEq 111 (rowProduct (cubicRows 84) secondRows 111) (pair01Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row85 :
    digitsEq 111 (rowProduct (cubicRows 85) secondRows 111) (pair01Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row86 :
    digitsEq 111 (rowProduct (cubicRows 86) secondRows 111) (pair01Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row87 :
    digitsEq 111 (rowProduct (cubicRows 87) secondRows 111) (pair01Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row88 :
    digitsEq 111 (rowProduct (cubicRows 88) secondRows 111) (pair01Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row89 :
    digitsEq 111 (rowProduct (cubicRows 89) secondRows 111) (pair01Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row90 :
    digitsEq 111 (rowProduct (cubicRows 90) secondRows 111) (pair01Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row91 :
    digitsEq 111 (rowProduct (cubicRows 91) secondRows 111) (pair01Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row92 :
    digitsEq 111 (rowProduct (cubicRows 92) secondRows 111) (pair01Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row93 :
    digitsEq 111 (rowProduct (cubicRows 93) secondRows 111) (pair01Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row94 :
    digitsEq 111 (rowProduct (cubicRows 94) secondRows 111) (pair01Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row95 :
    digitsEq 111 (rowProduct (cubicRows 95) secondRows 111) (pair01Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row96 :
    digitsEq 111 (rowProduct (cubicRows 96) secondRows 111) (pair01Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row97 :
    digitsEq 111 (rowProduct (cubicRows 97) secondRows 111) (pair01Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row98 :
    digitsEq 111 (rowProduct (cubicRows 98) secondRows 111) (pair01Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row99 :
    digitsEq 111 (rowProduct (cubicRows 99) secondRows 111) (pair01Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row100 :
    digitsEq 111 (rowProduct (cubicRows 100) secondRows 111) (pair01Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row101 :
    digitsEq 111 (rowProduct (cubicRows 101) secondRows 111) (pair01Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row102 :
    digitsEq 111 (rowProduct (cubicRows 102) secondRows 111) (pair01Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row103 :
    digitsEq 111 (rowProduct (cubicRows 103) secondRows 111) (pair01Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row104 :
    digitsEq 111 (rowProduct (cubicRows 104) secondRows 111) (pair01Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row105 :
    digitsEq 111 (rowProduct (cubicRows 105) secondRows 111) (pair01Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row106 :
    digitsEq 111 (rowProduct (cubicRows 106) secondRows 111) (pair01Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row107 :
    digitsEq 111 (rowProduct (cubicRows 107) secondRows 111) (pair01Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row108 :
    digitsEq 111 (rowProduct (cubicRows 108) secondRows 111) (pair01Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row109 :
    digitsEq 111 (rowProduct (cubicRows 109) secondRows 111) (pair01Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_row110 :
    digitsEq 111 (rowProduct (cubicRows 110) secondRows 111) (pair01Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair01_rows : ∀ i,
    digitsEq 111 (rowProduct (cubicRows i) secondRows 111) (pair01Rows i) = true :=
  (Fin.cases pair01_row0
    (Fin.cases pair01_row1
    (Fin.cases pair01_row2
    (Fin.cases pair01_row3
    (Fin.cases pair01_row4
    (Fin.cases pair01_row5
    (Fin.cases pair01_row6
    (Fin.cases pair01_row7
    (Fin.cases pair01_row8
    (Fin.cases pair01_row9
    (Fin.cases pair01_row10
    (Fin.cases pair01_row11
    (Fin.cases pair01_row12
    (Fin.cases pair01_row13
    (Fin.cases pair01_row14
    (Fin.cases pair01_row15
    (Fin.cases pair01_row16
    (Fin.cases pair01_row17
    (Fin.cases pair01_row18
    (Fin.cases pair01_row19
    (Fin.cases pair01_row20
    (Fin.cases pair01_row21
    (Fin.cases pair01_row22
    (Fin.cases pair01_row23
    (Fin.cases pair01_row24
    (Fin.cases pair01_row25
    (Fin.cases pair01_row26
    (Fin.cases pair01_row27
    (Fin.cases pair01_row28
    (Fin.cases pair01_row29
    (Fin.cases pair01_row30
    (Fin.cases pair01_row31
    (Fin.cases pair01_row32
    (Fin.cases pair01_row33
    (Fin.cases pair01_row34
    (Fin.cases pair01_row35
    (Fin.cases pair01_row36
    (Fin.cases pair01_row37
    (Fin.cases pair01_row38
    (Fin.cases pair01_row39
    (Fin.cases pair01_row40
    (Fin.cases pair01_row41
    (Fin.cases pair01_row42
    (Fin.cases pair01_row43
    (Fin.cases pair01_row44
    (Fin.cases pair01_row45
    (Fin.cases pair01_row46
    (Fin.cases pair01_row47
    (Fin.cases pair01_row48
    (Fin.cases pair01_row49
    (Fin.cases pair01_row50
    (Fin.cases pair01_row51
    (Fin.cases pair01_row52
    (Fin.cases pair01_row53
    (Fin.cases pair01_row54
    (Fin.cases pair01_row55
    (Fin.cases pair01_row56
    (Fin.cases pair01_row57
    (Fin.cases pair01_row58
    (Fin.cases pair01_row59
    (Fin.cases pair01_row60
    (Fin.cases pair01_row61
    (Fin.cases pair01_row62
    (Fin.cases pair01_row63
    (Fin.cases pair01_row64
    (Fin.cases pair01_row65
    (Fin.cases pair01_row66
    (Fin.cases pair01_row67
    (Fin.cases pair01_row68
    (Fin.cases pair01_row69
    (Fin.cases pair01_row70
    (Fin.cases pair01_row71
    (Fin.cases pair01_row72
    (Fin.cases pair01_row73
    (Fin.cases pair01_row74
    (Fin.cases pair01_row75
    (Fin.cases pair01_row76
    (Fin.cases pair01_row77
    (Fin.cases pair01_row78
    (Fin.cases pair01_row79
    (Fin.cases pair01_row80
    (Fin.cases pair01_row81
    (Fin.cases pair01_row82
    (Fin.cases pair01_row83
    (Fin.cases pair01_row84
    (Fin.cases pair01_row85
    (Fin.cases pair01_row86
    (Fin.cases pair01_row87
    (Fin.cases pair01_row88
    (Fin.cases pair01_row89
    (Fin.cases pair01_row90
    (Fin.cases pair01_row91
    (Fin.cases pair01_row92
    (Fin.cases pair01_row93
    (Fin.cases pair01_row94
    (Fin.cases pair01_row95
    (Fin.cases pair01_row96
    (Fin.cases pair01_row97
    (Fin.cases pair01_row98
    (Fin.cases pair01_row99
    (Fin.cases pair01_row100
    (Fin.cases pair01_row101
    (Fin.cases pair01_row102
    (Fin.cases pair01_row103
    (Fin.cases pair01_row104
    (Fin.cases pair01_row105
    (Fin.cases pair01_row106
    (Fin.cases pair01_row107
    (Fin.cases pair01_row108
    (Fin.cases pair01_row109
    (Fin.cases pair01_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_pair01 : cubicMatrix * secondMatrix = pair01Matrix :=
  decode_mul _ _ _ cubic_small second_small pair01_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
