module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: cubic times third

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
private theorem pair02_row0 :
    digitsEq 111 (rowProduct (cubicRows 0) thirdRows 111) (pair02Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row1 :
    digitsEq 111 (rowProduct (cubicRows 1) thirdRows 111) (pair02Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row2 :
    digitsEq 111 (rowProduct (cubicRows 2) thirdRows 111) (pair02Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row3 :
    digitsEq 111 (rowProduct (cubicRows 3) thirdRows 111) (pair02Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row4 :
    digitsEq 111 (rowProduct (cubicRows 4) thirdRows 111) (pair02Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row5 :
    digitsEq 111 (rowProduct (cubicRows 5) thirdRows 111) (pair02Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row6 :
    digitsEq 111 (rowProduct (cubicRows 6) thirdRows 111) (pair02Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row7 :
    digitsEq 111 (rowProduct (cubicRows 7) thirdRows 111) (pair02Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row8 :
    digitsEq 111 (rowProduct (cubicRows 8) thirdRows 111) (pair02Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row9 :
    digitsEq 111 (rowProduct (cubicRows 9) thirdRows 111) (pair02Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row10 :
    digitsEq 111 (rowProduct (cubicRows 10) thirdRows 111) (pair02Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row11 :
    digitsEq 111 (rowProduct (cubicRows 11) thirdRows 111) (pair02Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row12 :
    digitsEq 111 (rowProduct (cubicRows 12) thirdRows 111) (pair02Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row13 :
    digitsEq 111 (rowProduct (cubicRows 13) thirdRows 111) (pair02Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row14 :
    digitsEq 111 (rowProduct (cubicRows 14) thirdRows 111) (pair02Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row15 :
    digitsEq 111 (rowProduct (cubicRows 15) thirdRows 111) (pair02Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row16 :
    digitsEq 111 (rowProduct (cubicRows 16) thirdRows 111) (pair02Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row17 :
    digitsEq 111 (rowProduct (cubicRows 17) thirdRows 111) (pair02Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row18 :
    digitsEq 111 (rowProduct (cubicRows 18) thirdRows 111) (pair02Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row19 :
    digitsEq 111 (rowProduct (cubicRows 19) thirdRows 111) (pair02Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row20 :
    digitsEq 111 (rowProduct (cubicRows 20) thirdRows 111) (pair02Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row21 :
    digitsEq 111 (rowProduct (cubicRows 21) thirdRows 111) (pair02Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row22 :
    digitsEq 111 (rowProduct (cubicRows 22) thirdRows 111) (pair02Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row23 :
    digitsEq 111 (rowProduct (cubicRows 23) thirdRows 111) (pair02Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row24 :
    digitsEq 111 (rowProduct (cubicRows 24) thirdRows 111) (pair02Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row25 :
    digitsEq 111 (rowProduct (cubicRows 25) thirdRows 111) (pair02Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row26 :
    digitsEq 111 (rowProduct (cubicRows 26) thirdRows 111) (pair02Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row27 :
    digitsEq 111 (rowProduct (cubicRows 27) thirdRows 111) (pair02Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row28 :
    digitsEq 111 (rowProduct (cubicRows 28) thirdRows 111) (pair02Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row29 :
    digitsEq 111 (rowProduct (cubicRows 29) thirdRows 111) (pair02Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row30 :
    digitsEq 111 (rowProduct (cubicRows 30) thirdRows 111) (pair02Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row31 :
    digitsEq 111 (rowProduct (cubicRows 31) thirdRows 111) (pair02Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row32 :
    digitsEq 111 (rowProduct (cubicRows 32) thirdRows 111) (pair02Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row33 :
    digitsEq 111 (rowProduct (cubicRows 33) thirdRows 111) (pair02Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row34 :
    digitsEq 111 (rowProduct (cubicRows 34) thirdRows 111) (pair02Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row35 :
    digitsEq 111 (rowProduct (cubicRows 35) thirdRows 111) (pair02Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row36 :
    digitsEq 111 (rowProduct (cubicRows 36) thirdRows 111) (pair02Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row37 :
    digitsEq 111 (rowProduct (cubicRows 37) thirdRows 111) (pair02Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row38 :
    digitsEq 111 (rowProduct (cubicRows 38) thirdRows 111) (pair02Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row39 :
    digitsEq 111 (rowProduct (cubicRows 39) thirdRows 111) (pair02Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row40 :
    digitsEq 111 (rowProduct (cubicRows 40) thirdRows 111) (pair02Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row41 :
    digitsEq 111 (rowProduct (cubicRows 41) thirdRows 111) (pair02Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row42 :
    digitsEq 111 (rowProduct (cubicRows 42) thirdRows 111) (pair02Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row43 :
    digitsEq 111 (rowProduct (cubicRows 43) thirdRows 111) (pair02Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row44 :
    digitsEq 111 (rowProduct (cubicRows 44) thirdRows 111) (pair02Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row45 :
    digitsEq 111 (rowProduct (cubicRows 45) thirdRows 111) (pair02Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row46 :
    digitsEq 111 (rowProduct (cubicRows 46) thirdRows 111) (pair02Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row47 :
    digitsEq 111 (rowProduct (cubicRows 47) thirdRows 111) (pair02Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row48 :
    digitsEq 111 (rowProduct (cubicRows 48) thirdRows 111) (pair02Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row49 :
    digitsEq 111 (rowProduct (cubicRows 49) thirdRows 111) (pair02Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row50 :
    digitsEq 111 (rowProduct (cubicRows 50) thirdRows 111) (pair02Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row51 :
    digitsEq 111 (rowProduct (cubicRows 51) thirdRows 111) (pair02Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row52 :
    digitsEq 111 (rowProduct (cubicRows 52) thirdRows 111) (pair02Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row53 :
    digitsEq 111 (rowProduct (cubicRows 53) thirdRows 111) (pair02Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row54 :
    digitsEq 111 (rowProduct (cubicRows 54) thirdRows 111) (pair02Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row55 :
    digitsEq 111 (rowProduct (cubicRows 55) thirdRows 111) (pair02Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row56 :
    digitsEq 111 (rowProduct (cubicRows 56) thirdRows 111) (pair02Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row57 :
    digitsEq 111 (rowProduct (cubicRows 57) thirdRows 111) (pair02Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row58 :
    digitsEq 111 (rowProduct (cubicRows 58) thirdRows 111) (pair02Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row59 :
    digitsEq 111 (rowProduct (cubicRows 59) thirdRows 111) (pair02Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row60 :
    digitsEq 111 (rowProduct (cubicRows 60) thirdRows 111) (pair02Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row61 :
    digitsEq 111 (rowProduct (cubicRows 61) thirdRows 111) (pair02Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row62 :
    digitsEq 111 (rowProduct (cubicRows 62) thirdRows 111) (pair02Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row63 :
    digitsEq 111 (rowProduct (cubicRows 63) thirdRows 111) (pair02Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row64 :
    digitsEq 111 (rowProduct (cubicRows 64) thirdRows 111) (pair02Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row65 :
    digitsEq 111 (rowProduct (cubicRows 65) thirdRows 111) (pair02Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row66 :
    digitsEq 111 (rowProduct (cubicRows 66) thirdRows 111) (pair02Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row67 :
    digitsEq 111 (rowProduct (cubicRows 67) thirdRows 111) (pair02Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row68 :
    digitsEq 111 (rowProduct (cubicRows 68) thirdRows 111) (pair02Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row69 :
    digitsEq 111 (rowProduct (cubicRows 69) thirdRows 111) (pair02Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row70 :
    digitsEq 111 (rowProduct (cubicRows 70) thirdRows 111) (pair02Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row71 :
    digitsEq 111 (rowProduct (cubicRows 71) thirdRows 111) (pair02Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row72 :
    digitsEq 111 (rowProduct (cubicRows 72) thirdRows 111) (pair02Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row73 :
    digitsEq 111 (rowProduct (cubicRows 73) thirdRows 111) (pair02Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row74 :
    digitsEq 111 (rowProduct (cubicRows 74) thirdRows 111) (pair02Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row75 :
    digitsEq 111 (rowProduct (cubicRows 75) thirdRows 111) (pair02Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row76 :
    digitsEq 111 (rowProduct (cubicRows 76) thirdRows 111) (pair02Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row77 :
    digitsEq 111 (rowProduct (cubicRows 77) thirdRows 111) (pair02Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row78 :
    digitsEq 111 (rowProduct (cubicRows 78) thirdRows 111) (pair02Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row79 :
    digitsEq 111 (rowProduct (cubicRows 79) thirdRows 111) (pair02Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row80 :
    digitsEq 111 (rowProduct (cubicRows 80) thirdRows 111) (pair02Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row81 :
    digitsEq 111 (rowProduct (cubicRows 81) thirdRows 111) (pair02Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row82 :
    digitsEq 111 (rowProduct (cubicRows 82) thirdRows 111) (pair02Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row83 :
    digitsEq 111 (rowProduct (cubicRows 83) thirdRows 111) (pair02Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row84 :
    digitsEq 111 (rowProduct (cubicRows 84) thirdRows 111) (pair02Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row85 :
    digitsEq 111 (rowProduct (cubicRows 85) thirdRows 111) (pair02Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row86 :
    digitsEq 111 (rowProduct (cubicRows 86) thirdRows 111) (pair02Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row87 :
    digitsEq 111 (rowProduct (cubicRows 87) thirdRows 111) (pair02Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row88 :
    digitsEq 111 (rowProduct (cubicRows 88) thirdRows 111) (pair02Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row89 :
    digitsEq 111 (rowProduct (cubicRows 89) thirdRows 111) (pair02Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row90 :
    digitsEq 111 (rowProduct (cubicRows 90) thirdRows 111) (pair02Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row91 :
    digitsEq 111 (rowProduct (cubicRows 91) thirdRows 111) (pair02Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row92 :
    digitsEq 111 (rowProduct (cubicRows 92) thirdRows 111) (pair02Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row93 :
    digitsEq 111 (rowProduct (cubicRows 93) thirdRows 111) (pair02Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row94 :
    digitsEq 111 (rowProduct (cubicRows 94) thirdRows 111) (pair02Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row95 :
    digitsEq 111 (rowProduct (cubicRows 95) thirdRows 111) (pair02Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row96 :
    digitsEq 111 (rowProduct (cubicRows 96) thirdRows 111) (pair02Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row97 :
    digitsEq 111 (rowProduct (cubicRows 97) thirdRows 111) (pair02Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row98 :
    digitsEq 111 (rowProduct (cubicRows 98) thirdRows 111) (pair02Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row99 :
    digitsEq 111 (rowProduct (cubicRows 99) thirdRows 111) (pair02Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row100 :
    digitsEq 111 (rowProduct (cubicRows 100) thirdRows 111) (pair02Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row101 :
    digitsEq 111 (rowProduct (cubicRows 101) thirdRows 111) (pair02Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row102 :
    digitsEq 111 (rowProduct (cubicRows 102) thirdRows 111) (pair02Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row103 :
    digitsEq 111 (rowProduct (cubicRows 103) thirdRows 111) (pair02Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row104 :
    digitsEq 111 (rowProduct (cubicRows 104) thirdRows 111) (pair02Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row105 :
    digitsEq 111 (rowProduct (cubicRows 105) thirdRows 111) (pair02Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row106 :
    digitsEq 111 (rowProduct (cubicRows 106) thirdRows 111) (pair02Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row107 :
    digitsEq 111 (rowProduct (cubicRows 107) thirdRows 111) (pair02Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row108 :
    digitsEq 111 (rowProduct (cubicRows 108) thirdRows 111) (pair02Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row109 :
    digitsEq 111 (rowProduct (cubicRows 109) thirdRows 111) (pair02Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_row110 :
    digitsEq 111 (rowProduct (cubicRows 110) thirdRows 111) (pair02Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair02_rows : ∀ i,
    digitsEq 111 (rowProduct (cubicRows i) thirdRows 111) (pair02Rows i) = true :=
  (Fin.cases pair02_row0
    (Fin.cases pair02_row1
    (Fin.cases pair02_row2
    (Fin.cases pair02_row3
    (Fin.cases pair02_row4
    (Fin.cases pair02_row5
    (Fin.cases pair02_row6
    (Fin.cases pair02_row7
    (Fin.cases pair02_row8
    (Fin.cases pair02_row9
    (Fin.cases pair02_row10
    (Fin.cases pair02_row11
    (Fin.cases pair02_row12
    (Fin.cases pair02_row13
    (Fin.cases pair02_row14
    (Fin.cases pair02_row15
    (Fin.cases pair02_row16
    (Fin.cases pair02_row17
    (Fin.cases pair02_row18
    (Fin.cases pair02_row19
    (Fin.cases pair02_row20
    (Fin.cases pair02_row21
    (Fin.cases pair02_row22
    (Fin.cases pair02_row23
    (Fin.cases pair02_row24
    (Fin.cases pair02_row25
    (Fin.cases pair02_row26
    (Fin.cases pair02_row27
    (Fin.cases pair02_row28
    (Fin.cases pair02_row29
    (Fin.cases pair02_row30
    (Fin.cases pair02_row31
    (Fin.cases pair02_row32
    (Fin.cases pair02_row33
    (Fin.cases pair02_row34
    (Fin.cases pair02_row35
    (Fin.cases pair02_row36
    (Fin.cases pair02_row37
    (Fin.cases pair02_row38
    (Fin.cases pair02_row39
    (Fin.cases pair02_row40
    (Fin.cases pair02_row41
    (Fin.cases pair02_row42
    (Fin.cases pair02_row43
    (Fin.cases pair02_row44
    (Fin.cases pair02_row45
    (Fin.cases pair02_row46
    (Fin.cases pair02_row47
    (Fin.cases pair02_row48
    (Fin.cases pair02_row49
    (Fin.cases pair02_row50
    (Fin.cases pair02_row51
    (Fin.cases pair02_row52
    (Fin.cases pair02_row53
    (Fin.cases pair02_row54
    (Fin.cases pair02_row55
    (Fin.cases pair02_row56
    (Fin.cases pair02_row57
    (Fin.cases pair02_row58
    (Fin.cases pair02_row59
    (Fin.cases pair02_row60
    (Fin.cases pair02_row61
    (Fin.cases pair02_row62
    (Fin.cases pair02_row63
    (Fin.cases pair02_row64
    (Fin.cases pair02_row65
    (Fin.cases pair02_row66
    (Fin.cases pair02_row67
    (Fin.cases pair02_row68
    (Fin.cases pair02_row69
    (Fin.cases pair02_row70
    (Fin.cases pair02_row71
    (Fin.cases pair02_row72
    (Fin.cases pair02_row73
    (Fin.cases pair02_row74
    (Fin.cases pair02_row75
    (Fin.cases pair02_row76
    (Fin.cases pair02_row77
    (Fin.cases pair02_row78
    (Fin.cases pair02_row79
    (Fin.cases pair02_row80
    (Fin.cases pair02_row81
    (Fin.cases pair02_row82
    (Fin.cases pair02_row83
    (Fin.cases pair02_row84
    (Fin.cases pair02_row85
    (Fin.cases pair02_row86
    (Fin.cases pair02_row87
    (Fin.cases pair02_row88
    (Fin.cases pair02_row89
    (Fin.cases pair02_row90
    (Fin.cases pair02_row91
    (Fin.cases pair02_row92
    (Fin.cases pair02_row93
    (Fin.cases pair02_row94
    (Fin.cases pair02_row95
    (Fin.cases pair02_row96
    (Fin.cases pair02_row97
    (Fin.cases pair02_row98
    (Fin.cases pair02_row99
    (Fin.cases pair02_row100
    (Fin.cases pair02_row101
    (Fin.cases pair02_row102
    (Fin.cases pair02_row103
    (Fin.cases pair02_row104
    (Fin.cases pair02_row105
    (Fin.cases pair02_row106
    (Fin.cases pair02_row107
    (Fin.cases pair02_row108
    (Fin.cases pair02_row109
    (Fin.cases pair02_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_pair02 : cubicMatrix * thirdMatrix = pair02Matrix :=
  decode_mul _ _ _ cubic_small third_small pair02_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
