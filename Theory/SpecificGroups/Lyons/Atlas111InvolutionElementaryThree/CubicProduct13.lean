module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: conjugating times third

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
private theorem wThird_row0 :
    digitsEq 111 (rowProduct (conjugatingRows 0) thirdRows 111) (cwRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row1 :
    digitsEq 111 (rowProduct (conjugatingRows 1) thirdRows 111) (cwRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row2 :
    digitsEq 111 (rowProduct (conjugatingRows 2) thirdRows 111) (cwRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row3 :
    digitsEq 111 (rowProduct (conjugatingRows 3) thirdRows 111) (cwRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row4 :
    digitsEq 111 (rowProduct (conjugatingRows 4) thirdRows 111) (cwRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row5 :
    digitsEq 111 (rowProduct (conjugatingRows 5) thirdRows 111) (cwRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row6 :
    digitsEq 111 (rowProduct (conjugatingRows 6) thirdRows 111) (cwRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row7 :
    digitsEq 111 (rowProduct (conjugatingRows 7) thirdRows 111) (cwRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row8 :
    digitsEq 111 (rowProduct (conjugatingRows 8) thirdRows 111) (cwRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row9 :
    digitsEq 111 (rowProduct (conjugatingRows 9) thirdRows 111) (cwRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row10 :
    digitsEq 111 (rowProduct (conjugatingRows 10) thirdRows 111) (cwRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row11 :
    digitsEq 111 (rowProduct (conjugatingRows 11) thirdRows 111) (cwRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row12 :
    digitsEq 111 (rowProduct (conjugatingRows 12) thirdRows 111) (cwRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row13 :
    digitsEq 111 (rowProduct (conjugatingRows 13) thirdRows 111) (cwRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row14 :
    digitsEq 111 (rowProduct (conjugatingRows 14) thirdRows 111) (cwRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row15 :
    digitsEq 111 (rowProduct (conjugatingRows 15) thirdRows 111) (cwRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row16 :
    digitsEq 111 (rowProduct (conjugatingRows 16) thirdRows 111) (cwRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row17 :
    digitsEq 111 (rowProduct (conjugatingRows 17) thirdRows 111) (cwRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row18 :
    digitsEq 111 (rowProduct (conjugatingRows 18) thirdRows 111) (cwRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row19 :
    digitsEq 111 (rowProduct (conjugatingRows 19) thirdRows 111) (cwRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row20 :
    digitsEq 111 (rowProduct (conjugatingRows 20) thirdRows 111) (cwRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row21 :
    digitsEq 111 (rowProduct (conjugatingRows 21) thirdRows 111) (cwRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row22 :
    digitsEq 111 (rowProduct (conjugatingRows 22) thirdRows 111) (cwRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row23 :
    digitsEq 111 (rowProduct (conjugatingRows 23) thirdRows 111) (cwRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row24 :
    digitsEq 111 (rowProduct (conjugatingRows 24) thirdRows 111) (cwRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row25 :
    digitsEq 111 (rowProduct (conjugatingRows 25) thirdRows 111) (cwRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row26 :
    digitsEq 111 (rowProduct (conjugatingRows 26) thirdRows 111) (cwRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row27 :
    digitsEq 111 (rowProduct (conjugatingRows 27) thirdRows 111) (cwRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row28 :
    digitsEq 111 (rowProduct (conjugatingRows 28) thirdRows 111) (cwRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row29 :
    digitsEq 111 (rowProduct (conjugatingRows 29) thirdRows 111) (cwRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row30 :
    digitsEq 111 (rowProduct (conjugatingRows 30) thirdRows 111) (cwRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row31 :
    digitsEq 111 (rowProduct (conjugatingRows 31) thirdRows 111) (cwRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row32 :
    digitsEq 111 (rowProduct (conjugatingRows 32) thirdRows 111) (cwRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row33 :
    digitsEq 111 (rowProduct (conjugatingRows 33) thirdRows 111) (cwRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row34 :
    digitsEq 111 (rowProduct (conjugatingRows 34) thirdRows 111) (cwRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row35 :
    digitsEq 111 (rowProduct (conjugatingRows 35) thirdRows 111) (cwRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row36 :
    digitsEq 111 (rowProduct (conjugatingRows 36) thirdRows 111) (cwRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row37 :
    digitsEq 111 (rowProduct (conjugatingRows 37) thirdRows 111) (cwRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row38 :
    digitsEq 111 (rowProduct (conjugatingRows 38) thirdRows 111) (cwRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row39 :
    digitsEq 111 (rowProduct (conjugatingRows 39) thirdRows 111) (cwRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row40 :
    digitsEq 111 (rowProduct (conjugatingRows 40) thirdRows 111) (cwRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row41 :
    digitsEq 111 (rowProduct (conjugatingRows 41) thirdRows 111) (cwRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row42 :
    digitsEq 111 (rowProduct (conjugatingRows 42) thirdRows 111) (cwRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row43 :
    digitsEq 111 (rowProduct (conjugatingRows 43) thirdRows 111) (cwRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row44 :
    digitsEq 111 (rowProduct (conjugatingRows 44) thirdRows 111) (cwRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row45 :
    digitsEq 111 (rowProduct (conjugatingRows 45) thirdRows 111) (cwRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row46 :
    digitsEq 111 (rowProduct (conjugatingRows 46) thirdRows 111) (cwRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row47 :
    digitsEq 111 (rowProduct (conjugatingRows 47) thirdRows 111) (cwRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row48 :
    digitsEq 111 (rowProduct (conjugatingRows 48) thirdRows 111) (cwRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row49 :
    digitsEq 111 (rowProduct (conjugatingRows 49) thirdRows 111) (cwRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row50 :
    digitsEq 111 (rowProduct (conjugatingRows 50) thirdRows 111) (cwRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row51 :
    digitsEq 111 (rowProduct (conjugatingRows 51) thirdRows 111) (cwRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row52 :
    digitsEq 111 (rowProduct (conjugatingRows 52) thirdRows 111) (cwRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row53 :
    digitsEq 111 (rowProduct (conjugatingRows 53) thirdRows 111) (cwRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row54 :
    digitsEq 111 (rowProduct (conjugatingRows 54) thirdRows 111) (cwRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row55 :
    digitsEq 111 (rowProduct (conjugatingRows 55) thirdRows 111) (cwRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row56 :
    digitsEq 111 (rowProduct (conjugatingRows 56) thirdRows 111) (cwRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row57 :
    digitsEq 111 (rowProduct (conjugatingRows 57) thirdRows 111) (cwRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row58 :
    digitsEq 111 (rowProduct (conjugatingRows 58) thirdRows 111) (cwRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row59 :
    digitsEq 111 (rowProduct (conjugatingRows 59) thirdRows 111) (cwRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row60 :
    digitsEq 111 (rowProduct (conjugatingRows 60) thirdRows 111) (cwRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row61 :
    digitsEq 111 (rowProduct (conjugatingRows 61) thirdRows 111) (cwRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row62 :
    digitsEq 111 (rowProduct (conjugatingRows 62) thirdRows 111) (cwRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row63 :
    digitsEq 111 (rowProduct (conjugatingRows 63) thirdRows 111) (cwRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row64 :
    digitsEq 111 (rowProduct (conjugatingRows 64) thirdRows 111) (cwRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row65 :
    digitsEq 111 (rowProduct (conjugatingRows 65) thirdRows 111) (cwRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row66 :
    digitsEq 111 (rowProduct (conjugatingRows 66) thirdRows 111) (cwRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row67 :
    digitsEq 111 (rowProduct (conjugatingRows 67) thirdRows 111) (cwRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row68 :
    digitsEq 111 (rowProduct (conjugatingRows 68) thirdRows 111) (cwRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row69 :
    digitsEq 111 (rowProduct (conjugatingRows 69) thirdRows 111) (cwRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row70 :
    digitsEq 111 (rowProduct (conjugatingRows 70) thirdRows 111) (cwRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row71 :
    digitsEq 111 (rowProduct (conjugatingRows 71) thirdRows 111) (cwRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row72 :
    digitsEq 111 (rowProduct (conjugatingRows 72) thirdRows 111) (cwRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row73 :
    digitsEq 111 (rowProduct (conjugatingRows 73) thirdRows 111) (cwRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row74 :
    digitsEq 111 (rowProduct (conjugatingRows 74) thirdRows 111) (cwRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row75 :
    digitsEq 111 (rowProduct (conjugatingRows 75) thirdRows 111) (cwRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row76 :
    digitsEq 111 (rowProduct (conjugatingRows 76) thirdRows 111) (cwRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row77 :
    digitsEq 111 (rowProduct (conjugatingRows 77) thirdRows 111) (cwRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row78 :
    digitsEq 111 (rowProduct (conjugatingRows 78) thirdRows 111) (cwRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row79 :
    digitsEq 111 (rowProduct (conjugatingRows 79) thirdRows 111) (cwRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row80 :
    digitsEq 111 (rowProduct (conjugatingRows 80) thirdRows 111) (cwRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row81 :
    digitsEq 111 (rowProduct (conjugatingRows 81) thirdRows 111) (cwRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row82 :
    digitsEq 111 (rowProduct (conjugatingRows 82) thirdRows 111) (cwRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row83 :
    digitsEq 111 (rowProduct (conjugatingRows 83) thirdRows 111) (cwRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row84 :
    digitsEq 111 (rowProduct (conjugatingRows 84) thirdRows 111) (cwRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row85 :
    digitsEq 111 (rowProduct (conjugatingRows 85) thirdRows 111) (cwRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row86 :
    digitsEq 111 (rowProduct (conjugatingRows 86) thirdRows 111) (cwRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row87 :
    digitsEq 111 (rowProduct (conjugatingRows 87) thirdRows 111) (cwRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row88 :
    digitsEq 111 (rowProduct (conjugatingRows 88) thirdRows 111) (cwRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row89 :
    digitsEq 111 (rowProduct (conjugatingRows 89) thirdRows 111) (cwRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row90 :
    digitsEq 111 (rowProduct (conjugatingRows 90) thirdRows 111) (cwRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row91 :
    digitsEq 111 (rowProduct (conjugatingRows 91) thirdRows 111) (cwRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row92 :
    digitsEq 111 (rowProduct (conjugatingRows 92) thirdRows 111) (cwRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row93 :
    digitsEq 111 (rowProduct (conjugatingRows 93) thirdRows 111) (cwRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row94 :
    digitsEq 111 (rowProduct (conjugatingRows 94) thirdRows 111) (cwRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row95 :
    digitsEq 111 (rowProduct (conjugatingRows 95) thirdRows 111) (cwRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row96 :
    digitsEq 111 (rowProduct (conjugatingRows 96) thirdRows 111) (cwRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row97 :
    digitsEq 111 (rowProduct (conjugatingRows 97) thirdRows 111) (cwRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row98 :
    digitsEq 111 (rowProduct (conjugatingRows 98) thirdRows 111) (cwRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row99 :
    digitsEq 111 (rowProduct (conjugatingRows 99) thirdRows 111) (cwRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row100 :
    digitsEq 111 (rowProduct (conjugatingRows 100) thirdRows 111) (cwRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row101 :
    digitsEq 111 (rowProduct (conjugatingRows 101) thirdRows 111) (cwRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row102 :
    digitsEq 111 (rowProduct (conjugatingRows 102) thirdRows 111) (cwRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row103 :
    digitsEq 111 (rowProduct (conjugatingRows 103) thirdRows 111) (cwRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row104 :
    digitsEq 111 (rowProduct (conjugatingRows 104) thirdRows 111) (cwRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row105 :
    digitsEq 111 (rowProduct (conjugatingRows 105) thirdRows 111) (cwRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row106 :
    digitsEq 111 (rowProduct (conjugatingRows 106) thirdRows 111) (cwRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row107 :
    digitsEq 111 (rowProduct (conjugatingRows 107) thirdRows 111) (cwRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row108 :
    digitsEq 111 (rowProduct (conjugatingRows 108) thirdRows 111) (cwRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row109 :
    digitsEq 111 (rowProduct (conjugatingRows 109) thirdRows 111) (cwRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_row110 :
    digitsEq 111 (rowProduct (conjugatingRows 110) thirdRows 111) (cwRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem wThird_rows : ∀ i,
    digitsEq 111 (rowProduct (conjugatingRows i) thirdRows 111) (cwRows i) = true :=
  (Fin.cases wThird_row0
    (Fin.cases wThird_row1
    (Fin.cases wThird_row2
    (Fin.cases wThird_row3
    (Fin.cases wThird_row4
    (Fin.cases wThird_row5
    (Fin.cases wThird_row6
    (Fin.cases wThird_row7
    (Fin.cases wThird_row8
    (Fin.cases wThird_row9
    (Fin.cases wThird_row10
    (Fin.cases wThird_row11
    (Fin.cases wThird_row12
    (Fin.cases wThird_row13
    (Fin.cases wThird_row14
    (Fin.cases wThird_row15
    (Fin.cases wThird_row16
    (Fin.cases wThird_row17
    (Fin.cases wThird_row18
    (Fin.cases wThird_row19
    (Fin.cases wThird_row20
    (Fin.cases wThird_row21
    (Fin.cases wThird_row22
    (Fin.cases wThird_row23
    (Fin.cases wThird_row24
    (Fin.cases wThird_row25
    (Fin.cases wThird_row26
    (Fin.cases wThird_row27
    (Fin.cases wThird_row28
    (Fin.cases wThird_row29
    (Fin.cases wThird_row30
    (Fin.cases wThird_row31
    (Fin.cases wThird_row32
    (Fin.cases wThird_row33
    (Fin.cases wThird_row34
    (Fin.cases wThird_row35
    (Fin.cases wThird_row36
    (Fin.cases wThird_row37
    (Fin.cases wThird_row38
    (Fin.cases wThird_row39
    (Fin.cases wThird_row40
    (Fin.cases wThird_row41
    (Fin.cases wThird_row42
    (Fin.cases wThird_row43
    (Fin.cases wThird_row44
    (Fin.cases wThird_row45
    (Fin.cases wThird_row46
    (Fin.cases wThird_row47
    (Fin.cases wThird_row48
    (Fin.cases wThird_row49
    (Fin.cases wThird_row50
    (Fin.cases wThird_row51
    (Fin.cases wThird_row52
    (Fin.cases wThird_row53
    (Fin.cases wThird_row54
    (Fin.cases wThird_row55
    (Fin.cases wThird_row56
    (Fin.cases wThird_row57
    (Fin.cases wThird_row58
    (Fin.cases wThird_row59
    (Fin.cases wThird_row60
    (Fin.cases wThird_row61
    (Fin.cases wThird_row62
    (Fin.cases wThird_row63
    (Fin.cases wThird_row64
    (Fin.cases wThird_row65
    (Fin.cases wThird_row66
    (Fin.cases wThird_row67
    (Fin.cases wThird_row68
    (Fin.cases wThird_row69
    (Fin.cases wThird_row70
    (Fin.cases wThird_row71
    (Fin.cases wThird_row72
    (Fin.cases wThird_row73
    (Fin.cases wThird_row74
    (Fin.cases wThird_row75
    (Fin.cases wThird_row76
    (Fin.cases wThird_row77
    (Fin.cases wThird_row78
    (Fin.cases wThird_row79
    (Fin.cases wThird_row80
    (Fin.cases wThird_row81
    (Fin.cases wThird_row82
    (Fin.cases wThird_row83
    (Fin.cases wThird_row84
    (Fin.cases wThird_row85
    (Fin.cases wThird_row86
    (Fin.cases wThird_row87
    (Fin.cases wThird_row88
    (Fin.cases wThird_row89
    (Fin.cases wThird_row90
    (Fin.cases wThird_row91
    (Fin.cases wThird_row92
    (Fin.cases wThird_row93
    (Fin.cases wThird_row94
    (Fin.cases wThird_row95
    (Fin.cases wThird_row96
    (Fin.cases wThird_row97
    (Fin.cases wThird_row98
    (Fin.cases wThird_row99
    (Fin.cases wThird_row100
    (Fin.cases wThird_row101
    (Fin.cases wThird_row102
    (Fin.cases wThird_row103
    (Fin.cases wThird_row104
    (Fin.cases wThird_row105
    (Fin.cases wThird_row106
    (Fin.cases wThird_row107
    (Fin.cases wThird_row108
    (Fin.cases wThird_row109
    (Fin.cases wThird_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_wThird : conjugatingMatrix * thirdMatrix = cwMatrix :=
  decode_mul _ _ _ conjugating_small third_small wThird_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
