module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: yx2y times ab

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
private theorem conjugating_row0 :
    digitsEq 111 (rowProduct (yx2yRows 0) abRows 111) (conjugatingRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row1 :
    digitsEq 111 (rowProduct (yx2yRows 1) abRows 111) (conjugatingRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row2 :
    digitsEq 111 (rowProduct (yx2yRows 2) abRows 111) (conjugatingRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row3 :
    digitsEq 111 (rowProduct (yx2yRows 3) abRows 111) (conjugatingRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row4 :
    digitsEq 111 (rowProduct (yx2yRows 4) abRows 111) (conjugatingRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row5 :
    digitsEq 111 (rowProduct (yx2yRows 5) abRows 111) (conjugatingRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row6 :
    digitsEq 111 (rowProduct (yx2yRows 6) abRows 111) (conjugatingRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row7 :
    digitsEq 111 (rowProduct (yx2yRows 7) abRows 111) (conjugatingRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row8 :
    digitsEq 111 (rowProduct (yx2yRows 8) abRows 111) (conjugatingRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row9 :
    digitsEq 111 (rowProduct (yx2yRows 9) abRows 111) (conjugatingRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row10 :
    digitsEq 111 (rowProduct (yx2yRows 10) abRows 111) (conjugatingRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row11 :
    digitsEq 111 (rowProduct (yx2yRows 11) abRows 111) (conjugatingRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row12 :
    digitsEq 111 (rowProduct (yx2yRows 12) abRows 111) (conjugatingRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row13 :
    digitsEq 111 (rowProduct (yx2yRows 13) abRows 111) (conjugatingRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row14 :
    digitsEq 111 (rowProduct (yx2yRows 14) abRows 111) (conjugatingRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row15 :
    digitsEq 111 (rowProduct (yx2yRows 15) abRows 111) (conjugatingRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row16 :
    digitsEq 111 (rowProduct (yx2yRows 16) abRows 111) (conjugatingRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row17 :
    digitsEq 111 (rowProduct (yx2yRows 17) abRows 111) (conjugatingRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row18 :
    digitsEq 111 (rowProduct (yx2yRows 18) abRows 111) (conjugatingRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row19 :
    digitsEq 111 (rowProduct (yx2yRows 19) abRows 111) (conjugatingRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row20 :
    digitsEq 111 (rowProduct (yx2yRows 20) abRows 111) (conjugatingRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row21 :
    digitsEq 111 (rowProduct (yx2yRows 21) abRows 111) (conjugatingRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row22 :
    digitsEq 111 (rowProduct (yx2yRows 22) abRows 111) (conjugatingRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row23 :
    digitsEq 111 (rowProduct (yx2yRows 23) abRows 111) (conjugatingRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row24 :
    digitsEq 111 (rowProduct (yx2yRows 24) abRows 111) (conjugatingRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row25 :
    digitsEq 111 (rowProduct (yx2yRows 25) abRows 111) (conjugatingRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row26 :
    digitsEq 111 (rowProduct (yx2yRows 26) abRows 111) (conjugatingRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row27 :
    digitsEq 111 (rowProduct (yx2yRows 27) abRows 111) (conjugatingRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row28 :
    digitsEq 111 (rowProduct (yx2yRows 28) abRows 111) (conjugatingRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row29 :
    digitsEq 111 (rowProduct (yx2yRows 29) abRows 111) (conjugatingRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row30 :
    digitsEq 111 (rowProduct (yx2yRows 30) abRows 111) (conjugatingRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row31 :
    digitsEq 111 (rowProduct (yx2yRows 31) abRows 111) (conjugatingRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row32 :
    digitsEq 111 (rowProduct (yx2yRows 32) abRows 111) (conjugatingRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row33 :
    digitsEq 111 (rowProduct (yx2yRows 33) abRows 111) (conjugatingRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row34 :
    digitsEq 111 (rowProduct (yx2yRows 34) abRows 111) (conjugatingRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row35 :
    digitsEq 111 (rowProduct (yx2yRows 35) abRows 111) (conjugatingRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row36 :
    digitsEq 111 (rowProduct (yx2yRows 36) abRows 111) (conjugatingRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row37 :
    digitsEq 111 (rowProduct (yx2yRows 37) abRows 111) (conjugatingRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row38 :
    digitsEq 111 (rowProduct (yx2yRows 38) abRows 111) (conjugatingRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row39 :
    digitsEq 111 (rowProduct (yx2yRows 39) abRows 111) (conjugatingRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row40 :
    digitsEq 111 (rowProduct (yx2yRows 40) abRows 111) (conjugatingRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row41 :
    digitsEq 111 (rowProduct (yx2yRows 41) abRows 111) (conjugatingRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row42 :
    digitsEq 111 (rowProduct (yx2yRows 42) abRows 111) (conjugatingRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row43 :
    digitsEq 111 (rowProduct (yx2yRows 43) abRows 111) (conjugatingRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row44 :
    digitsEq 111 (rowProduct (yx2yRows 44) abRows 111) (conjugatingRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row45 :
    digitsEq 111 (rowProduct (yx2yRows 45) abRows 111) (conjugatingRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row46 :
    digitsEq 111 (rowProduct (yx2yRows 46) abRows 111) (conjugatingRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row47 :
    digitsEq 111 (rowProduct (yx2yRows 47) abRows 111) (conjugatingRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row48 :
    digitsEq 111 (rowProduct (yx2yRows 48) abRows 111) (conjugatingRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row49 :
    digitsEq 111 (rowProduct (yx2yRows 49) abRows 111) (conjugatingRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row50 :
    digitsEq 111 (rowProduct (yx2yRows 50) abRows 111) (conjugatingRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row51 :
    digitsEq 111 (rowProduct (yx2yRows 51) abRows 111) (conjugatingRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row52 :
    digitsEq 111 (rowProduct (yx2yRows 52) abRows 111) (conjugatingRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row53 :
    digitsEq 111 (rowProduct (yx2yRows 53) abRows 111) (conjugatingRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row54 :
    digitsEq 111 (rowProduct (yx2yRows 54) abRows 111) (conjugatingRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row55 :
    digitsEq 111 (rowProduct (yx2yRows 55) abRows 111) (conjugatingRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row56 :
    digitsEq 111 (rowProduct (yx2yRows 56) abRows 111) (conjugatingRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row57 :
    digitsEq 111 (rowProduct (yx2yRows 57) abRows 111) (conjugatingRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row58 :
    digitsEq 111 (rowProduct (yx2yRows 58) abRows 111) (conjugatingRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row59 :
    digitsEq 111 (rowProduct (yx2yRows 59) abRows 111) (conjugatingRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row60 :
    digitsEq 111 (rowProduct (yx2yRows 60) abRows 111) (conjugatingRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row61 :
    digitsEq 111 (rowProduct (yx2yRows 61) abRows 111) (conjugatingRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row62 :
    digitsEq 111 (rowProduct (yx2yRows 62) abRows 111) (conjugatingRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row63 :
    digitsEq 111 (rowProduct (yx2yRows 63) abRows 111) (conjugatingRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row64 :
    digitsEq 111 (rowProduct (yx2yRows 64) abRows 111) (conjugatingRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row65 :
    digitsEq 111 (rowProduct (yx2yRows 65) abRows 111) (conjugatingRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row66 :
    digitsEq 111 (rowProduct (yx2yRows 66) abRows 111) (conjugatingRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row67 :
    digitsEq 111 (rowProduct (yx2yRows 67) abRows 111) (conjugatingRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row68 :
    digitsEq 111 (rowProduct (yx2yRows 68) abRows 111) (conjugatingRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row69 :
    digitsEq 111 (rowProduct (yx2yRows 69) abRows 111) (conjugatingRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row70 :
    digitsEq 111 (rowProduct (yx2yRows 70) abRows 111) (conjugatingRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row71 :
    digitsEq 111 (rowProduct (yx2yRows 71) abRows 111) (conjugatingRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row72 :
    digitsEq 111 (rowProduct (yx2yRows 72) abRows 111) (conjugatingRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row73 :
    digitsEq 111 (rowProduct (yx2yRows 73) abRows 111) (conjugatingRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row74 :
    digitsEq 111 (rowProduct (yx2yRows 74) abRows 111) (conjugatingRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row75 :
    digitsEq 111 (rowProduct (yx2yRows 75) abRows 111) (conjugatingRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row76 :
    digitsEq 111 (rowProduct (yx2yRows 76) abRows 111) (conjugatingRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row77 :
    digitsEq 111 (rowProduct (yx2yRows 77) abRows 111) (conjugatingRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row78 :
    digitsEq 111 (rowProduct (yx2yRows 78) abRows 111) (conjugatingRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row79 :
    digitsEq 111 (rowProduct (yx2yRows 79) abRows 111) (conjugatingRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row80 :
    digitsEq 111 (rowProduct (yx2yRows 80) abRows 111) (conjugatingRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row81 :
    digitsEq 111 (rowProduct (yx2yRows 81) abRows 111) (conjugatingRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row82 :
    digitsEq 111 (rowProduct (yx2yRows 82) abRows 111) (conjugatingRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row83 :
    digitsEq 111 (rowProduct (yx2yRows 83) abRows 111) (conjugatingRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row84 :
    digitsEq 111 (rowProduct (yx2yRows 84) abRows 111) (conjugatingRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row85 :
    digitsEq 111 (rowProduct (yx2yRows 85) abRows 111) (conjugatingRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row86 :
    digitsEq 111 (rowProduct (yx2yRows 86) abRows 111) (conjugatingRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row87 :
    digitsEq 111 (rowProduct (yx2yRows 87) abRows 111) (conjugatingRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row88 :
    digitsEq 111 (rowProduct (yx2yRows 88) abRows 111) (conjugatingRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row89 :
    digitsEq 111 (rowProduct (yx2yRows 89) abRows 111) (conjugatingRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row90 :
    digitsEq 111 (rowProduct (yx2yRows 90) abRows 111) (conjugatingRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row91 :
    digitsEq 111 (rowProduct (yx2yRows 91) abRows 111) (conjugatingRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row92 :
    digitsEq 111 (rowProduct (yx2yRows 92) abRows 111) (conjugatingRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row93 :
    digitsEq 111 (rowProduct (yx2yRows 93) abRows 111) (conjugatingRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row94 :
    digitsEq 111 (rowProduct (yx2yRows 94) abRows 111) (conjugatingRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row95 :
    digitsEq 111 (rowProduct (yx2yRows 95) abRows 111) (conjugatingRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row96 :
    digitsEq 111 (rowProduct (yx2yRows 96) abRows 111) (conjugatingRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row97 :
    digitsEq 111 (rowProduct (yx2yRows 97) abRows 111) (conjugatingRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row98 :
    digitsEq 111 (rowProduct (yx2yRows 98) abRows 111) (conjugatingRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row99 :
    digitsEq 111 (rowProduct (yx2yRows 99) abRows 111) (conjugatingRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row100 :
    digitsEq 111 (rowProduct (yx2yRows 100) abRows 111) (conjugatingRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row101 :
    digitsEq 111 (rowProduct (yx2yRows 101) abRows 111) (conjugatingRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row102 :
    digitsEq 111 (rowProduct (yx2yRows 102) abRows 111) (conjugatingRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row103 :
    digitsEq 111 (rowProduct (yx2yRows 103) abRows 111) (conjugatingRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row104 :
    digitsEq 111 (rowProduct (yx2yRows 104) abRows 111) (conjugatingRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row105 :
    digitsEq 111 (rowProduct (yx2yRows 105) abRows 111) (conjugatingRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row106 :
    digitsEq 111 (rowProduct (yx2yRows 106) abRows 111) (conjugatingRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row107 :
    digitsEq 111 (rowProduct (yx2yRows 107) abRows 111) (conjugatingRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row108 :
    digitsEq 111 (rowProduct (yx2yRows 108) abRows 111) (conjugatingRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row109 :
    digitsEq 111 (rowProduct (yx2yRows 109) abRows 111) (conjugatingRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_row110 :
    digitsEq 111 (rowProduct (yx2yRows 110) abRows 111) (conjugatingRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugating_rows : ∀ i,
    digitsEq 111 (rowProduct (yx2yRows i) abRows 111) (conjugatingRows i) = true :=
  (Fin.cases conjugating_row0
    (Fin.cases conjugating_row1
    (Fin.cases conjugating_row2
    (Fin.cases conjugating_row3
    (Fin.cases conjugating_row4
    (Fin.cases conjugating_row5
    (Fin.cases conjugating_row6
    (Fin.cases conjugating_row7
    (Fin.cases conjugating_row8
    (Fin.cases conjugating_row9
    (Fin.cases conjugating_row10
    (Fin.cases conjugating_row11
    (Fin.cases conjugating_row12
    (Fin.cases conjugating_row13
    (Fin.cases conjugating_row14
    (Fin.cases conjugating_row15
    (Fin.cases conjugating_row16
    (Fin.cases conjugating_row17
    (Fin.cases conjugating_row18
    (Fin.cases conjugating_row19
    (Fin.cases conjugating_row20
    (Fin.cases conjugating_row21
    (Fin.cases conjugating_row22
    (Fin.cases conjugating_row23
    (Fin.cases conjugating_row24
    (Fin.cases conjugating_row25
    (Fin.cases conjugating_row26
    (Fin.cases conjugating_row27
    (Fin.cases conjugating_row28
    (Fin.cases conjugating_row29
    (Fin.cases conjugating_row30
    (Fin.cases conjugating_row31
    (Fin.cases conjugating_row32
    (Fin.cases conjugating_row33
    (Fin.cases conjugating_row34
    (Fin.cases conjugating_row35
    (Fin.cases conjugating_row36
    (Fin.cases conjugating_row37
    (Fin.cases conjugating_row38
    (Fin.cases conjugating_row39
    (Fin.cases conjugating_row40
    (Fin.cases conjugating_row41
    (Fin.cases conjugating_row42
    (Fin.cases conjugating_row43
    (Fin.cases conjugating_row44
    (Fin.cases conjugating_row45
    (Fin.cases conjugating_row46
    (Fin.cases conjugating_row47
    (Fin.cases conjugating_row48
    (Fin.cases conjugating_row49
    (Fin.cases conjugating_row50
    (Fin.cases conjugating_row51
    (Fin.cases conjugating_row52
    (Fin.cases conjugating_row53
    (Fin.cases conjugating_row54
    (Fin.cases conjugating_row55
    (Fin.cases conjugating_row56
    (Fin.cases conjugating_row57
    (Fin.cases conjugating_row58
    (Fin.cases conjugating_row59
    (Fin.cases conjugating_row60
    (Fin.cases conjugating_row61
    (Fin.cases conjugating_row62
    (Fin.cases conjugating_row63
    (Fin.cases conjugating_row64
    (Fin.cases conjugating_row65
    (Fin.cases conjugating_row66
    (Fin.cases conjugating_row67
    (Fin.cases conjugating_row68
    (Fin.cases conjugating_row69
    (Fin.cases conjugating_row70
    (Fin.cases conjugating_row71
    (Fin.cases conjugating_row72
    (Fin.cases conjugating_row73
    (Fin.cases conjugating_row74
    (Fin.cases conjugating_row75
    (Fin.cases conjugating_row76
    (Fin.cases conjugating_row77
    (Fin.cases conjugating_row78
    (Fin.cases conjugating_row79
    (Fin.cases conjugating_row80
    (Fin.cases conjugating_row81
    (Fin.cases conjugating_row82
    (Fin.cases conjugating_row83
    (Fin.cases conjugating_row84
    (Fin.cases conjugating_row85
    (Fin.cases conjugating_row86
    (Fin.cases conjugating_row87
    (Fin.cases conjugating_row88
    (Fin.cases conjugating_row89
    (Fin.cases conjugating_row90
    (Fin.cases conjugating_row91
    (Fin.cases conjugating_row92
    (Fin.cases conjugating_row93
    (Fin.cases conjugating_row94
    (Fin.cases conjugating_row95
    (Fin.cases conjugating_row96
    (Fin.cases conjugating_row97
    (Fin.cases conjugating_row98
    (Fin.cases conjugating_row99
    (Fin.cases conjugating_row100
    (Fin.cases conjugating_row101
    (Fin.cases conjugating_row102
    (Fin.cases conjugating_row103
    (Fin.cases conjugating_row104
    (Fin.cases conjugating_row105
    (Fin.cases conjugating_row106
    (Fin.cases conjugating_row107
    (Fin.cases conjugating_row108
    (Fin.cases conjugating_row109
    (Fin.cases conjugating_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_conjugating : yx2yMatrix * abMatrix = conjugatingMatrix :=
  decode_mul _ _ _ yx2y_small ab_small conjugating_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
