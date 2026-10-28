module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: cubic times conjugating

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
private theorem cw_row0 :
    digitsEq 111 (rowProduct (cubicRows 0) conjugatingRows 111) (cwRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row1 :
    digitsEq 111 (rowProduct (cubicRows 1) conjugatingRows 111) (cwRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row2 :
    digitsEq 111 (rowProduct (cubicRows 2) conjugatingRows 111) (cwRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row3 :
    digitsEq 111 (rowProduct (cubicRows 3) conjugatingRows 111) (cwRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row4 :
    digitsEq 111 (rowProduct (cubicRows 4) conjugatingRows 111) (cwRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row5 :
    digitsEq 111 (rowProduct (cubicRows 5) conjugatingRows 111) (cwRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row6 :
    digitsEq 111 (rowProduct (cubicRows 6) conjugatingRows 111) (cwRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row7 :
    digitsEq 111 (rowProduct (cubicRows 7) conjugatingRows 111) (cwRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row8 :
    digitsEq 111 (rowProduct (cubicRows 8) conjugatingRows 111) (cwRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row9 :
    digitsEq 111 (rowProduct (cubicRows 9) conjugatingRows 111) (cwRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row10 :
    digitsEq 111 (rowProduct (cubicRows 10) conjugatingRows 111) (cwRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row11 :
    digitsEq 111 (rowProduct (cubicRows 11) conjugatingRows 111) (cwRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row12 :
    digitsEq 111 (rowProduct (cubicRows 12) conjugatingRows 111) (cwRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row13 :
    digitsEq 111 (rowProduct (cubicRows 13) conjugatingRows 111) (cwRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row14 :
    digitsEq 111 (rowProduct (cubicRows 14) conjugatingRows 111) (cwRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row15 :
    digitsEq 111 (rowProduct (cubicRows 15) conjugatingRows 111) (cwRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row16 :
    digitsEq 111 (rowProduct (cubicRows 16) conjugatingRows 111) (cwRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row17 :
    digitsEq 111 (rowProduct (cubicRows 17) conjugatingRows 111) (cwRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row18 :
    digitsEq 111 (rowProduct (cubicRows 18) conjugatingRows 111) (cwRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row19 :
    digitsEq 111 (rowProduct (cubicRows 19) conjugatingRows 111) (cwRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row20 :
    digitsEq 111 (rowProduct (cubicRows 20) conjugatingRows 111) (cwRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row21 :
    digitsEq 111 (rowProduct (cubicRows 21) conjugatingRows 111) (cwRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row22 :
    digitsEq 111 (rowProduct (cubicRows 22) conjugatingRows 111) (cwRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row23 :
    digitsEq 111 (rowProduct (cubicRows 23) conjugatingRows 111) (cwRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row24 :
    digitsEq 111 (rowProduct (cubicRows 24) conjugatingRows 111) (cwRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row25 :
    digitsEq 111 (rowProduct (cubicRows 25) conjugatingRows 111) (cwRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row26 :
    digitsEq 111 (rowProduct (cubicRows 26) conjugatingRows 111) (cwRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row27 :
    digitsEq 111 (rowProduct (cubicRows 27) conjugatingRows 111) (cwRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row28 :
    digitsEq 111 (rowProduct (cubicRows 28) conjugatingRows 111) (cwRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row29 :
    digitsEq 111 (rowProduct (cubicRows 29) conjugatingRows 111) (cwRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row30 :
    digitsEq 111 (rowProduct (cubicRows 30) conjugatingRows 111) (cwRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row31 :
    digitsEq 111 (rowProduct (cubicRows 31) conjugatingRows 111) (cwRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row32 :
    digitsEq 111 (rowProduct (cubicRows 32) conjugatingRows 111) (cwRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row33 :
    digitsEq 111 (rowProduct (cubicRows 33) conjugatingRows 111) (cwRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row34 :
    digitsEq 111 (rowProduct (cubicRows 34) conjugatingRows 111) (cwRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row35 :
    digitsEq 111 (rowProduct (cubicRows 35) conjugatingRows 111) (cwRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row36 :
    digitsEq 111 (rowProduct (cubicRows 36) conjugatingRows 111) (cwRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row37 :
    digitsEq 111 (rowProduct (cubicRows 37) conjugatingRows 111) (cwRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row38 :
    digitsEq 111 (rowProduct (cubicRows 38) conjugatingRows 111) (cwRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row39 :
    digitsEq 111 (rowProduct (cubicRows 39) conjugatingRows 111) (cwRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row40 :
    digitsEq 111 (rowProduct (cubicRows 40) conjugatingRows 111) (cwRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row41 :
    digitsEq 111 (rowProduct (cubicRows 41) conjugatingRows 111) (cwRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row42 :
    digitsEq 111 (rowProduct (cubicRows 42) conjugatingRows 111) (cwRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row43 :
    digitsEq 111 (rowProduct (cubicRows 43) conjugatingRows 111) (cwRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row44 :
    digitsEq 111 (rowProduct (cubicRows 44) conjugatingRows 111) (cwRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row45 :
    digitsEq 111 (rowProduct (cubicRows 45) conjugatingRows 111) (cwRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row46 :
    digitsEq 111 (rowProduct (cubicRows 46) conjugatingRows 111) (cwRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row47 :
    digitsEq 111 (rowProduct (cubicRows 47) conjugatingRows 111) (cwRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row48 :
    digitsEq 111 (rowProduct (cubicRows 48) conjugatingRows 111) (cwRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row49 :
    digitsEq 111 (rowProduct (cubicRows 49) conjugatingRows 111) (cwRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row50 :
    digitsEq 111 (rowProduct (cubicRows 50) conjugatingRows 111) (cwRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row51 :
    digitsEq 111 (rowProduct (cubicRows 51) conjugatingRows 111) (cwRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row52 :
    digitsEq 111 (rowProduct (cubicRows 52) conjugatingRows 111) (cwRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row53 :
    digitsEq 111 (rowProduct (cubicRows 53) conjugatingRows 111) (cwRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row54 :
    digitsEq 111 (rowProduct (cubicRows 54) conjugatingRows 111) (cwRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row55 :
    digitsEq 111 (rowProduct (cubicRows 55) conjugatingRows 111) (cwRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row56 :
    digitsEq 111 (rowProduct (cubicRows 56) conjugatingRows 111) (cwRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row57 :
    digitsEq 111 (rowProduct (cubicRows 57) conjugatingRows 111) (cwRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row58 :
    digitsEq 111 (rowProduct (cubicRows 58) conjugatingRows 111) (cwRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row59 :
    digitsEq 111 (rowProduct (cubicRows 59) conjugatingRows 111) (cwRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row60 :
    digitsEq 111 (rowProduct (cubicRows 60) conjugatingRows 111) (cwRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row61 :
    digitsEq 111 (rowProduct (cubicRows 61) conjugatingRows 111) (cwRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row62 :
    digitsEq 111 (rowProduct (cubicRows 62) conjugatingRows 111) (cwRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row63 :
    digitsEq 111 (rowProduct (cubicRows 63) conjugatingRows 111) (cwRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row64 :
    digitsEq 111 (rowProduct (cubicRows 64) conjugatingRows 111) (cwRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row65 :
    digitsEq 111 (rowProduct (cubicRows 65) conjugatingRows 111) (cwRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row66 :
    digitsEq 111 (rowProduct (cubicRows 66) conjugatingRows 111) (cwRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row67 :
    digitsEq 111 (rowProduct (cubicRows 67) conjugatingRows 111) (cwRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row68 :
    digitsEq 111 (rowProduct (cubicRows 68) conjugatingRows 111) (cwRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row69 :
    digitsEq 111 (rowProduct (cubicRows 69) conjugatingRows 111) (cwRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row70 :
    digitsEq 111 (rowProduct (cubicRows 70) conjugatingRows 111) (cwRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row71 :
    digitsEq 111 (rowProduct (cubicRows 71) conjugatingRows 111) (cwRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row72 :
    digitsEq 111 (rowProduct (cubicRows 72) conjugatingRows 111) (cwRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row73 :
    digitsEq 111 (rowProduct (cubicRows 73) conjugatingRows 111) (cwRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row74 :
    digitsEq 111 (rowProduct (cubicRows 74) conjugatingRows 111) (cwRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row75 :
    digitsEq 111 (rowProduct (cubicRows 75) conjugatingRows 111) (cwRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row76 :
    digitsEq 111 (rowProduct (cubicRows 76) conjugatingRows 111) (cwRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row77 :
    digitsEq 111 (rowProduct (cubicRows 77) conjugatingRows 111) (cwRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row78 :
    digitsEq 111 (rowProduct (cubicRows 78) conjugatingRows 111) (cwRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row79 :
    digitsEq 111 (rowProduct (cubicRows 79) conjugatingRows 111) (cwRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row80 :
    digitsEq 111 (rowProduct (cubicRows 80) conjugatingRows 111) (cwRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row81 :
    digitsEq 111 (rowProduct (cubicRows 81) conjugatingRows 111) (cwRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row82 :
    digitsEq 111 (rowProduct (cubicRows 82) conjugatingRows 111) (cwRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row83 :
    digitsEq 111 (rowProduct (cubicRows 83) conjugatingRows 111) (cwRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row84 :
    digitsEq 111 (rowProduct (cubicRows 84) conjugatingRows 111) (cwRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row85 :
    digitsEq 111 (rowProduct (cubicRows 85) conjugatingRows 111) (cwRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row86 :
    digitsEq 111 (rowProduct (cubicRows 86) conjugatingRows 111) (cwRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row87 :
    digitsEq 111 (rowProduct (cubicRows 87) conjugatingRows 111) (cwRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row88 :
    digitsEq 111 (rowProduct (cubicRows 88) conjugatingRows 111) (cwRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row89 :
    digitsEq 111 (rowProduct (cubicRows 89) conjugatingRows 111) (cwRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row90 :
    digitsEq 111 (rowProduct (cubicRows 90) conjugatingRows 111) (cwRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row91 :
    digitsEq 111 (rowProduct (cubicRows 91) conjugatingRows 111) (cwRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row92 :
    digitsEq 111 (rowProduct (cubicRows 92) conjugatingRows 111) (cwRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row93 :
    digitsEq 111 (rowProduct (cubicRows 93) conjugatingRows 111) (cwRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row94 :
    digitsEq 111 (rowProduct (cubicRows 94) conjugatingRows 111) (cwRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row95 :
    digitsEq 111 (rowProduct (cubicRows 95) conjugatingRows 111) (cwRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row96 :
    digitsEq 111 (rowProduct (cubicRows 96) conjugatingRows 111) (cwRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row97 :
    digitsEq 111 (rowProduct (cubicRows 97) conjugatingRows 111) (cwRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row98 :
    digitsEq 111 (rowProduct (cubicRows 98) conjugatingRows 111) (cwRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row99 :
    digitsEq 111 (rowProduct (cubicRows 99) conjugatingRows 111) (cwRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row100 :
    digitsEq 111 (rowProduct (cubicRows 100) conjugatingRows 111) (cwRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row101 :
    digitsEq 111 (rowProduct (cubicRows 101) conjugatingRows 111) (cwRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row102 :
    digitsEq 111 (rowProduct (cubicRows 102) conjugatingRows 111) (cwRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row103 :
    digitsEq 111 (rowProduct (cubicRows 103) conjugatingRows 111) (cwRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row104 :
    digitsEq 111 (rowProduct (cubicRows 104) conjugatingRows 111) (cwRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row105 :
    digitsEq 111 (rowProduct (cubicRows 105) conjugatingRows 111) (cwRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row106 :
    digitsEq 111 (rowProduct (cubicRows 106) conjugatingRows 111) (cwRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row107 :
    digitsEq 111 (rowProduct (cubicRows 107) conjugatingRows 111) (cwRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row108 :
    digitsEq 111 (rowProduct (cubicRows 108) conjugatingRows 111) (cwRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row109 :
    digitsEq 111 (rowProduct (cubicRows 109) conjugatingRows 111) (cwRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_row110 :
    digitsEq 111 (rowProduct (cubicRows 110) conjugatingRows 111) (cwRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cw_rows : ∀ i,
    digitsEq 111 (rowProduct (cubicRows i) conjugatingRows 111) (cwRows i) = true :=
  (Fin.cases cw_row0
    (Fin.cases cw_row1
    (Fin.cases cw_row2
    (Fin.cases cw_row3
    (Fin.cases cw_row4
    (Fin.cases cw_row5
    (Fin.cases cw_row6
    (Fin.cases cw_row7
    (Fin.cases cw_row8
    (Fin.cases cw_row9
    (Fin.cases cw_row10
    (Fin.cases cw_row11
    (Fin.cases cw_row12
    (Fin.cases cw_row13
    (Fin.cases cw_row14
    (Fin.cases cw_row15
    (Fin.cases cw_row16
    (Fin.cases cw_row17
    (Fin.cases cw_row18
    (Fin.cases cw_row19
    (Fin.cases cw_row20
    (Fin.cases cw_row21
    (Fin.cases cw_row22
    (Fin.cases cw_row23
    (Fin.cases cw_row24
    (Fin.cases cw_row25
    (Fin.cases cw_row26
    (Fin.cases cw_row27
    (Fin.cases cw_row28
    (Fin.cases cw_row29
    (Fin.cases cw_row30
    (Fin.cases cw_row31
    (Fin.cases cw_row32
    (Fin.cases cw_row33
    (Fin.cases cw_row34
    (Fin.cases cw_row35
    (Fin.cases cw_row36
    (Fin.cases cw_row37
    (Fin.cases cw_row38
    (Fin.cases cw_row39
    (Fin.cases cw_row40
    (Fin.cases cw_row41
    (Fin.cases cw_row42
    (Fin.cases cw_row43
    (Fin.cases cw_row44
    (Fin.cases cw_row45
    (Fin.cases cw_row46
    (Fin.cases cw_row47
    (Fin.cases cw_row48
    (Fin.cases cw_row49
    (Fin.cases cw_row50
    (Fin.cases cw_row51
    (Fin.cases cw_row52
    (Fin.cases cw_row53
    (Fin.cases cw_row54
    (Fin.cases cw_row55
    (Fin.cases cw_row56
    (Fin.cases cw_row57
    (Fin.cases cw_row58
    (Fin.cases cw_row59
    (Fin.cases cw_row60
    (Fin.cases cw_row61
    (Fin.cases cw_row62
    (Fin.cases cw_row63
    (Fin.cases cw_row64
    (Fin.cases cw_row65
    (Fin.cases cw_row66
    (Fin.cases cw_row67
    (Fin.cases cw_row68
    (Fin.cases cw_row69
    (Fin.cases cw_row70
    (Fin.cases cw_row71
    (Fin.cases cw_row72
    (Fin.cases cw_row73
    (Fin.cases cw_row74
    (Fin.cases cw_row75
    (Fin.cases cw_row76
    (Fin.cases cw_row77
    (Fin.cases cw_row78
    (Fin.cases cw_row79
    (Fin.cases cw_row80
    (Fin.cases cw_row81
    (Fin.cases cw_row82
    (Fin.cases cw_row83
    (Fin.cases cw_row84
    (Fin.cases cw_row85
    (Fin.cases cw_row86
    (Fin.cases cw_row87
    (Fin.cases cw_row88
    (Fin.cases cw_row89
    (Fin.cases cw_row90
    (Fin.cases cw_row91
    (Fin.cases cw_row92
    (Fin.cases cw_row93
    (Fin.cases cw_row94
    (Fin.cases cw_row95
    (Fin.cases cw_row96
    (Fin.cases cw_row97
    (Fin.cases cw_row98
    (Fin.cases cw_row99
    (Fin.cases cw_row100
    (Fin.cases cw_row101
    (Fin.cases cw_row102
    (Fin.cases cw_row103
    (Fin.cases cw_row104
    (Fin.cases cw_row105
    (Fin.cases cw_row106
    (Fin.cases cw_row107
    (Fin.cases cw_row108
    (Fin.cases cw_row109
    (Fin.cases cw_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_cw : cubicMatrix * conjugatingMatrix = cwMatrix :=
  decode_mul _ _ _ cubic_small conjugating_small cw_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
