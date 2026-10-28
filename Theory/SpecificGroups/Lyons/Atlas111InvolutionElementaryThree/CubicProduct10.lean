module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: cubic times localB

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
private theorem cy_row0 :
    digitsEq 111 (rowProduct (cubicRows 0) localBRows 111) (cyRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row1 :
    digitsEq 111 (rowProduct (cubicRows 1) localBRows 111) (cyRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row2 :
    digitsEq 111 (rowProduct (cubicRows 2) localBRows 111) (cyRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row3 :
    digitsEq 111 (rowProduct (cubicRows 3) localBRows 111) (cyRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row4 :
    digitsEq 111 (rowProduct (cubicRows 4) localBRows 111) (cyRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row5 :
    digitsEq 111 (rowProduct (cubicRows 5) localBRows 111) (cyRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row6 :
    digitsEq 111 (rowProduct (cubicRows 6) localBRows 111) (cyRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row7 :
    digitsEq 111 (rowProduct (cubicRows 7) localBRows 111) (cyRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row8 :
    digitsEq 111 (rowProduct (cubicRows 8) localBRows 111) (cyRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row9 :
    digitsEq 111 (rowProduct (cubicRows 9) localBRows 111) (cyRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row10 :
    digitsEq 111 (rowProduct (cubicRows 10) localBRows 111) (cyRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row11 :
    digitsEq 111 (rowProduct (cubicRows 11) localBRows 111) (cyRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row12 :
    digitsEq 111 (rowProduct (cubicRows 12) localBRows 111) (cyRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row13 :
    digitsEq 111 (rowProduct (cubicRows 13) localBRows 111) (cyRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row14 :
    digitsEq 111 (rowProduct (cubicRows 14) localBRows 111) (cyRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row15 :
    digitsEq 111 (rowProduct (cubicRows 15) localBRows 111) (cyRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row16 :
    digitsEq 111 (rowProduct (cubicRows 16) localBRows 111) (cyRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row17 :
    digitsEq 111 (rowProduct (cubicRows 17) localBRows 111) (cyRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row18 :
    digitsEq 111 (rowProduct (cubicRows 18) localBRows 111) (cyRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row19 :
    digitsEq 111 (rowProduct (cubicRows 19) localBRows 111) (cyRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row20 :
    digitsEq 111 (rowProduct (cubicRows 20) localBRows 111) (cyRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row21 :
    digitsEq 111 (rowProduct (cubicRows 21) localBRows 111) (cyRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row22 :
    digitsEq 111 (rowProduct (cubicRows 22) localBRows 111) (cyRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row23 :
    digitsEq 111 (rowProduct (cubicRows 23) localBRows 111) (cyRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row24 :
    digitsEq 111 (rowProduct (cubicRows 24) localBRows 111) (cyRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row25 :
    digitsEq 111 (rowProduct (cubicRows 25) localBRows 111) (cyRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row26 :
    digitsEq 111 (rowProduct (cubicRows 26) localBRows 111) (cyRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row27 :
    digitsEq 111 (rowProduct (cubicRows 27) localBRows 111) (cyRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row28 :
    digitsEq 111 (rowProduct (cubicRows 28) localBRows 111) (cyRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row29 :
    digitsEq 111 (rowProduct (cubicRows 29) localBRows 111) (cyRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row30 :
    digitsEq 111 (rowProduct (cubicRows 30) localBRows 111) (cyRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row31 :
    digitsEq 111 (rowProduct (cubicRows 31) localBRows 111) (cyRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row32 :
    digitsEq 111 (rowProduct (cubicRows 32) localBRows 111) (cyRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row33 :
    digitsEq 111 (rowProduct (cubicRows 33) localBRows 111) (cyRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row34 :
    digitsEq 111 (rowProduct (cubicRows 34) localBRows 111) (cyRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row35 :
    digitsEq 111 (rowProduct (cubicRows 35) localBRows 111) (cyRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row36 :
    digitsEq 111 (rowProduct (cubicRows 36) localBRows 111) (cyRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row37 :
    digitsEq 111 (rowProduct (cubicRows 37) localBRows 111) (cyRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row38 :
    digitsEq 111 (rowProduct (cubicRows 38) localBRows 111) (cyRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row39 :
    digitsEq 111 (rowProduct (cubicRows 39) localBRows 111) (cyRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row40 :
    digitsEq 111 (rowProduct (cubicRows 40) localBRows 111) (cyRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row41 :
    digitsEq 111 (rowProduct (cubicRows 41) localBRows 111) (cyRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row42 :
    digitsEq 111 (rowProduct (cubicRows 42) localBRows 111) (cyRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row43 :
    digitsEq 111 (rowProduct (cubicRows 43) localBRows 111) (cyRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row44 :
    digitsEq 111 (rowProduct (cubicRows 44) localBRows 111) (cyRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row45 :
    digitsEq 111 (rowProduct (cubicRows 45) localBRows 111) (cyRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row46 :
    digitsEq 111 (rowProduct (cubicRows 46) localBRows 111) (cyRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row47 :
    digitsEq 111 (rowProduct (cubicRows 47) localBRows 111) (cyRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row48 :
    digitsEq 111 (rowProduct (cubicRows 48) localBRows 111) (cyRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row49 :
    digitsEq 111 (rowProduct (cubicRows 49) localBRows 111) (cyRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row50 :
    digitsEq 111 (rowProduct (cubicRows 50) localBRows 111) (cyRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row51 :
    digitsEq 111 (rowProduct (cubicRows 51) localBRows 111) (cyRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row52 :
    digitsEq 111 (rowProduct (cubicRows 52) localBRows 111) (cyRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row53 :
    digitsEq 111 (rowProduct (cubicRows 53) localBRows 111) (cyRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row54 :
    digitsEq 111 (rowProduct (cubicRows 54) localBRows 111) (cyRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row55 :
    digitsEq 111 (rowProduct (cubicRows 55) localBRows 111) (cyRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row56 :
    digitsEq 111 (rowProduct (cubicRows 56) localBRows 111) (cyRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row57 :
    digitsEq 111 (rowProduct (cubicRows 57) localBRows 111) (cyRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row58 :
    digitsEq 111 (rowProduct (cubicRows 58) localBRows 111) (cyRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row59 :
    digitsEq 111 (rowProduct (cubicRows 59) localBRows 111) (cyRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row60 :
    digitsEq 111 (rowProduct (cubicRows 60) localBRows 111) (cyRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row61 :
    digitsEq 111 (rowProduct (cubicRows 61) localBRows 111) (cyRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row62 :
    digitsEq 111 (rowProduct (cubicRows 62) localBRows 111) (cyRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row63 :
    digitsEq 111 (rowProduct (cubicRows 63) localBRows 111) (cyRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row64 :
    digitsEq 111 (rowProduct (cubicRows 64) localBRows 111) (cyRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row65 :
    digitsEq 111 (rowProduct (cubicRows 65) localBRows 111) (cyRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row66 :
    digitsEq 111 (rowProduct (cubicRows 66) localBRows 111) (cyRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row67 :
    digitsEq 111 (rowProduct (cubicRows 67) localBRows 111) (cyRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row68 :
    digitsEq 111 (rowProduct (cubicRows 68) localBRows 111) (cyRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row69 :
    digitsEq 111 (rowProduct (cubicRows 69) localBRows 111) (cyRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row70 :
    digitsEq 111 (rowProduct (cubicRows 70) localBRows 111) (cyRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row71 :
    digitsEq 111 (rowProduct (cubicRows 71) localBRows 111) (cyRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row72 :
    digitsEq 111 (rowProduct (cubicRows 72) localBRows 111) (cyRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row73 :
    digitsEq 111 (rowProduct (cubicRows 73) localBRows 111) (cyRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row74 :
    digitsEq 111 (rowProduct (cubicRows 74) localBRows 111) (cyRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row75 :
    digitsEq 111 (rowProduct (cubicRows 75) localBRows 111) (cyRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row76 :
    digitsEq 111 (rowProduct (cubicRows 76) localBRows 111) (cyRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row77 :
    digitsEq 111 (rowProduct (cubicRows 77) localBRows 111) (cyRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row78 :
    digitsEq 111 (rowProduct (cubicRows 78) localBRows 111) (cyRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row79 :
    digitsEq 111 (rowProduct (cubicRows 79) localBRows 111) (cyRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row80 :
    digitsEq 111 (rowProduct (cubicRows 80) localBRows 111) (cyRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row81 :
    digitsEq 111 (rowProduct (cubicRows 81) localBRows 111) (cyRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row82 :
    digitsEq 111 (rowProduct (cubicRows 82) localBRows 111) (cyRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row83 :
    digitsEq 111 (rowProduct (cubicRows 83) localBRows 111) (cyRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row84 :
    digitsEq 111 (rowProduct (cubicRows 84) localBRows 111) (cyRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row85 :
    digitsEq 111 (rowProduct (cubicRows 85) localBRows 111) (cyRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row86 :
    digitsEq 111 (rowProduct (cubicRows 86) localBRows 111) (cyRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row87 :
    digitsEq 111 (rowProduct (cubicRows 87) localBRows 111) (cyRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row88 :
    digitsEq 111 (rowProduct (cubicRows 88) localBRows 111) (cyRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row89 :
    digitsEq 111 (rowProduct (cubicRows 89) localBRows 111) (cyRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row90 :
    digitsEq 111 (rowProduct (cubicRows 90) localBRows 111) (cyRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row91 :
    digitsEq 111 (rowProduct (cubicRows 91) localBRows 111) (cyRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row92 :
    digitsEq 111 (rowProduct (cubicRows 92) localBRows 111) (cyRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row93 :
    digitsEq 111 (rowProduct (cubicRows 93) localBRows 111) (cyRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row94 :
    digitsEq 111 (rowProduct (cubicRows 94) localBRows 111) (cyRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row95 :
    digitsEq 111 (rowProduct (cubicRows 95) localBRows 111) (cyRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row96 :
    digitsEq 111 (rowProduct (cubicRows 96) localBRows 111) (cyRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row97 :
    digitsEq 111 (rowProduct (cubicRows 97) localBRows 111) (cyRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row98 :
    digitsEq 111 (rowProduct (cubicRows 98) localBRows 111) (cyRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row99 :
    digitsEq 111 (rowProduct (cubicRows 99) localBRows 111) (cyRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row100 :
    digitsEq 111 (rowProduct (cubicRows 100) localBRows 111) (cyRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row101 :
    digitsEq 111 (rowProduct (cubicRows 101) localBRows 111) (cyRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row102 :
    digitsEq 111 (rowProduct (cubicRows 102) localBRows 111) (cyRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row103 :
    digitsEq 111 (rowProduct (cubicRows 103) localBRows 111) (cyRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row104 :
    digitsEq 111 (rowProduct (cubicRows 104) localBRows 111) (cyRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row105 :
    digitsEq 111 (rowProduct (cubicRows 105) localBRows 111) (cyRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row106 :
    digitsEq 111 (rowProduct (cubicRows 106) localBRows 111) (cyRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row107 :
    digitsEq 111 (rowProduct (cubicRows 107) localBRows 111) (cyRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row108 :
    digitsEq 111 (rowProduct (cubicRows 108) localBRows 111) (cyRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row109 :
    digitsEq 111 (rowProduct (cubicRows 109) localBRows 111) (cyRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_row110 :
    digitsEq 111 (rowProduct (cubicRows 110) localBRows 111) (cyRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem cy_rows : ∀ i,
    digitsEq 111 (rowProduct (cubicRows i) localBRows 111) (cyRows i) = true :=
  (Fin.cases cy_row0
    (Fin.cases cy_row1
    (Fin.cases cy_row2
    (Fin.cases cy_row3
    (Fin.cases cy_row4
    (Fin.cases cy_row5
    (Fin.cases cy_row6
    (Fin.cases cy_row7
    (Fin.cases cy_row8
    (Fin.cases cy_row9
    (Fin.cases cy_row10
    (Fin.cases cy_row11
    (Fin.cases cy_row12
    (Fin.cases cy_row13
    (Fin.cases cy_row14
    (Fin.cases cy_row15
    (Fin.cases cy_row16
    (Fin.cases cy_row17
    (Fin.cases cy_row18
    (Fin.cases cy_row19
    (Fin.cases cy_row20
    (Fin.cases cy_row21
    (Fin.cases cy_row22
    (Fin.cases cy_row23
    (Fin.cases cy_row24
    (Fin.cases cy_row25
    (Fin.cases cy_row26
    (Fin.cases cy_row27
    (Fin.cases cy_row28
    (Fin.cases cy_row29
    (Fin.cases cy_row30
    (Fin.cases cy_row31
    (Fin.cases cy_row32
    (Fin.cases cy_row33
    (Fin.cases cy_row34
    (Fin.cases cy_row35
    (Fin.cases cy_row36
    (Fin.cases cy_row37
    (Fin.cases cy_row38
    (Fin.cases cy_row39
    (Fin.cases cy_row40
    (Fin.cases cy_row41
    (Fin.cases cy_row42
    (Fin.cases cy_row43
    (Fin.cases cy_row44
    (Fin.cases cy_row45
    (Fin.cases cy_row46
    (Fin.cases cy_row47
    (Fin.cases cy_row48
    (Fin.cases cy_row49
    (Fin.cases cy_row50
    (Fin.cases cy_row51
    (Fin.cases cy_row52
    (Fin.cases cy_row53
    (Fin.cases cy_row54
    (Fin.cases cy_row55
    (Fin.cases cy_row56
    (Fin.cases cy_row57
    (Fin.cases cy_row58
    (Fin.cases cy_row59
    (Fin.cases cy_row60
    (Fin.cases cy_row61
    (Fin.cases cy_row62
    (Fin.cases cy_row63
    (Fin.cases cy_row64
    (Fin.cases cy_row65
    (Fin.cases cy_row66
    (Fin.cases cy_row67
    (Fin.cases cy_row68
    (Fin.cases cy_row69
    (Fin.cases cy_row70
    (Fin.cases cy_row71
    (Fin.cases cy_row72
    (Fin.cases cy_row73
    (Fin.cases cy_row74
    (Fin.cases cy_row75
    (Fin.cases cy_row76
    (Fin.cases cy_row77
    (Fin.cases cy_row78
    (Fin.cases cy_row79
    (Fin.cases cy_row80
    (Fin.cases cy_row81
    (Fin.cases cy_row82
    (Fin.cases cy_row83
    (Fin.cases cy_row84
    (Fin.cases cy_row85
    (Fin.cases cy_row86
    (Fin.cases cy_row87
    (Fin.cases cy_row88
    (Fin.cases cy_row89
    (Fin.cases cy_row90
    (Fin.cases cy_row91
    (Fin.cases cy_row92
    (Fin.cases cy_row93
    (Fin.cases cy_row94
    (Fin.cases cy_row95
    (Fin.cases cy_row96
    (Fin.cases cy_row97
    (Fin.cases cy_row98
    (Fin.cases cy_row99
    (Fin.cases cy_row100
    (Fin.cases cy_row101
    (Fin.cases cy_row102
    (Fin.cases cy_row103
    (Fin.cases cy_row104
    (Fin.cases cy_row105
    (Fin.cases cy_row106
    (Fin.cases cy_row107
    (Fin.cases cy_row108
    (Fin.cases cy_row109
    (Fin.cases cy_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_cy : cubicMatrix * localBMatrix = cyMatrix :=
  decode_mul _ _ _ cubic_small localB_small cy_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
