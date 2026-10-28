module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: ab times localB

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
private theorem xy_row0 :
    digitsEq 111 (rowProduct (abRows 0) localBRows 111) (xyRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row1 :
    digitsEq 111 (rowProduct (abRows 1) localBRows 111) (xyRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row2 :
    digitsEq 111 (rowProduct (abRows 2) localBRows 111) (xyRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row3 :
    digitsEq 111 (rowProduct (abRows 3) localBRows 111) (xyRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row4 :
    digitsEq 111 (rowProduct (abRows 4) localBRows 111) (xyRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row5 :
    digitsEq 111 (rowProduct (abRows 5) localBRows 111) (xyRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row6 :
    digitsEq 111 (rowProduct (abRows 6) localBRows 111) (xyRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row7 :
    digitsEq 111 (rowProduct (abRows 7) localBRows 111) (xyRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row8 :
    digitsEq 111 (rowProduct (abRows 8) localBRows 111) (xyRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row9 :
    digitsEq 111 (rowProduct (abRows 9) localBRows 111) (xyRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row10 :
    digitsEq 111 (rowProduct (abRows 10) localBRows 111) (xyRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row11 :
    digitsEq 111 (rowProduct (abRows 11) localBRows 111) (xyRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row12 :
    digitsEq 111 (rowProduct (abRows 12) localBRows 111) (xyRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row13 :
    digitsEq 111 (rowProduct (abRows 13) localBRows 111) (xyRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row14 :
    digitsEq 111 (rowProduct (abRows 14) localBRows 111) (xyRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row15 :
    digitsEq 111 (rowProduct (abRows 15) localBRows 111) (xyRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row16 :
    digitsEq 111 (rowProduct (abRows 16) localBRows 111) (xyRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row17 :
    digitsEq 111 (rowProduct (abRows 17) localBRows 111) (xyRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row18 :
    digitsEq 111 (rowProduct (abRows 18) localBRows 111) (xyRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row19 :
    digitsEq 111 (rowProduct (abRows 19) localBRows 111) (xyRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row20 :
    digitsEq 111 (rowProduct (abRows 20) localBRows 111) (xyRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row21 :
    digitsEq 111 (rowProduct (abRows 21) localBRows 111) (xyRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row22 :
    digitsEq 111 (rowProduct (abRows 22) localBRows 111) (xyRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row23 :
    digitsEq 111 (rowProduct (abRows 23) localBRows 111) (xyRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row24 :
    digitsEq 111 (rowProduct (abRows 24) localBRows 111) (xyRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row25 :
    digitsEq 111 (rowProduct (abRows 25) localBRows 111) (xyRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row26 :
    digitsEq 111 (rowProduct (abRows 26) localBRows 111) (xyRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row27 :
    digitsEq 111 (rowProduct (abRows 27) localBRows 111) (xyRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row28 :
    digitsEq 111 (rowProduct (abRows 28) localBRows 111) (xyRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row29 :
    digitsEq 111 (rowProduct (abRows 29) localBRows 111) (xyRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row30 :
    digitsEq 111 (rowProduct (abRows 30) localBRows 111) (xyRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row31 :
    digitsEq 111 (rowProduct (abRows 31) localBRows 111) (xyRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row32 :
    digitsEq 111 (rowProduct (abRows 32) localBRows 111) (xyRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row33 :
    digitsEq 111 (rowProduct (abRows 33) localBRows 111) (xyRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row34 :
    digitsEq 111 (rowProduct (abRows 34) localBRows 111) (xyRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row35 :
    digitsEq 111 (rowProduct (abRows 35) localBRows 111) (xyRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row36 :
    digitsEq 111 (rowProduct (abRows 36) localBRows 111) (xyRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row37 :
    digitsEq 111 (rowProduct (abRows 37) localBRows 111) (xyRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row38 :
    digitsEq 111 (rowProduct (abRows 38) localBRows 111) (xyRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row39 :
    digitsEq 111 (rowProduct (abRows 39) localBRows 111) (xyRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row40 :
    digitsEq 111 (rowProduct (abRows 40) localBRows 111) (xyRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row41 :
    digitsEq 111 (rowProduct (abRows 41) localBRows 111) (xyRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row42 :
    digitsEq 111 (rowProduct (abRows 42) localBRows 111) (xyRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row43 :
    digitsEq 111 (rowProduct (abRows 43) localBRows 111) (xyRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row44 :
    digitsEq 111 (rowProduct (abRows 44) localBRows 111) (xyRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row45 :
    digitsEq 111 (rowProduct (abRows 45) localBRows 111) (xyRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row46 :
    digitsEq 111 (rowProduct (abRows 46) localBRows 111) (xyRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row47 :
    digitsEq 111 (rowProduct (abRows 47) localBRows 111) (xyRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row48 :
    digitsEq 111 (rowProduct (abRows 48) localBRows 111) (xyRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row49 :
    digitsEq 111 (rowProduct (abRows 49) localBRows 111) (xyRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row50 :
    digitsEq 111 (rowProduct (abRows 50) localBRows 111) (xyRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row51 :
    digitsEq 111 (rowProduct (abRows 51) localBRows 111) (xyRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row52 :
    digitsEq 111 (rowProduct (abRows 52) localBRows 111) (xyRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row53 :
    digitsEq 111 (rowProduct (abRows 53) localBRows 111) (xyRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row54 :
    digitsEq 111 (rowProduct (abRows 54) localBRows 111) (xyRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row55 :
    digitsEq 111 (rowProduct (abRows 55) localBRows 111) (xyRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row56 :
    digitsEq 111 (rowProduct (abRows 56) localBRows 111) (xyRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row57 :
    digitsEq 111 (rowProduct (abRows 57) localBRows 111) (xyRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row58 :
    digitsEq 111 (rowProduct (abRows 58) localBRows 111) (xyRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row59 :
    digitsEq 111 (rowProduct (abRows 59) localBRows 111) (xyRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row60 :
    digitsEq 111 (rowProduct (abRows 60) localBRows 111) (xyRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row61 :
    digitsEq 111 (rowProduct (abRows 61) localBRows 111) (xyRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row62 :
    digitsEq 111 (rowProduct (abRows 62) localBRows 111) (xyRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row63 :
    digitsEq 111 (rowProduct (abRows 63) localBRows 111) (xyRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row64 :
    digitsEq 111 (rowProduct (abRows 64) localBRows 111) (xyRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row65 :
    digitsEq 111 (rowProduct (abRows 65) localBRows 111) (xyRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row66 :
    digitsEq 111 (rowProduct (abRows 66) localBRows 111) (xyRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row67 :
    digitsEq 111 (rowProduct (abRows 67) localBRows 111) (xyRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row68 :
    digitsEq 111 (rowProduct (abRows 68) localBRows 111) (xyRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row69 :
    digitsEq 111 (rowProduct (abRows 69) localBRows 111) (xyRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row70 :
    digitsEq 111 (rowProduct (abRows 70) localBRows 111) (xyRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row71 :
    digitsEq 111 (rowProduct (abRows 71) localBRows 111) (xyRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row72 :
    digitsEq 111 (rowProduct (abRows 72) localBRows 111) (xyRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row73 :
    digitsEq 111 (rowProduct (abRows 73) localBRows 111) (xyRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row74 :
    digitsEq 111 (rowProduct (abRows 74) localBRows 111) (xyRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row75 :
    digitsEq 111 (rowProduct (abRows 75) localBRows 111) (xyRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row76 :
    digitsEq 111 (rowProduct (abRows 76) localBRows 111) (xyRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row77 :
    digitsEq 111 (rowProduct (abRows 77) localBRows 111) (xyRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row78 :
    digitsEq 111 (rowProduct (abRows 78) localBRows 111) (xyRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row79 :
    digitsEq 111 (rowProduct (abRows 79) localBRows 111) (xyRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row80 :
    digitsEq 111 (rowProduct (abRows 80) localBRows 111) (xyRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row81 :
    digitsEq 111 (rowProduct (abRows 81) localBRows 111) (xyRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row82 :
    digitsEq 111 (rowProduct (abRows 82) localBRows 111) (xyRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row83 :
    digitsEq 111 (rowProduct (abRows 83) localBRows 111) (xyRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row84 :
    digitsEq 111 (rowProduct (abRows 84) localBRows 111) (xyRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row85 :
    digitsEq 111 (rowProduct (abRows 85) localBRows 111) (xyRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row86 :
    digitsEq 111 (rowProduct (abRows 86) localBRows 111) (xyRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row87 :
    digitsEq 111 (rowProduct (abRows 87) localBRows 111) (xyRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row88 :
    digitsEq 111 (rowProduct (abRows 88) localBRows 111) (xyRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row89 :
    digitsEq 111 (rowProduct (abRows 89) localBRows 111) (xyRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row90 :
    digitsEq 111 (rowProduct (abRows 90) localBRows 111) (xyRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row91 :
    digitsEq 111 (rowProduct (abRows 91) localBRows 111) (xyRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row92 :
    digitsEq 111 (rowProduct (abRows 92) localBRows 111) (xyRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row93 :
    digitsEq 111 (rowProduct (abRows 93) localBRows 111) (xyRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row94 :
    digitsEq 111 (rowProduct (abRows 94) localBRows 111) (xyRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row95 :
    digitsEq 111 (rowProduct (abRows 95) localBRows 111) (xyRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row96 :
    digitsEq 111 (rowProduct (abRows 96) localBRows 111) (xyRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row97 :
    digitsEq 111 (rowProduct (abRows 97) localBRows 111) (xyRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row98 :
    digitsEq 111 (rowProduct (abRows 98) localBRows 111) (xyRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row99 :
    digitsEq 111 (rowProduct (abRows 99) localBRows 111) (xyRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row100 :
    digitsEq 111 (rowProduct (abRows 100) localBRows 111) (xyRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row101 :
    digitsEq 111 (rowProduct (abRows 101) localBRows 111) (xyRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row102 :
    digitsEq 111 (rowProduct (abRows 102) localBRows 111) (xyRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row103 :
    digitsEq 111 (rowProduct (abRows 103) localBRows 111) (xyRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row104 :
    digitsEq 111 (rowProduct (abRows 104) localBRows 111) (xyRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row105 :
    digitsEq 111 (rowProduct (abRows 105) localBRows 111) (xyRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row106 :
    digitsEq 111 (rowProduct (abRows 106) localBRows 111) (xyRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row107 :
    digitsEq 111 (rowProduct (abRows 107) localBRows 111) (xyRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row108 :
    digitsEq 111 (rowProduct (abRows 108) localBRows 111) (xyRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row109 :
    digitsEq 111 (rowProduct (abRows 109) localBRows 111) (xyRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_row110 :
    digitsEq 111 (rowProduct (abRows 110) localBRows 111) (xyRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem xy_rows : ∀ i,
    digitsEq 111 (rowProduct (abRows i) localBRows 111) (xyRows i) = true :=
  (Fin.cases xy_row0
    (Fin.cases xy_row1
    (Fin.cases xy_row2
    (Fin.cases xy_row3
    (Fin.cases xy_row4
    (Fin.cases xy_row5
    (Fin.cases xy_row6
    (Fin.cases xy_row7
    (Fin.cases xy_row8
    (Fin.cases xy_row9
    (Fin.cases xy_row10
    (Fin.cases xy_row11
    (Fin.cases xy_row12
    (Fin.cases xy_row13
    (Fin.cases xy_row14
    (Fin.cases xy_row15
    (Fin.cases xy_row16
    (Fin.cases xy_row17
    (Fin.cases xy_row18
    (Fin.cases xy_row19
    (Fin.cases xy_row20
    (Fin.cases xy_row21
    (Fin.cases xy_row22
    (Fin.cases xy_row23
    (Fin.cases xy_row24
    (Fin.cases xy_row25
    (Fin.cases xy_row26
    (Fin.cases xy_row27
    (Fin.cases xy_row28
    (Fin.cases xy_row29
    (Fin.cases xy_row30
    (Fin.cases xy_row31
    (Fin.cases xy_row32
    (Fin.cases xy_row33
    (Fin.cases xy_row34
    (Fin.cases xy_row35
    (Fin.cases xy_row36
    (Fin.cases xy_row37
    (Fin.cases xy_row38
    (Fin.cases xy_row39
    (Fin.cases xy_row40
    (Fin.cases xy_row41
    (Fin.cases xy_row42
    (Fin.cases xy_row43
    (Fin.cases xy_row44
    (Fin.cases xy_row45
    (Fin.cases xy_row46
    (Fin.cases xy_row47
    (Fin.cases xy_row48
    (Fin.cases xy_row49
    (Fin.cases xy_row50
    (Fin.cases xy_row51
    (Fin.cases xy_row52
    (Fin.cases xy_row53
    (Fin.cases xy_row54
    (Fin.cases xy_row55
    (Fin.cases xy_row56
    (Fin.cases xy_row57
    (Fin.cases xy_row58
    (Fin.cases xy_row59
    (Fin.cases xy_row60
    (Fin.cases xy_row61
    (Fin.cases xy_row62
    (Fin.cases xy_row63
    (Fin.cases xy_row64
    (Fin.cases xy_row65
    (Fin.cases xy_row66
    (Fin.cases xy_row67
    (Fin.cases xy_row68
    (Fin.cases xy_row69
    (Fin.cases xy_row70
    (Fin.cases xy_row71
    (Fin.cases xy_row72
    (Fin.cases xy_row73
    (Fin.cases xy_row74
    (Fin.cases xy_row75
    (Fin.cases xy_row76
    (Fin.cases xy_row77
    (Fin.cases xy_row78
    (Fin.cases xy_row79
    (Fin.cases xy_row80
    (Fin.cases xy_row81
    (Fin.cases xy_row82
    (Fin.cases xy_row83
    (Fin.cases xy_row84
    (Fin.cases xy_row85
    (Fin.cases xy_row86
    (Fin.cases xy_row87
    (Fin.cases xy_row88
    (Fin.cases xy_row89
    (Fin.cases xy_row90
    (Fin.cases xy_row91
    (Fin.cases xy_row92
    (Fin.cases xy_row93
    (Fin.cases xy_row94
    (Fin.cases xy_row95
    (Fin.cases xy_row96
    (Fin.cases xy_row97
    (Fin.cases xy_row98
    (Fin.cases xy_row99
    (Fin.cases xy_row100
    (Fin.cases xy_row101
    (Fin.cases xy_row102
    (Fin.cases xy_row103
    (Fin.cases xy_row104
    (Fin.cases xy_row105
    (Fin.cases xy_row106
    (Fin.cases xy_row107
    (Fin.cases xy_row108
    (Fin.cases xy_row109
    (Fin.cases xy_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_xy : abMatrix * localBMatrix = xyMatrix :=
  decode_mul _ _ _ ab_small localB_small xy_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
