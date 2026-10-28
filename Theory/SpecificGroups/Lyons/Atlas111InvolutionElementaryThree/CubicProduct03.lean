module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: seed times seed

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
private theorem seed2_row0 :
    digitsEq 111 (rowProduct (seedRows 0) seedRows 111) (seed2Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row1 :
    digitsEq 111 (rowProduct (seedRows 1) seedRows 111) (seed2Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row2 :
    digitsEq 111 (rowProduct (seedRows 2) seedRows 111) (seed2Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row3 :
    digitsEq 111 (rowProduct (seedRows 3) seedRows 111) (seed2Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row4 :
    digitsEq 111 (rowProduct (seedRows 4) seedRows 111) (seed2Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row5 :
    digitsEq 111 (rowProduct (seedRows 5) seedRows 111) (seed2Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row6 :
    digitsEq 111 (rowProduct (seedRows 6) seedRows 111) (seed2Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row7 :
    digitsEq 111 (rowProduct (seedRows 7) seedRows 111) (seed2Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row8 :
    digitsEq 111 (rowProduct (seedRows 8) seedRows 111) (seed2Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row9 :
    digitsEq 111 (rowProduct (seedRows 9) seedRows 111) (seed2Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row10 :
    digitsEq 111 (rowProduct (seedRows 10) seedRows 111) (seed2Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row11 :
    digitsEq 111 (rowProduct (seedRows 11) seedRows 111) (seed2Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row12 :
    digitsEq 111 (rowProduct (seedRows 12) seedRows 111) (seed2Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row13 :
    digitsEq 111 (rowProduct (seedRows 13) seedRows 111) (seed2Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row14 :
    digitsEq 111 (rowProduct (seedRows 14) seedRows 111) (seed2Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row15 :
    digitsEq 111 (rowProduct (seedRows 15) seedRows 111) (seed2Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row16 :
    digitsEq 111 (rowProduct (seedRows 16) seedRows 111) (seed2Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row17 :
    digitsEq 111 (rowProduct (seedRows 17) seedRows 111) (seed2Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row18 :
    digitsEq 111 (rowProduct (seedRows 18) seedRows 111) (seed2Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row19 :
    digitsEq 111 (rowProduct (seedRows 19) seedRows 111) (seed2Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row20 :
    digitsEq 111 (rowProduct (seedRows 20) seedRows 111) (seed2Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row21 :
    digitsEq 111 (rowProduct (seedRows 21) seedRows 111) (seed2Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row22 :
    digitsEq 111 (rowProduct (seedRows 22) seedRows 111) (seed2Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row23 :
    digitsEq 111 (rowProduct (seedRows 23) seedRows 111) (seed2Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row24 :
    digitsEq 111 (rowProduct (seedRows 24) seedRows 111) (seed2Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row25 :
    digitsEq 111 (rowProduct (seedRows 25) seedRows 111) (seed2Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row26 :
    digitsEq 111 (rowProduct (seedRows 26) seedRows 111) (seed2Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row27 :
    digitsEq 111 (rowProduct (seedRows 27) seedRows 111) (seed2Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row28 :
    digitsEq 111 (rowProduct (seedRows 28) seedRows 111) (seed2Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row29 :
    digitsEq 111 (rowProduct (seedRows 29) seedRows 111) (seed2Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row30 :
    digitsEq 111 (rowProduct (seedRows 30) seedRows 111) (seed2Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row31 :
    digitsEq 111 (rowProduct (seedRows 31) seedRows 111) (seed2Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row32 :
    digitsEq 111 (rowProduct (seedRows 32) seedRows 111) (seed2Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row33 :
    digitsEq 111 (rowProduct (seedRows 33) seedRows 111) (seed2Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row34 :
    digitsEq 111 (rowProduct (seedRows 34) seedRows 111) (seed2Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row35 :
    digitsEq 111 (rowProduct (seedRows 35) seedRows 111) (seed2Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row36 :
    digitsEq 111 (rowProduct (seedRows 36) seedRows 111) (seed2Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row37 :
    digitsEq 111 (rowProduct (seedRows 37) seedRows 111) (seed2Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row38 :
    digitsEq 111 (rowProduct (seedRows 38) seedRows 111) (seed2Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row39 :
    digitsEq 111 (rowProduct (seedRows 39) seedRows 111) (seed2Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row40 :
    digitsEq 111 (rowProduct (seedRows 40) seedRows 111) (seed2Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row41 :
    digitsEq 111 (rowProduct (seedRows 41) seedRows 111) (seed2Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row42 :
    digitsEq 111 (rowProduct (seedRows 42) seedRows 111) (seed2Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row43 :
    digitsEq 111 (rowProduct (seedRows 43) seedRows 111) (seed2Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row44 :
    digitsEq 111 (rowProduct (seedRows 44) seedRows 111) (seed2Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row45 :
    digitsEq 111 (rowProduct (seedRows 45) seedRows 111) (seed2Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row46 :
    digitsEq 111 (rowProduct (seedRows 46) seedRows 111) (seed2Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row47 :
    digitsEq 111 (rowProduct (seedRows 47) seedRows 111) (seed2Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row48 :
    digitsEq 111 (rowProduct (seedRows 48) seedRows 111) (seed2Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row49 :
    digitsEq 111 (rowProduct (seedRows 49) seedRows 111) (seed2Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row50 :
    digitsEq 111 (rowProduct (seedRows 50) seedRows 111) (seed2Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row51 :
    digitsEq 111 (rowProduct (seedRows 51) seedRows 111) (seed2Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row52 :
    digitsEq 111 (rowProduct (seedRows 52) seedRows 111) (seed2Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row53 :
    digitsEq 111 (rowProduct (seedRows 53) seedRows 111) (seed2Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row54 :
    digitsEq 111 (rowProduct (seedRows 54) seedRows 111) (seed2Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row55 :
    digitsEq 111 (rowProduct (seedRows 55) seedRows 111) (seed2Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row56 :
    digitsEq 111 (rowProduct (seedRows 56) seedRows 111) (seed2Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row57 :
    digitsEq 111 (rowProduct (seedRows 57) seedRows 111) (seed2Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row58 :
    digitsEq 111 (rowProduct (seedRows 58) seedRows 111) (seed2Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row59 :
    digitsEq 111 (rowProduct (seedRows 59) seedRows 111) (seed2Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row60 :
    digitsEq 111 (rowProduct (seedRows 60) seedRows 111) (seed2Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row61 :
    digitsEq 111 (rowProduct (seedRows 61) seedRows 111) (seed2Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row62 :
    digitsEq 111 (rowProduct (seedRows 62) seedRows 111) (seed2Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row63 :
    digitsEq 111 (rowProduct (seedRows 63) seedRows 111) (seed2Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row64 :
    digitsEq 111 (rowProduct (seedRows 64) seedRows 111) (seed2Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row65 :
    digitsEq 111 (rowProduct (seedRows 65) seedRows 111) (seed2Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row66 :
    digitsEq 111 (rowProduct (seedRows 66) seedRows 111) (seed2Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row67 :
    digitsEq 111 (rowProduct (seedRows 67) seedRows 111) (seed2Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row68 :
    digitsEq 111 (rowProduct (seedRows 68) seedRows 111) (seed2Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row69 :
    digitsEq 111 (rowProduct (seedRows 69) seedRows 111) (seed2Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row70 :
    digitsEq 111 (rowProduct (seedRows 70) seedRows 111) (seed2Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row71 :
    digitsEq 111 (rowProduct (seedRows 71) seedRows 111) (seed2Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row72 :
    digitsEq 111 (rowProduct (seedRows 72) seedRows 111) (seed2Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row73 :
    digitsEq 111 (rowProduct (seedRows 73) seedRows 111) (seed2Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row74 :
    digitsEq 111 (rowProduct (seedRows 74) seedRows 111) (seed2Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row75 :
    digitsEq 111 (rowProduct (seedRows 75) seedRows 111) (seed2Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row76 :
    digitsEq 111 (rowProduct (seedRows 76) seedRows 111) (seed2Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row77 :
    digitsEq 111 (rowProduct (seedRows 77) seedRows 111) (seed2Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row78 :
    digitsEq 111 (rowProduct (seedRows 78) seedRows 111) (seed2Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row79 :
    digitsEq 111 (rowProduct (seedRows 79) seedRows 111) (seed2Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row80 :
    digitsEq 111 (rowProduct (seedRows 80) seedRows 111) (seed2Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row81 :
    digitsEq 111 (rowProduct (seedRows 81) seedRows 111) (seed2Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row82 :
    digitsEq 111 (rowProduct (seedRows 82) seedRows 111) (seed2Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row83 :
    digitsEq 111 (rowProduct (seedRows 83) seedRows 111) (seed2Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row84 :
    digitsEq 111 (rowProduct (seedRows 84) seedRows 111) (seed2Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row85 :
    digitsEq 111 (rowProduct (seedRows 85) seedRows 111) (seed2Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row86 :
    digitsEq 111 (rowProduct (seedRows 86) seedRows 111) (seed2Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row87 :
    digitsEq 111 (rowProduct (seedRows 87) seedRows 111) (seed2Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row88 :
    digitsEq 111 (rowProduct (seedRows 88) seedRows 111) (seed2Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row89 :
    digitsEq 111 (rowProduct (seedRows 89) seedRows 111) (seed2Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row90 :
    digitsEq 111 (rowProduct (seedRows 90) seedRows 111) (seed2Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row91 :
    digitsEq 111 (rowProduct (seedRows 91) seedRows 111) (seed2Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row92 :
    digitsEq 111 (rowProduct (seedRows 92) seedRows 111) (seed2Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row93 :
    digitsEq 111 (rowProduct (seedRows 93) seedRows 111) (seed2Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row94 :
    digitsEq 111 (rowProduct (seedRows 94) seedRows 111) (seed2Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row95 :
    digitsEq 111 (rowProduct (seedRows 95) seedRows 111) (seed2Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row96 :
    digitsEq 111 (rowProduct (seedRows 96) seedRows 111) (seed2Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row97 :
    digitsEq 111 (rowProduct (seedRows 97) seedRows 111) (seed2Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row98 :
    digitsEq 111 (rowProduct (seedRows 98) seedRows 111) (seed2Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row99 :
    digitsEq 111 (rowProduct (seedRows 99) seedRows 111) (seed2Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row100 :
    digitsEq 111 (rowProduct (seedRows 100) seedRows 111) (seed2Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row101 :
    digitsEq 111 (rowProduct (seedRows 101) seedRows 111) (seed2Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row102 :
    digitsEq 111 (rowProduct (seedRows 102) seedRows 111) (seed2Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row103 :
    digitsEq 111 (rowProduct (seedRows 103) seedRows 111) (seed2Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row104 :
    digitsEq 111 (rowProduct (seedRows 104) seedRows 111) (seed2Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row105 :
    digitsEq 111 (rowProduct (seedRows 105) seedRows 111) (seed2Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row106 :
    digitsEq 111 (rowProduct (seedRows 106) seedRows 111) (seed2Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row107 :
    digitsEq 111 (rowProduct (seedRows 107) seedRows 111) (seed2Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row108 :
    digitsEq 111 (rowProduct (seedRows 108) seedRows 111) (seed2Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row109 :
    digitsEq 111 (rowProduct (seedRows 109) seedRows 111) (seed2Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_row110 :
    digitsEq 111 (rowProduct (seedRows 110) seedRows 111) (seed2Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed2_rows : ∀ i,
    digitsEq 111 (rowProduct (seedRows i) seedRows 111) (seed2Rows i) = true :=
  (Fin.cases seed2_row0
    (Fin.cases seed2_row1
    (Fin.cases seed2_row2
    (Fin.cases seed2_row3
    (Fin.cases seed2_row4
    (Fin.cases seed2_row5
    (Fin.cases seed2_row6
    (Fin.cases seed2_row7
    (Fin.cases seed2_row8
    (Fin.cases seed2_row9
    (Fin.cases seed2_row10
    (Fin.cases seed2_row11
    (Fin.cases seed2_row12
    (Fin.cases seed2_row13
    (Fin.cases seed2_row14
    (Fin.cases seed2_row15
    (Fin.cases seed2_row16
    (Fin.cases seed2_row17
    (Fin.cases seed2_row18
    (Fin.cases seed2_row19
    (Fin.cases seed2_row20
    (Fin.cases seed2_row21
    (Fin.cases seed2_row22
    (Fin.cases seed2_row23
    (Fin.cases seed2_row24
    (Fin.cases seed2_row25
    (Fin.cases seed2_row26
    (Fin.cases seed2_row27
    (Fin.cases seed2_row28
    (Fin.cases seed2_row29
    (Fin.cases seed2_row30
    (Fin.cases seed2_row31
    (Fin.cases seed2_row32
    (Fin.cases seed2_row33
    (Fin.cases seed2_row34
    (Fin.cases seed2_row35
    (Fin.cases seed2_row36
    (Fin.cases seed2_row37
    (Fin.cases seed2_row38
    (Fin.cases seed2_row39
    (Fin.cases seed2_row40
    (Fin.cases seed2_row41
    (Fin.cases seed2_row42
    (Fin.cases seed2_row43
    (Fin.cases seed2_row44
    (Fin.cases seed2_row45
    (Fin.cases seed2_row46
    (Fin.cases seed2_row47
    (Fin.cases seed2_row48
    (Fin.cases seed2_row49
    (Fin.cases seed2_row50
    (Fin.cases seed2_row51
    (Fin.cases seed2_row52
    (Fin.cases seed2_row53
    (Fin.cases seed2_row54
    (Fin.cases seed2_row55
    (Fin.cases seed2_row56
    (Fin.cases seed2_row57
    (Fin.cases seed2_row58
    (Fin.cases seed2_row59
    (Fin.cases seed2_row60
    (Fin.cases seed2_row61
    (Fin.cases seed2_row62
    (Fin.cases seed2_row63
    (Fin.cases seed2_row64
    (Fin.cases seed2_row65
    (Fin.cases seed2_row66
    (Fin.cases seed2_row67
    (Fin.cases seed2_row68
    (Fin.cases seed2_row69
    (Fin.cases seed2_row70
    (Fin.cases seed2_row71
    (Fin.cases seed2_row72
    (Fin.cases seed2_row73
    (Fin.cases seed2_row74
    (Fin.cases seed2_row75
    (Fin.cases seed2_row76
    (Fin.cases seed2_row77
    (Fin.cases seed2_row78
    (Fin.cases seed2_row79
    (Fin.cases seed2_row80
    (Fin.cases seed2_row81
    (Fin.cases seed2_row82
    (Fin.cases seed2_row83
    (Fin.cases seed2_row84
    (Fin.cases seed2_row85
    (Fin.cases seed2_row86
    (Fin.cases seed2_row87
    (Fin.cases seed2_row88
    (Fin.cases seed2_row89
    (Fin.cases seed2_row90
    (Fin.cases seed2_row91
    (Fin.cases seed2_row92
    (Fin.cases seed2_row93
    (Fin.cases seed2_row94
    (Fin.cases seed2_row95
    (Fin.cases seed2_row96
    (Fin.cases seed2_row97
    (Fin.cases seed2_row98
    (Fin.cases seed2_row99
    (Fin.cases seed2_row100
    (Fin.cases seed2_row101
    (Fin.cases seed2_row102
    (Fin.cases seed2_row103
    (Fin.cases seed2_row104
    (Fin.cases seed2_row105
    (Fin.cases seed2_row106
    (Fin.cases seed2_row107
    (Fin.cases seed2_row108
    (Fin.cases seed2_row109
    (Fin.cases seed2_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_seed2 : seedMatrix * seedMatrix = seed2Matrix :=
  decode_mul _ _ _ seed_small seed_small seed2_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
