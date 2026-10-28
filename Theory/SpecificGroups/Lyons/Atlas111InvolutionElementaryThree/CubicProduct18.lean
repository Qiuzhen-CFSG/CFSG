module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: second times third

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
private theorem pair12_row0 :
    digitsEq 111 (rowProduct (secondRows 0) thirdRows 111) (pair12Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row1 :
    digitsEq 111 (rowProduct (secondRows 1) thirdRows 111) (pair12Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row2 :
    digitsEq 111 (rowProduct (secondRows 2) thirdRows 111) (pair12Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row3 :
    digitsEq 111 (rowProduct (secondRows 3) thirdRows 111) (pair12Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row4 :
    digitsEq 111 (rowProduct (secondRows 4) thirdRows 111) (pair12Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row5 :
    digitsEq 111 (rowProduct (secondRows 5) thirdRows 111) (pair12Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row6 :
    digitsEq 111 (rowProduct (secondRows 6) thirdRows 111) (pair12Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row7 :
    digitsEq 111 (rowProduct (secondRows 7) thirdRows 111) (pair12Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row8 :
    digitsEq 111 (rowProduct (secondRows 8) thirdRows 111) (pair12Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row9 :
    digitsEq 111 (rowProduct (secondRows 9) thirdRows 111) (pair12Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row10 :
    digitsEq 111 (rowProduct (secondRows 10) thirdRows 111) (pair12Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row11 :
    digitsEq 111 (rowProduct (secondRows 11) thirdRows 111) (pair12Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row12 :
    digitsEq 111 (rowProduct (secondRows 12) thirdRows 111) (pair12Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row13 :
    digitsEq 111 (rowProduct (secondRows 13) thirdRows 111) (pair12Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row14 :
    digitsEq 111 (rowProduct (secondRows 14) thirdRows 111) (pair12Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row15 :
    digitsEq 111 (rowProduct (secondRows 15) thirdRows 111) (pair12Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row16 :
    digitsEq 111 (rowProduct (secondRows 16) thirdRows 111) (pair12Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row17 :
    digitsEq 111 (rowProduct (secondRows 17) thirdRows 111) (pair12Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row18 :
    digitsEq 111 (rowProduct (secondRows 18) thirdRows 111) (pair12Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row19 :
    digitsEq 111 (rowProduct (secondRows 19) thirdRows 111) (pair12Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row20 :
    digitsEq 111 (rowProduct (secondRows 20) thirdRows 111) (pair12Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row21 :
    digitsEq 111 (rowProduct (secondRows 21) thirdRows 111) (pair12Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row22 :
    digitsEq 111 (rowProduct (secondRows 22) thirdRows 111) (pair12Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row23 :
    digitsEq 111 (rowProduct (secondRows 23) thirdRows 111) (pair12Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row24 :
    digitsEq 111 (rowProduct (secondRows 24) thirdRows 111) (pair12Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row25 :
    digitsEq 111 (rowProduct (secondRows 25) thirdRows 111) (pair12Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row26 :
    digitsEq 111 (rowProduct (secondRows 26) thirdRows 111) (pair12Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row27 :
    digitsEq 111 (rowProduct (secondRows 27) thirdRows 111) (pair12Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row28 :
    digitsEq 111 (rowProduct (secondRows 28) thirdRows 111) (pair12Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row29 :
    digitsEq 111 (rowProduct (secondRows 29) thirdRows 111) (pair12Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row30 :
    digitsEq 111 (rowProduct (secondRows 30) thirdRows 111) (pair12Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row31 :
    digitsEq 111 (rowProduct (secondRows 31) thirdRows 111) (pair12Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row32 :
    digitsEq 111 (rowProduct (secondRows 32) thirdRows 111) (pair12Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row33 :
    digitsEq 111 (rowProduct (secondRows 33) thirdRows 111) (pair12Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row34 :
    digitsEq 111 (rowProduct (secondRows 34) thirdRows 111) (pair12Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row35 :
    digitsEq 111 (rowProduct (secondRows 35) thirdRows 111) (pair12Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row36 :
    digitsEq 111 (rowProduct (secondRows 36) thirdRows 111) (pair12Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row37 :
    digitsEq 111 (rowProduct (secondRows 37) thirdRows 111) (pair12Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row38 :
    digitsEq 111 (rowProduct (secondRows 38) thirdRows 111) (pair12Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row39 :
    digitsEq 111 (rowProduct (secondRows 39) thirdRows 111) (pair12Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row40 :
    digitsEq 111 (rowProduct (secondRows 40) thirdRows 111) (pair12Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row41 :
    digitsEq 111 (rowProduct (secondRows 41) thirdRows 111) (pair12Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row42 :
    digitsEq 111 (rowProduct (secondRows 42) thirdRows 111) (pair12Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row43 :
    digitsEq 111 (rowProduct (secondRows 43) thirdRows 111) (pair12Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row44 :
    digitsEq 111 (rowProduct (secondRows 44) thirdRows 111) (pair12Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row45 :
    digitsEq 111 (rowProduct (secondRows 45) thirdRows 111) (pair12Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row46 :
    digitsEq 111 (rowProduct (secondRows 46) thirdRows 111) (pair12Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row47 :
    digitsEq 111 (rowProduct (secondRows 47) thirdRows 111) (pair12Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row48 :
    digitsEq 111 (rowProduct (secondRows 48) thirdRows 111) (pair12Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row49 :
    digitsEq 111 (rowProduct (secondRows 49) thirdRows 111) (pair12Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row50 :
    digitsEq 111 (rowProduct (secondRows 50) thirdRows 111) (pair12Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row51 :
    digitsEq 111 (rowProduct (secondRows 51) thirdRows 111) (pair12Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row52 :
    digitsEq 111 (rowProduct (secondRows 52) thirdRows 111) (pair12Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row53 :
    digitsEq 111 (rowProduct (secondRows 53) thirdRows 111) (pair12Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row54 :
    digitsEq 111 (rowProduct (secondRows 54) thirdRows 111) (pair12Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row55 :
    digitsEq 111 (rowProduct (secondRows 55) thirdRows 111) (pair12Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row56 :
    digitsEq 111 (rowProduct (secondRows 56) thirdRows 111) (pair12Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row57 :
    digitsEq 111 (rowProduct (secondRows 57) thirdRows 111) (pair12Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row58 :
    digitsEq 111 (rowProduct (secondRows 58) thirdRows 111) (pair12Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row59 :
    digitsEq 111 (rowProduct (secondRows 59) thirdRows 111) (pair12Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row60 :
    digitsEq 111 (rowProduct (secondRows 60) thirdRows 111) (pair12Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row61 :
    digitsEq 111 (rowProduct (secondRows 61) thirdRows 111) (pair12Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row62 :
    digitsEq 111 (rowProduct (secondRows 62) thirdRows 111) (pair12Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row63 :
    digitsEq 111 (rowProduct (secondRows 63) thirdRows 111) (pair12Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row64 :
    digitsEq 111 (rowProduct (secondRows 64) thirdRows 111) (pair12Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row65 :
    digitsEq 111 (rowProduct (secondRows 65) thirdRows 111) (pair12Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row66 :
    digitsEq 111 (rowProduct (secondRows 66) thirdRows 111) (pair12Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row67 :
    digitsEq 111 (rowProduct (secondRows 67) thirdRows 111) (pair12Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row68 :
    digitsEq 111 (rowProduct (secondRows 68) thirdRows 111) (pair12Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row69 :
    digitsEq 111 (rowProduct (secondRows 69) thirdRows 111) (pair12Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row70 :
    digitsEq 111 (rowProduct (secondRows 70) thirdRows 111) (pair12Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row71 :
    digitsEq 111 (rowProduct (secondRows 71) thirdRows 111) (pair12Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row72 :
    digitsEq 111 (rowProduct (secondRows 72) thirdRows 111) (pair12Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row73 :
    digitsEq 111 (rowProduct (secondRows 73) thirdRows 111) (pair12Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row74 :
    digitsEq 111 (rowProduct (secondRows 74) thirdRows 111) (pair12Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row75 :
    digitsEq 111 (rowProduct (secondRows 75) thirdRows 111) (pair12Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row76 :
    digitsEq 111 (rowProduct (secondRows 76) thirdRows 111) (pair12Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row77 :
    digitsEq 111 (rowProduct (secondRows 77) thirdRows 111) (pair12Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row78 :
    digitsEq 111 (rowProduct (secondRows 78) thirdRows 111) (pair12Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row79 :
    digitsEq 111 (rowProduct (secondRows 79) thirdRows 111) (pair12Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row80 :
    digitsEq 111 (rowProduct (secondRows 80) thirdRows 111) (pair12Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row81 :
    digitsEq 111 (rowProduct (secondRows 81) thirdRows 111) (pair12Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row82 :
    digitsEq 111 (rowProduct (secondRows 82) thirdRows 111) (pair12Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row83 :
    digitsEq 111 (rowProduct (secondRows 83) thirdRows 111) (pair12Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row84 :
    digitsEq 111 (rowProduct (secondRows 84) thirdRows 111) (pair12Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row85 :
    digitsEq 111 (rowProduct (secondRows 85) thirdRows 111) (pair12Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row86 :
    digitsEq 111 (rowProduct (secondRows 86) thirdRows 111) (pair12Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row87 :
    digitsEq 111 (rowProduct (secondRows 87) thirdRows 111) (pair12Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row88 :
    digitsEq 111 (rowProduct (secondRows 88) thirdRows 111) (pair12Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row89 :
    digitsEq 111 (rowProduct (secondRows 89) thirdRows 111) (pair12Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row90 :
    digitsEq 111 (rowProduct (secondRows 90) thirdRows 111) (pair12Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row91 :
    digitsEq 111 (rowProduct (secondRows 91) thirdRows 111) (pair12Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row92 :
    digitsEq 111 (rowProduct (secondRows 92) thirdRows 111) (pair12Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row93 :
    digitsEq 111 (rowProduct (secondRows 93) thirdRows 111) (pair12Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row94 :
    digitsEq 111 (rowProduct (secondRows 94) thirdRows 111) (pair12Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row95 :
    digitsEq 111 (rowProduct (secondRows 95) thirdRows 111) (pair12Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row96 :
    digitsEq 111 (rowProduct (secondRows 96) thirdRows 111) (pair12Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row97 :
    digitsEq 111 (rowProduct (secondRows 97) thirdRows 111) (pair12Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row98 :
    digitsEq 111 (rowProduct (secondRows 98) thirdRows 111) (pair12Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row99 :
    digitsEq 111 (rowProduct (secondRows 99) thirdRows 111) (pair12Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row100 :
    digitsEq 111 (rowProduct (secondRows 100) thirdRows 111) (pair12Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row101 :
    digitsEq 111 (rowProduct (secondRows 101) thirdRows 111) (pair12Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row102 :
    digitsEq 111 (rowProduct (secondRows 102) thirdRows 111) (pair12Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row103 :
    digitsEq 111 (rowProduct (secondRows 103) thirdRows 111) (pair12Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row104 :
    digitsEq 111 (rowProduct (secondRows 104) thirdRows 111) (pair12Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row105 :
    digitsEq 111 (rowProduct (secondRows 105) thirdRows 111) (pair12Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row106 :
    digitsEq 111 (rowProduct (secondRows 106) thirdRows 111) (pair12Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row107 :
    digitsEq 111 (rowProduct (secondRows 107) thirdRows 111) (pair12Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row108 :
    digitsEq 111 (rowProduct (secondRows 108) thirdRows 111) (pair12Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row109 :
    digitsEq 111 (rowProduct (secondRows 109) thirdRows 111) (pair12Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_row110 :
    digitsEq 111 (rowProduct (secondRows 110) thirdRows 111) (pair12Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem pair12_rows : ∀ i,
    digitsEq 111 (rowProduct (secondRows i) thirdRows 111) (pair12Rows i) = true :=
  (Fin.cases pair12_row0
    (Fin.cases pair12_row1
    (Fin.cases pair12_row2
    (Fin.cases pair12_row3
    (Fin.cases pair12_row4
    (Fin.cases pair12_row5
    (Fin.cases pair12_row6
    (Fin.cases pair12_row7
    (Fin.cases pair12_row8
    (Fin.cases pair12_row9
    (Fin.cases pair12_row10
    (Fin.cases pair12_row11
    (Fin.cases pair12_row12
    (Fin.cases pair12_row13
    (Fin.cases pair12_row14
    (Fin.cases pair12_row15
    (Fin.cases pair12_row16
    (Fin.cases pair12_row17
    (Fin.cases pair12_row18
    (Fin.cases pair12_row19
    (Fin.cases pair12_row20
    (Fin.cases pair12_row21
    (Fin.cases pair12_row22
    (Fin.cases pair12_row23
    (Fin.cases pair12_row24
    (Fin.cases pair12_row25
    (Fin.cases pair12_row26
    (Fin.cases pair12_row27
    (Fin.cases pair12_row28
    (Fin.cases pair12_row29
    (Fin.cases pair12_row30
    (Fin.cases pair12_row31
    (Fin.cases pair12_row32
    (Fin.cases pair12_row33
    (Fin.cases pair12_row34
    (Fin.cases pair12_row35
    (Fin.cases pair12_row36
    (Fin.cases pair12_row37
    (Fin.cases pair12_row38
    (Fin.cases pair12_row39
    (Fin.cases pair12_row40
    (Fin.cases pair12_row41
    (Fin.cases pair12_row42
    (Fin.cases pair12_row43
    (Fin.cases pair12_row44
    (Fin.cases pair12_row45
    (Fin.cases pair12_row46
    (Fin.cases pair12_row47
    (Fin.cases pair12_row48
    (Fin.cases pair12_row49
    (Fin.cases pair12_row50
    (Fin.cases pair12_row51
    (Fin.cases pair12_row52
    (Fin.cases pair12_row53
    (Fin.cases pair12_row54
    (Fin.cases pair12_row55
    (Fin.cases pair12_row56
    (Fin.cases pair12_row57
    (Fin.cases pair12_row58
    (Fin.cases pair12_row59
    (Fin.cases pair12_row60
    (Fin.cases pair12_row61
    (Fin.cases pair12_row62
    (Fin.cases pair12_row63
    (Fin.cases pair12_row64
    (Fin.cases pair12_row65
    (Fin.cases pair12_row66
    (Fin.cases pair12_row67
    (Fin.cases pair12_row68
    (Fin.cases pair12_row69
    (Fin.cases pair12_row70
    (Fin.cases pair12_row71
    (Fin.cases pair12_row72
    (Fin.cases pair12_row73
    (Fin.cases pair12_row74
    (Fin.cases pair12_row75
    (Fin.cases pair12_row76
    (Fin.cases pair12_row77
    (Fin.cases pair12_row78
    (Fin.cases pair12_row79
    (Fin.cases pair12_row80
    (Fin.cases pair12_row81
    (Fin.cases pair12_row82
    (Fin.cases pair12_row83
    (Fin.cases pair12_row84
    (Fin.cases pair12_row85
    (Fin.cases pair12_row86
    (Fin.cases pair12_row87
    (Fin.cases pair12_row88
    (Fin.cases pair12_row89
    (Fin.cases pair12_row90
    (Fin.cases pair12_row91
    (Fin.cases pair12_row92
    (Fin.cases pair12_row93
    (Fin.cases pair12_row94
    (Fin.cases pair12_row95
    (Fin.cases pair12_row96
    (Fin.cases pair12_row97
    (Fin.cases pair12_row98
    (Fin.cases pair12_row99
    (Fin.cases pair12_row100
    (Fin.cases pair12_row101
    (Fin.cases pair12_row102
    (Fin.cases pair12_row103
    (Fin.cases pair12_row104
    (Fin.cases pair12_row105
    (Fin.cases pair12_row106
    (Fin.cases pair12_row107
    (Fin.cases pair12_row108
    (Fin.cases pair12_row109
    (Fin.cases pair12_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_pair12 : secondMatrix * thirdMatrix = pair12Matrix :=
  decode_mul _ _ _ second_small third_small pair12_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
