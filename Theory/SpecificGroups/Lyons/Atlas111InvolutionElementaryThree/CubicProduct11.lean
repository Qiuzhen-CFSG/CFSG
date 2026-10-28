module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: localB times second

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
private theorem ySecond_row0 :
    digitsEq 111 (rowProduct (localBRows 0) secondRows 111) (cyRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row1 :
    digitsEq 111 (rowProduct (localBRows 1) secondRows 111) (cyRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row2 :
    digitsEq 111 (rowProduct (localBRows 2) secondRows 111) (cyRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row3 :
    digitsEq 111 (rowProduct (localBRows 3) secondRows 111) (cyRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row4 :
    digitsEq 111 (rowProduct (localBRows 4) secondRows 111) (cyRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row5 :
    digitsEq 111 (rowProduct (localBRows 5) secondRows 111) (cyRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row6 :
    digitsEq 111 (rowProduct (localBRows 6) secondRows 111) (cyRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row7 :
    digitsEq 111 (rowProduct (localBRows 7) secondRows 111) (cyRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row8 :
    digitsEq 111 (rowProduct (localBRows 8) secondRows 111) (cyRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row9 :
    digitsEq 111 (rowProduct (localBRows 9) secondRows 111) (cyRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row10 :
    digitsEq 111 (rowProduct (localBRows 10) secondRows 111) (cyRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row11 :
    digitsEq 111 (rowProduct (localBRows 11) secondRows 111) (cyRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row12 :
    digitsEq 111 (rowProduct (localBRows 12) secondRows 111) (cyRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row13 :
    digitsEq 111 (rowProduct (localBRows 13) secondRows 111) (cyRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row14 :
    digitsEq 111 (rowProduct (localBRows 14) secondRows 111) (cyRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row15 :
    digitsEq 111 (rowProduct (localBRows 15) secondRows 111) (cyRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row16 :
    digitsEq 111 (rowProduct (localBRows 16) secondRows 111) (cyRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row17 :
    digitsEq 111 (rowProduct (localBRows 17) secondRows 111) (cyRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row18 :
    digitsEq 111 (rowProduct (localBRows 18) secondRows 111) (cyRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row19 :
    digitsEq 111 (rowProduct (localBRows 19) secondRows 111) (cyRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row20 :
    digitsEq 111 (rowProduct (localBRows 20) secondRows 111) (cyRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row21 :
    digitsEq 111 (rowProduct (localBRows 21) secondRows 111) (cyRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row22 :
    digitsEq 111 (rowProduct (localBRows 22) secondRows 111) (cyRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row23 :
    digitsEq 111 (rowProduct (localBRows 23) secondRows 111) (cyRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row24 :
    digitsEq 111 (rowProduct (localBRows 24) secondRows 111) (cyRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row25 :
    digitsEq 111 (rowProduct (localBRows 25) secondRows 111) (cyRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row26 :
    digitsEq 111 (rowProduct (localBRows 26) secondRows 111) (cyRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row27 :
    digitsEq 111 (rowProduct (localBRows 27) secondRows 111) (cyRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row28 :
    digitsEq 111 (rowProduct (localBRows 28) secondRows 111) (cyRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row29 :
    digitsEq 111 (rowProduct (localBRows 29) secondRows 111) (cyRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row30 :
    digitsEq 111 (rowProduct (localBRows 30) secondRows 111) (cyRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row31 :
    digitsEq 111 (rowProduct (localBRows 31) secondRows 111) (cyRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row32 :
    digitsEq 111 (rowProduct (localBRows 32) secondRows 111) (cyRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row33 :
    digitsEq 111 (rowProduct (localBRows 33) secondRows 111) (cyRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row34 :
    digitsEq 111 (rowProduct (localBRows 34) secondRows 111) (cyRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row35 :
    digitsEq 111 (rowProduct (localBRows 35) secondRows 111) (cyRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row36 :
    digitsEq 111 (rowProduct (localBRows 36) secondRows 111) (cyRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row37 :
    digitsEq 111 (rowProduct (localBRows 37) secondRows 111) (cyRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row38 :
    digitsEq 111 (rowProduct (localBRows 38) secondRows 111) (cyRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row39 :
    digitsEq 111 (rowProduct (localBRows 39) secondRows 111) (cyRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row40 :
    digitsEq 111 (rowProduct (localBRows 40) secondRows 111) (cyRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row41 :
    digitsEq 111 (rowProduct (localBRows 41) secondRows 111) (cyRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row42 :
    digitsEq 111 (rowProduct (localBRows 42) secondRows 111) (cyRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row43 :
    digitsEq 111 (rowProduct (localBRows 43) secondRows 111) (cyRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row44 :
    digitsEq 111 (rowProduct (localBRows 44) secondRows 111) (cyRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row45 :
    digitsEq 111 (rowProduct (localBRows 45) secondRows 111) (cyRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row46 :
    digitsEq 111 (rowProduct (localBRows 46) secondRows 111) (cyRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row47 :
    digitsEq 111 (rowProduct (localBRows 47) secondRows 111) (cyRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row48 :
    digitsEq 111 (rowProduct (localBRows 48) secondRows 111) (cyRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row49 :
    digitsEq 111 (rowProduct (localBRows 49) secondRows 111) (cyRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row50 :
    digitsEq 111 (rowProduct (localBRows 50) secondRows 111) (cyRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row51 :
    digitsEq 111 (rowProduct (localBRows 51) secondRows 111) (cyRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row52 :
    digitsEq 111 (rowProduct (localBRows 52) secondRows 111) (cyRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row53 :
    digitsEq 111 (rowProduct (localBRows 53) secondRows 111) (cyRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row54 :
    digitsEq 111 (rowProduct (localBRows 54) secondRows 111) (cyRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row55 :
    digitsEq 111 (rowProduct (localBRows 55) secondRows 111) (cyRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row56 :
    digitsEq 111 (rowProduct (localBRows 56) secondRows 111) (cyRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row57 :
    digitsEq 111 (rowProduct (localBRows 57) secondRows 111) (cyRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row58 :
    digitsEq 111 (rowProduct (localBRows 58) secondRows 111) (cyRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row59 :
    digitsEq 111 (rowProduct (localBRows 59) secondRows 111) (cyRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row60 :
    digitsEq 111 (rowProduct (localBRows 60) secondRows 111) (cyRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row61 :
    digitsEq 111 (rowProduct (localBRows 61) secondRows 111) (cyRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row62 :
    digitsEq 111 (rowProduct (localBRows 62) secondRows 111) (cyRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row63 :
    digitsEq 111 (rowProduct (localBRows 63) secondRows 111) (cyRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row64 :
    digitsEq 111 (rowProduct (localBRows 64) secondRows 111) (cyRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row65 :
    digitsEq 111 (rowProduct (localBRows 65) secondRows 111) (cyRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row66 :
    digitsEq 111 (rowProduct (localBRows 66) secondRows 111) (cyRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row67 :
    digitsEq 111 (rowProduct (localBRows 67) secondRows 111) (cyRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row68 :
    digitsEq 111 (rowProduct (localBRows 68) secondRows 111) (cyRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row69 :
    digitsEq 111 (rowProduct (localBRows 69) secondRows 111) (cyRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row70 :
    digitsEq 111 (rowProduct (localBRows 70) secondRows 111) (cyRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row71 :
    digitsEq 111 (rowProduct (localBRows 71) secondRows 111) (cyRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row72 :
    digitsEq 111 (rowProduct (localBRows 72) secondRows 111) (cyRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row73 :
    digitsEq 111 (rowProduct (localBRows 73) secondRows 111) (cyRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row74 :
    digitsEq 111 (rowProduct (localBRows 74) secondRows 111) (cyRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row75 :
    digitsEq 111 (rowProduct (localBRows 75) secondRows 111) (cyRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row76 :
    digitsEq 111 (rowProduct (localBRows 76) secondRows 111) (cyRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row77 :
    digitsEq 111 (rowProduct (localBRows 77) secondRows 111) (cyRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row78 :
    digitsEq 111 (rowProduct (localBRows 78) secondRows 111) (cyRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row79 :
    digitsEq 111 (rowProduct (localBRows 79) secondRows 111) (cyRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row80 :
    digitsEq 111 (rowProduct (localBRows 80) secondRows 111) (cyRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row81 :
    digitsEq 111 (rowProduct (localBRows 81) secondRows 111) (cyRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row82 :
    digitsEq 111 (rowProduct (localBRows 82) secondRows 111) (cyRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row83 :
    digitsEq 111 (rowProduct (localBRows 83) secondRows 111) (cyRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row84 :
    digitsEq 111 (rowProduct (localBRows 84) secondRows 111) (cyRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row85 :
    digitsEq 111 (rowProduct (localBRows 85) secondRows 111) (cyRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row86 :
    digitsEq 111 (rowProduct (localBRows 86) secondRows 111) (cyRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row87 :
    digitsEq 111 (rowProduct (localBRows 87) secondRows 111) (cyRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row88 :
    digitsEq 111 (rowProduct (localBRows 88) secondRows 111) (cyRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row89 :
    digitsEq 111 (rowProduct (localBRows 89) secondRows 111) (cyRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row90 :
    digitsEq 111 (rowProduct (localBRows 90) secondRows 111) (cyRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row91 :
    digitsEq 111 (rowProduct (localBRows 91) secondRows 111) (cyRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row92 :
    digitsEq 111 (rowProduct (localBRows 92) secondRows 111) (cyRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row93 :
    digitsEq 111 (rowProduct (localBRows 93) secondRows 111) (cyRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row94 :
    digitsEq 111 (rowProduct (localBRows 94) secondRows 111) (cyRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row95 :
    digitsEq 111 (rowProduct (localBRows 95) secondRows 111) (cyRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row96 :
    digitsEq 111 (rowProduct (localBRows 96) secondRows 111) (cyRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row97 :
    digitsEq 111 (rowProduct (localBRows 97) secondRows 111) (cyRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row98 :
    digitsEq 111 (rowProduct (localBRows 98) secondRows 111) (cyRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row99 :
    digitsEq 111 (rowProduct (localBRows 99) secondRows 111) (cyRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row100 :
    digitsEq 111 (rowProduct (localBRows 100) secondRows 111) (cyRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row101 :
    digitsEq 111 (rowProduct (localBRows 101) secondRows 111) (cyRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row102 :
    digitsEq 111 (rowProduct (localBRows 102) secondRows 111) (cyRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row103 :
    digitsEq 111 (rowProduct (localBRows 103) secondRows 111) (cyRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row104 :
    digitsEq 111 (rowProduct (localBRows 104) secondRows 111) (cyRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row105 :
    digitsEq 111 (rowProduct (localBRows 105) secondRows 111) (cyRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row106 :
    digitsEq 111 (rowProduct (localBRows 106) secondRows 111) (cyRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row107 :
    digitsEq 111 (rowProduct (localBRows 107) secondRows 111) (cyRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row108 :
    digitsEq 111 (rowProduct (localBRows 108) secondRows 111) (cyRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row109 :
    digitsEq 111 (rowProduct (localBRows 109) secondRows 111) (cyRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_row110 :
    digitsEq 111 (rowProduct (localBRows 110) secondRows 111) (cyRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem ySecond_rows : ∀ i,
    digitsEq 111 (rowProduct (localBRows i) secondRows 111) (cyRows i) = true :=
  (Fin.cases ySecond_row0
    (Fin.cases ySecond_row1
    (Fin.cases ySecond_row2
    (Fin.cases ySecond_row3
    (Fin.cases ySecond_row4
    (Fin.cases ySecond_row5
    (Fin.cases ySecond_row6
    (Fin.cases ySecond_row7
    (Fin.cases ySecond_row8
    (Fin.cases ySecond_row9
    (Fin.cases ySecond_row10
    (Fin.cases ySecond_row11
    (Fin.cases ySecond_row12
    (Fin.cases ySecond_row13
    (Fin.cases ySecond_row14
    (Fin.cases ySecond_row15
    (Fin.cases ySecond_row16
    (Fin.cases ySecond_row17
    (Fin.cases ySecond_row18
    (Fin.cases ySecond_row19
    (Fin.cases ySecond_row20
    (Fin.cases ySecond_row21
    (Fin.cases ySecond_row22
    (Fin.cases ySecond_row23
    (Fin.cases ySecond_row24
    (Fin.cases ySecond_row25
    (Fin.cases ySecond_row26
    (Fin.cases ySecond_row27
    (Fin.cases ySecond_row28
    (Fin.cases ySecond_row29
    (Fin.cases ySecond_row30
    (Fin.cases ySecond_row31
    (Fin.cases ySecond_row32
    (Fin.cases ySecond_row33
    (Fin.cases ySecond_row34
    (Fin.cases ySecond_row35
    (Fin.cases ySecond_row36
    (Fin.cases ySecond_row37
    (Fin.cases ySecond_row38
    (Fin.cases ySecond_row39
    (Fin.cases ySecond_row40
    (Fin.cases ySecond_row41
    (Fin.cases ySecond_row42
    (Fin.cases ySecond_row43
    (Fin.cases ySecond_row44
    (Fin.cases ySecond_row45
    (Fin.cases ySecond_row46
    (Fin.cases ySecond_row47
    (Fin.cases ySecond_row48
    (Fin.cases ySecond_row49
    (Fin.cases ySecond_row50
    (Fin.cases ySecond_row51
    (Fin.cases ySecond_row52
    (Fin.cases ySecond_row53
    (Fin.cases ySecond_row54
    (Fin.cases ySecond_row55
    (Fin.cases ySecond_row56
    (Fin.cases ySecond_row57
    (Fin.cases ySecond_row58
    (Fin.cases ySecond_row59
    (Fin.cases ySecond_row60
    (Fin.cases ySecond_row61
    (Fin.cases ySecond_row62
    (Fin.cases ySecond_row63
    (Fin.cases ySecond_row64
    (Fin.cases ySecond_row65
    (Fin.cases ySecond_row66
    (Fin.cases ySecond_row67
    (Fin.cases ySecond_row68
    (Fin.cases ySecond_row69
    (Fin.cases ySecond_row70
    (Fin.cases ySecond_row71
    (Fin.cases ySecond_row72
    (Fin.cases ySecond_row73
    (Fin.cases ySecond_row74
    (Fin.cases ySecond_row75
    (Fin.cases ySecond_row76
    (Fin.cases ySecond_row77
    (Fin.cases ySecond_row78
    (Fin.cases ySecond_row79
    (Fin.cases ySecond_row80
    (Fin.cases ySecond_row81
    (Fin.cases ySecond_row82
    (Fin.cases ySecond_row83
    (Fin.cases ySecond_row84
    (Fin.cases ySecond_row85
    (Fin.cases ySecond_row86
    (Fin.cases ySecond_row87
    (Fin.cases ySecond_row88
    (Fin.cases ySecond_row89
    (Fin.cases ySecond_row90
    (Fin.cases ySecond_row91
    (Fin.cases ySecond_row92
    (Fin.cases ySecond_row93
    (Fin.cases ySecond_row94
    (Fin.cases ySecond_row95
    (Fin.cases ySecond_row96
    (Fin.cases ySecond_row97
    (Fin.cases ySecond_row98
    (Fin.cases ySecond_row99
    (Fin.cases ySecond_row100
    (Fin.cases ySecond_row101
    (Fin.cases ySecond_row102
    (Fin.cases ySecond_row103
    (Fin.cases ySecond_row104
    (Fin.cases ySecond_row105
    (Fin.cases ySecond_row106
    (Fin.cases ySecond_row107
    (Fin.cases ySecond_row108
    (Fin.cases ySecond_row109
    (Fin.cases ySecond_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_ySecond : localBMatrix * secondMatrix = cyMatrix :=
  decode_mul _ _ _ localB_small second_small ySecond_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
