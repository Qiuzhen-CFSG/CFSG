module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.CubicData

/-!
# Cubic triple multiplication: xyx6 times localB

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
private theorem seed_row0 :
    digitsEq 111 (rowProduct (xyx6Rows 0) localBRows 111) (seedRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row1 :
    digitsEq 111 (rowProduct (xyx6Rows 1) localBRows 111) (seedRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row2 :
    digitsEq 111 (rowProduct (xyx6Rows 2) localBRows 111) (seedRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row3 :
    digitsEq 111 (rowProduct (xyx6Rows 3) localBRows 111) (seedRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row4 :
    digitsEq 111 (rowProduct (xyx6Rows 4) localBRows 111) (seedRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row5 :
    digitsEq 111 (rowProduct (xyx6Rows 5) localBRows 111) (seedRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row6 :
    digitsEq 111 (rowProduct (xyx6Rows 6) localBRows 111) (seedRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row7 :
    digitsEq 111 (rowProduct (xyx6Rows 7) localBRows 111) (seedRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row8 :
    digitsEq 111 (rowProduct (xyx6Rows 8) localBRows 111) (seedRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row9 :
    digitsEq 111 (rowProduct (xyx6Rows 9) localBRows 111) (seedRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row10 :
    digitsEq 111 (rowProduct (xyx6Rows 10) localBRows 111) (seedRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row11 :
    digitsEq 111 (rowProduct (xyx6Rows 11) localBRows 111) (seedRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row12 :
    digitsEq 111 (rowProduct (xyx6Rows 12) localBRows 111) (seedRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row13 :
    digitsEq 111 (rowProduct (xyx6Rows 13) localBRows 111) (seedRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row14 :
    digitsEq 111 (rowProduct (xyx6Rows 14) localBRows 111) (seedRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row15 :
    digitsEq 111 (rowProduct (xyx6Rows 15) localBRows 111) (seedRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row16 :
    digitsEq 111 (rowProduct (xyx6Rows 16) localBRows 111) (seedRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row17 :
    digitsEq 111 (rowProduct (xyx6Rows 17) localBRows 111) (seedRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row18 :
    digitsEq 111 (rowProduct (xyx6Rows 18) localBRows 111) (seedRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row19 :
    digitsEq 111 (rowProduct (xyx6Rows 19) localBRows 111) (seedRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row20 :
    digitsEq 111 (rowProduct (xyx6Rows 20) localBRows 111) (seedRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row21 :
    digitsEq 111 (rowProduct (xyx6Rows 21) localBRows 111) (seedRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row22 :
    digitsEq 111 (rowProduct (xyx6Rows 22) localBRows 111) (seedRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row23 :
    digitsEq 111 (rowProduct (xyx6Rows 23) localBRows 111) (seedRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row24 :
    digitsEq 111 (rowProduct (xyx6Rows 24) localBRows 111) (seedRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row25 :
    digitsEq 111 (rowProduct (xyx6Rows 25) localBRows 111) (seedRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row26 :
    digitsEq 111 (rowProduct (xyx6Rows 26) localBRows 111) (seedRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row27 :
    digitsEq 111 (rowProduct (xyx6Rows 27) localBRows 111) (seedRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row28 :
    digitsEq 111 (rowProduct (xyx6Rows 28) localBRows 111) (seedRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row29 :
    digitsEq 111 (rowProduct (xyx6Rows 29) localBRows 111) (seedRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row30 :
    digitsEq 111 (rowProduct (xyx6Rows 30) localBRows 111) (seedRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row31 :
    digitsEq 111 (rowProduct (xyx6Rows 31) localBRows 111) (seedRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row32 :
    digitsEq 111 (rowProduct (xyx6Rows 32) localBRows 111) (seedRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row33 :
    digitsEq 111 (rowProduct (xyx6Rows 33) localBRows 111) (seedRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row34 :
    digitsEq 111 (rowProduct (xyx6Rows 34) localBRows 111) (seedRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row35 :
    digitsEq 111 (rowProduct (xyx6Rows 35) localBRows 111) (seedRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row36 :
    digitsEq 111 (rowProduct (xyx6Rows 36) localBRows 111) (seedRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row37 :
    digitsEq 111 (rowProduct (xyx6Rows 37) localBRows 111) (seedRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row38 :
    digitsEq 111 (rowProduct (xyx6Rows 38) localBRows 111) (seedRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row39 :
    digitsEq 111 (rowProduct (xyx6Rows 39) localBRows 111) (seedRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row40 :
    digitsEq 111 (rowProduct (xyx6Rows 40) localBRows 111) (seedRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row41 :
    digitsEq 111 (rowProduct (xyx6Rows 41) localBRows 111) (seedRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row42 :
    digitsEq 111 (rowProduct (xyx6Rows 42) localBRows 111) (seedRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row43 :
    digitsEq 111 (rowProduct (xyx6Rows 43) localBRows 111) (seedRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row44 :
    digitsEq 111 (rowProduct (xyx6Rows 44) localBRows 111) (seedRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row45 :
    digitsEq 111 (rowProduct (xyx6Rows 45) localBRows 111) (seedRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row46 :
    digitsEq 111 (rowProduct (xyx6Rows 46) localBRows 111) (seedRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row47 :
    digitsEq 111 (rowProduct (xyx6Rows 47) localBRows 111) (seedRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row48 :
    digitsEq 111 (rowProduct (xyx6Rows 48) localBRows 111) (seedRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row49 :
    digitsEq 111 (rowProduct (xyx6Rows 49) localBRows 111) (seedRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row50 :
    digitsEq 111 (rowProduct (xyx6Rows 50) localBRows 111) (seedRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row51 :
    digitsEq 111 (rowProduct (xyx6Rows 51) localBRows 111) (seedRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row52 :
    digitsEq 111 (rowProduct (xyx6Rows 52) localBRows 111) (seedRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row53 :
    digitsEq 111 (rowProduct (xyx6Rows 53) localBRows 111) (seedRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row54 :
    digitsEq 111 (rowProduct (xyx6Rows 54) localBRows 111) (seedRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row55 :
    digitsEq 111 (rowProduct (xyx6Rows 55) localBRows 111) (seedRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row56 :
    digitsEq 111 (rowProduct (xyx6Rows 56) localBRows 111) (seedRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row57 :
    digitsEq 111 (rowProduct (xyx6Rows 57) localBRows 111) (seedRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row58 :
    digitsEq 111 (rowProduct (xyx6Rows 58) localBRows 111) (seedRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row59 :
    digitsEq 111 (rowProduct (xyx6Rows 59) localBRows 111) (seedRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row60 :
    digitsEq 111 (rowProduct (xyx6Rows 60) localBRows 111) (seedRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row61 :
    digitsEq 111 (rowProduct (xyx6Rows 61) localBRows 111) (seedRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row62 :
    digitsEq 111 (rowProduct (xyx6Rows 62) localBRows 111) (seedRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row63 :
    digitsEq 111 (rowProduct (xyx6Rows 63) localBRows 111) (seedRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row64 :
    digitsEq 111 (rowProduct (xyx6Rows 64) localBRows 111) (seedRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row65 :
    digitsEq 111 (rowProduct (xyx6Rows 65) localBRows 111) (seedRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row66 :
    digitsEq 111 (rowProduct (xyx6Rows 66) localBRows 111) (seedRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row67 :
    digitsEq 111 (rowProduct (xyx6Rows 67) localBRows 111) (seedRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row68 :
    digitsEq 111 (rowProduct (xyx6Rows 68) localBRows 111) (seedRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row69 :
    digitsEq 111 (rowProduct (xyx6Rows 69) localBRows 111) (seedRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row70 :
    digitsEq 111 (rowProduct (xyx6Rows 70) localBRows 111) (seedRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row71 :
    digitsEq 111 (rowProduct (xyx6Rows 71) localBRows 111) (seedRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row72 :
    digitsEq 111 (rowProduct (xyx6Rows 72) localBRows 111) (seedRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row73 :
    digitsEq 111 (rowProduct (xyx6Rows 73) localBRows 111) (seedRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row74 :
    digitsEq 111 (rowProduct (xyx6Rows 74) localBRows 111) (seedRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row75 :
    digitsEq 111 (rowProduct (xyx6Rows 75) localBRows 111) (seedRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row76 :
    digitsEq 111 (rowProduct (xyx6Rows 76) localBRows 111) (seedRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row77 :
    digitsEq 111 (rowProduct (xyx6Rows 77) localBRows 111) (seedRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row78 :
    digitsEq 111 (rowProduct (xyx6Rows 78) localBRows 111) (seedRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row79 :
    digitsEq 111 (rowProduct (xyx6Rows 79) localBRows 111) (seedRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row80 :
    digitsEq 111 (rowProduct (xyx6Rows 80) localBRows 111) (seedRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row81 :
    digitsEq 111 (rowProduct (xyx6Rows 81) localBRows 111) (seedRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row82 :
    digitsEq 111 (rowProduct (xyx6Rows 82) localBRows 111) (seedRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row83 :
    digitsEq 111 (rowProduct (xyx6Rows 83) localBRows 111) (seedRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row84 :
    digitsEq 111 (rowProduct (xyx6Rows 84) localBRows 111) (seedRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row85 :
    digitsEq 111 (rowProduct (xyx6Rows 85) localBRows 111) (seedRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row86 :
    digitsEq 111 (rowProduct (xyx6Rows 86) localBRows 111) (seedRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row87 :
    digitsEq 111 (rowProduct (xyx6Rows 87) localBRows 111) (seedRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row88 :
    digitsEq 111 (rowProduct (xyx6Rows 88) localBRows 111) (seedRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row89 :
    digitsEq 111 (rowProduct (xyx6Rows 89) localBRows 111) (seedRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row90 :
    digitsEq 111 (rowProduct (xyx6Rows 90) localBRows 111) (seedRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row91 :
    digitsEq 111 (rowProduct (xyx6Rows 91) localBRows 111) (seedRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row92 :
    digitsEq 111 (rowProduct (xyx6Rows 92) localBRows 111) (seedRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row93 :
    digitsEq 111 (rowProduct (xyx6Rows 93) localBRows 111) (seedRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row94 :
    digitsEq 111 (rowProduct (xyx6Rows 94) localBRows 111) (seedRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row95 :
    digitsEq 111 (rowProduct (xyx6Rows 95) localBRows 111) (seedRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row96 :
    digitsEq 111 (rowProduct (xyx6Rows 96) localBRows 111) (seedRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row97 :
    digitsEq 111 (rowProduct (xyx6Rows 97) localBRows 111) (seedRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row98 :
    digitsEq 111 (rowProduct (xyx6Rows 98) localBRows 111) (seedRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row99 :
    digitsEq 111 (rowProduct (xyx6Rows 99) localBRows 111) (seedRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row100 :
    digitsEq 111 (rowProduct (xyx6Rows 100) localBRows 111) (seedRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row101 :
    digitsEq 111 (rowProduct (xyx6Rows 101) localBRows 111) (seedRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row102 :
    digitsEq 111 (rowProduct (xyx6Rows 102) localBRows 111) (seedRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row103 :
    digitsEq 111 (rowProduct (xyx6Rows 103) localBRows 111) (seedRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row104 :
    digitsEq 111 (rowProduct (xyx6Rows 104) localBRows 111) (seedRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row105 :
    digitsEq 111 (rowProduct (xyx6Rows 105) localBRows 111) (seedRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row106 :
    digitsEq 111 (rowProduct (xyx6Rows 106) localBRows 111) (seedRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row107 :
    digitsEq 111 (rowProduct (xyx6Rows 107) localBRows 111) (seedRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row108 :
    digitsEq 111 (rowProduct (xyx6Rows 108) localBRows 111) (seedRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row109 :
    digitsEq 111 (rowProduct (xyx6Rows 109) localBRows 111) (seedRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_row110 :
    digitsEq 111 (rowProduct (xyx6Rows 110) localBRows 111) (seedRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem seed_rows : ∀ i,
    digitsEq 111 (rowProduct (xyx6Rows i) localBRows 111) (seedRows i) = true :=
  (Fin.cases seed_row0
    (Fin.cases seed_row1
    (Fin.cases seed_row2
    (Fin.cases seed_row3
    (Fin.cases seed_row4
    (Fin.cases seed_row5
    (Fin.cases seed_row6
    (Fin.cases seed_row7
    (Fin.cases seed_row8
    (Fin.cases seed_row9
    (Fin.cases seed_row10
    (Fin.cases seed_row11
    (Fin.cases seed_row12
    (Fin.cases seed_row13
    (Fin.cases seed_row14
    (Fin.cases seed_row15
    (Fin.cases seed_row16
    (Fin.cases seed_row17
    (Fin.cases seed_row18
    (Fin.cases seed_row19
    (Fin.cases seed_row20
    (Fin.cases seed_row21
    (Fin.cases seed_row22
    (Fin.cases seed_row23
    (Fin.cases seed_row24
    (Fin.cases seed_row25
    (Fin.cases seed_row26
    (Fin.cases seed_row27
    (Fin.cases seed_row28
    (Fin.cases seed_row29
    (Fin.cases seed_row30
    (Fin.cases seed_row31
    (Fin.cases seed_row32
    (Fin.cases seed_row33
    (Fin.cases seed_row34
    (Fin.cases seed_row35
    (Fin.cases seed_row36
    (Fin.cases seed_row37
    (Fin.cases seed_row38
    (Fin.cases seed_row39
    (Fin.cases seed_row40
    (Fin.cases seed_row41
    (Fin.cases seed_row42
    (Fin.cases seed_row43
    (Fin.cases seed_row44
    (Fin.cases seed_row45
    (Fin.cases seed_row46
    (Fin.cases seed_row47
    (Fin.cases seed_row48
    (Fin.cases seed_row49
    (Fin.cases seed_row50
    (Fin.cases seed_row51
    (Fin.cases seed_row52
    (Fin.cases seed_row53
    (Fin.cases seed_row54
    (Fin.cases seed_row55
    (Fin.cases seed_row56
    (Fin.cases seed_row57
    (Fin.cases seed_row58
    (Fin.cases seed_row59
    (Fin.cases seed_row60
    (Fin.cases seed_row61
    (Fin.cases seed_row62
    (Fin.cases seed_row63
    (Fin.cases seed_row64
    (Fin.cases seed_row65
    (Fin.cases seed_row66
    (Fin.cases seed_row67
    (Fin.cases seed_row68
    (Fin.cases seed_row69
    (Fin.cases seed_row70
    (Fin.cases seed_row71
    (Fin.cases seed_row72
    (Fin.cases seed_row73
    (Fin.cases seed_row74
    (Fin.cases seed_row75
    (Fin.cases seed_row76
    (Fin.cases seed_row77
    (Fin.cases seed_row78
    (Fin.cases seed_row79
    (Fin.cases seed_row80
    (Fin.cases seed_row81
    (Fin.cases seed_row82
    (Fin.cases seed_row83
    (Fin.cases seed_row84
    (Fin.cases seed_row85
    (Fin.cases seed_row86
    (Fin.cases seed_row87
    (Fin.cases seed_row88
    (Fin.cases seed_row89
    (Fin.cases seed_row90
    (Fin.cases seed_row91
    (Fin.cases seed_row92
    (Fin.cases seed_row93
    (Fin.cases seed_row94
    (Fin.cases seed_row95
    (Fin.cases seed_row96
    (Fin.cases seed_row97
    (Fin.cases seed_row98
    (Fin.cases seed_row99
    (Fin.cases seed_row100
    (Fin.cases seed_row101
    (Fin.cases seed_row102
    (Fin.cases seed_row103
    (Fin.cases seed_row104
    (Fin.cases seed_row105
    (Fin.cases seed_row106
    (Fin.cases seed_row107
    (Fin.cases seed_row108
    (Fin.cases seed_row109
    (Fin.cases seed_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_seed : xyx6Matrix * localBMatrix = seedMatrix :=
  decode_mul _ _ _ xyx6_small localB_small seed_rows

end Lyons.SimplicityCertificate.InvolutionElementaryThree.MatrixCertificate
