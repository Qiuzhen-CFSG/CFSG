module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: b times b

These 111 row checks certify `bMatrix * bMatrix = b2Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row0 :
    digitsEq 111 (rowProduct (bRows 0) bRows 111) (b2Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row1 :
    digitsEq 111 (rowProduct (bRows 1) bRows 111) (b2Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row2 :
    digitsEq 111 (rowProduct (bRows 2) bRows 111) (b2Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row3 :
    digitsEq 111 (rowProduct (bRows 3) bRows 111) (b2Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row4 :
    digitsEq 111 (rowProduct (bRows 4) bRows 111) (b2Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row5 :
    digitsEq 111 (rowProduct (bRows 5) bRows 111) (b2Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row6 :
    digitsEq 111 (rowProduct (bRows 6) bRows 111) (b2Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row7 :
    digitsEq 111 (rowProduct (bRows 7) bRows 111) (b2Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row8 :
    digitsEq 111 (rowProduct (bRows 8) bRows 111) (b2Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row9 :
    digitsEq 111 (rowProduct (bRows 9) bRows 111) (b2Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row10 :
    digitsEq 111 (rowProduct (bRows 10) bRows 111) (b2Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row11 :
    digitsEq 111 (rowProduct (bRows 11) bRows 111) (b2Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row12 :
    digitsEq 111 (rowProduct (bRows 12) bRows 111) (b2Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row13 :
    digitsEq 111 (rowProduct (bRows 13) bRows 111) (b2Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row14 :
    digitsEq 111 (rowProduct (bRows 14) bRows 111) (b2Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row15 :
    digitsEq 111 (rowProduct (bRows 15) bRows 111) (b2Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row16 :
    digitsEq 111 (rowProduct (bRows 16) bRows 111) (b2Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row17 :
    digitsEq 111 (rowProduct (bRows 17) bRows 111) (b2Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row18 :
    digitsEq 111 (rowProduct (bRows 18) bRows 111) (b2Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row19 :
    digitsEq 111 (rowProduct (bRows 19) bRows 111) (b2Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row20 :
    digitsEq 111 (rowProduct (bRows 20) bRows 111) (b2Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row21 :
    digitsEq 111 (rowProduct (bRows 21) bRows 111) (b2Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row22 :
    digitsEq 111 (rowProduct (bRows 22) bRows 111) (b2Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row23 :
    digitsEq 111 (rowProduct (bRows 23) bRows 111) (b2Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row24 :
    digitsEq 111 (rowProduct (bRows 24) bRows 111) (b2Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row25 :
    digitsEq 111 (rowProduct (bRows 25) bRows 111) (b2Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row26 :
    digitsEq 111 (rowProduct (bRows 26) bRows 111) (b2Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row27 :
    digitsEq 111 (rowProduct (bRows 27) bRows 111) (b2Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row28 :
    digitsEq 111 (rowProduct (bRows 28) bRows 111) (b2Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row29 :
    digitsEq 111 (rowProduct (bRows 29) bRows 111) (b2Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row30 :
    digitsEq 111 (rowProduct (bRows 30) bRows 111) (b2Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row31 :
    digitsEq 111 (rowProduct (bRows 31) bRows 111) (b2Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row32 :
    digitsEq 111 (rowProduct (bRows 32) bRows 111) (b2Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row33 :
    digitsEq 111 (rowProduct (bRows 33) bRows 111) (b2Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row34 :
    digitsEq 111 (rowProduct (bRows 34) bRows 111) (b2Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row35 :
    digitsEq 111 (rowProduct (bRows 35) bRows 111) (b2Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row36 :
    digitsEq 111 (rowProduct (bRows 36) bRows 111) (b2Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row37 :
    digitsEq 111 (rowProduct (bRows 37) bRows 111) (b2Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row38 :
    digitsEq 111 (rowProduct (bRows 38) bRows 111) (b2Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row39 :
    digitsEq 111 (rowProduct (bRows 39) bRows 111) (b2Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row40 :
    digitsEq 111 (rowProduct (bRows 40) bRows 111) (b2Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row41 :
    digitsEq 111 (rowProduct (bRows 41) bRows 111) (b2Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row42 :
    digitsEq 111 (rowProduct (bRows 42) bRows 111) (b2Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row43 :
    digitsEq 111 (rowProduct (bRows 43) bRows 111) (b2Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row44 :
    digitsEq 111 (rowProduct (bRows 44) bRows 111) (b2Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row45 :
    digitsEq 111 (rowProduct (bRows 45) bRows 111) (b2Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row46 :
    digitsEq 111 (rowProduct (bRows 46) bRows 111) (b2Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row47 :
    digitsEq 111 (rowProduct (bRows 47) bRows 111) (b2Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row48 :
    digitsEq 111 (rowProduct (bRows 48) bRows 111) (b2Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row49 :
    digitsEq 111 (rowProduct (bRows 49) bRows 111) (b2Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row50 :
    digitsEq 111 (rowProduct (bRows 50) bRows 111) (b2Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row51 :
    digitsEq 111 (rowProduct (bRows 51) bRows 111) (b2Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row52 :
    digitsEq 111 (rowProduct (bRows 52) bRows 111) (b2Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row53 :
    digitsEq 111 (rowProduct (bRows 53) bRows 111) (b2Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row54 :
    digitsEq 111 (rowProduct (bRows 54) bRows 111) (b2Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row55 :
    digitsEq 111 (rowProduct (bRows 55) bRows 111) (b2Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row56 :
    digitsEq 111 (rowProduct (bRows 56) bRows 111) (b2Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row57 :
    digitsEq 111 (rowProduct (bRows 57) bRows 111) (b2Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row58 :
    digitsEq 111 (rowProduct (bRows 58) bRows 111) (b2Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row59 :
    digitsEq 111 (rowProduct (bRows 59) bRows 111) (b2Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row60 :
    digitsEq 111 (rowProduct (bRows 60) bRows 111) (b2Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row61 :
    digitsEq 111 (rowProduct (bRows 61) bRows 111) (b2Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row62 :
    digitsEq 111 (rowProduct (bRows 62) bRows 111) (b2Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row63 :
    digitsEq 111 (rowProduct (bRows 63) bRows 111) (b2Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row64 :
    digitsEq 111 (rowProduct (bRows 64) bRows 111) (b2Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row65 :
    digitsEq 111 (rowProduct (bRows 65) bRows 111) (b2Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row66 :
    digitsEq 111 (rowProduct (bRows 66) bRows 111) (b2Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row67 :
    digitsEq 111 (rowProduct (bRows 67) bRows 111) (b2Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row68 :
    digitsEq 111 (rowProduct (bRows 68) bRows 111) (b2Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row69 :
    digitsEq 111 (rowProduct (bRows 69) bRows 111) (b2Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row70 :
    digitsEq 111 (rowProduct (bRows 70) bRows 111) (b2Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row71 :
    digitsEq 111 (rowProduct (bRows 71) bRows 111) (b2Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row72 :
    digitsEq 111 (rowProduct (bRows 72) bRows 111) (b2Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row73 :
    digitsEq 111 (rowProduct (bRows 73) bRows 111) (b2Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row74 :
    digitsEq 111 (rowProduct (bRows 74) bRows 111) (b2Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row75 :
    digitsEq 111 (rowProduct (bRows 75) bRows 111) (b2Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row76 :
    digitsEq 111 (rowProduct (bRows 76) bRows 111) (b2Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row77 :
    digitsEq 111 (rowProduct (bRows 77) bRows 111) (b2Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row78 :
    digitsEq 111 (rowProduct (bRows 78) bRows 111) (b2Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row79 :
    digitsEq 111 (rowProduct (bRows 79) bRows 111) (b2Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row80 :
    digitsEq 111 (rowProduct (bRows 80) bRows 111) (b2Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row81 :
    digitsEq 111 (rowProduct (bRows 81) bRows 111) (b2Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row82 :
    digitsEq 111 (rowProduct (bRows 82) bRows 111) (b2Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row83 :
    digitsEq 111 (rowProduct (bRows 83) bRows 111) (b2Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row84 :
    digitsEq 111 (rowProduct (bRows 84) bRows 111) (b2Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row85 :
    digitsEq 111 (rowProduct (bRows 85) bRows 111) (b2Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row86 :
    digitsEq 111 (rowProduct (bRows 86) bRows 111) (b2Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row87 :
    digitsEq 111 (rowProduct (bRows 87) bRows 111) (b2Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row88 :
    digitsEq 111 (rowProduct (bRows 88) bRows 111) (b2Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row89 :
    digitsEq 111 (rowProduct (bRows 89) bRows 111) (b2Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row90 :
    digitsEq 111 (rowProduct (bRows 90) bRows 111) (b2Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row91 :
    digitsEq 111 (rowProduct (bRows 91) bRows 111) (b2Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row92 :
    digitsEq 111 (rowProduct (bRows 92) bRows 111) (b2Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row93 :
    digitsEq 111 (rowProduct (bRows 93) bRows 111) (b2Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row94 :
    digitsEq 111 (rowProduct (bRows 94) bRows 111) (b2Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row95 :
    digitsEq 111 (rowProduct (bRows 95) bRows 111) (b2Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row96 :
    digitsEq 111 (rowProduct (bRows 96) bRows 111) (b2Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row97 :
    digitsEq 111 (rowProduct (bRows 97) bRows 111) (b2Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row98 :
    digitsEq 111 (rowProduct (bRows 98) bRows 111) (b2Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row99 :
    digitsEq 111 (rowProduct (bRows 99) bRows 111) (b2Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row100 :
    digitsEq 111 (rowProduct (bRows 100) bRows 111) (b2Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row101 :
    digitsEq 111 (rowProduct (bRows 101) bRows 111) (b2Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row102 :
    digitsEq 111 (rowProduct (bRows 102) bRows 111) (b2Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row103 :
    digitsEq 111 (rowProduct (bRows 103) bRows 111) (b2Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row104 :
    digitsEq 111 (rowProduct (bRows 104) bRows 111) (b2Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row105 :
    digitsEq 111 (rowProduct (bRows 105) bRows 111) (b2Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row106 :
    digitsEq 111 (rowProduct (bRows 106) bRows 111) (b2Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row107 :
    digitsEq 111 (rowProduct (bRows 107) bRows 111) (b2Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row108 :
    digitsEq 111 (rowProduct (bRows 108) bRows 111) (b2Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row109 :
    digitsEq 111 (rowProduct (bRows 109) bRows 111) (b2Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b2_row110 :
    digitsEq 111 (rowProduct (bRows 110) bRows 111) (b2Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem b2_rows : ∀ i,
    digitsEq 111 (rowProduct (bRows i) bRows 111) (b2Rows i) = true :=
  (Fin.cases b2_row0
    (Fin.cases b2_row1
    (Fin.cases b2_row2
    (Fin.cases b2_row3
    (Fin.cases b2_row4
    (Fin.cases b2_row5
    (Fin.cases b2_row6
    (Fin.cases b2_row7
    (Fin.cases b2_row8
    (Fin.cases b2_row9
    (Fin.cases b2_row10
    (Fin.cases b2_row11
    (Fin.cases b2_row12
    (Fin.cases b2_row13
    (Fin.cases b2_row14
    (Fin.cases b2_row15
    (Fin.cases b2_row16
    (Fin.cases b2_row17
    (Fin.cases b2_row18
    (Fin.cases b2_row19
    (Fin.cases b2_row20
    (Fin.cases b2_row21
    (Fin.cases b2_row22
    (Fin.cases b2_row23
    (Fin.cases b2_row24
    (Fin.cases b2_row25
    (Fin.cases b2_row26
    (Fin.cases b2_row27
    (Fin.cases b2_row28
    (Fin.cases b2_row29
    (Fin.cases b2_row30
    (Fin.cases b2_row31
    (Fin.cases b2_row32
    (Fin.cases b2_row33
    (Fin.cases b2_row34
    (Fin.cases b2_row35
    (Fin.cases b2_row36
    (Fin.cases b2_row37
    (Fin.cases b2_row38
    (Fin.cases b2_row39
    (Fin.cases b2_row40
    (Fin.cases b2_row41
    (Fin.cases b2_row42
    (Fin.cases b2_row43
    (Fin.cases b2_row44
    (Fin.cases b2_row45
    (Fin.cases b2_row46
    (Fin.cases b2_row47
    (Fin.cases b2_row48
    (Fin.cases b2_row49
    (Fin.cases b2_row50
    (Fin.cases b2_row51
    (Fin.cases b2_row52
    (Fin.cases b2_row53
    (Fin.cases b2_row54
    (Fin.cases b2_row55
    (Fin.cases b2_row56
    (Fin.cases b2_row57
    (Fin.cases b2_row58
    (Fin.cases b2_row59
    (Fin.cases b2_row60
    (Fin.cases b2_row61
    (Fin.cases b2_row62
    (Fin.cases b2_row63
    (Fin.cases b2_row64
    (Fin.cases b2_row65
    (Fin.cases b2_row66
    (Fin.cases b2_row67
    (Fin.cases b2_row68
    (Fin.cases b2_row69
    (Fin.cases b2_row70
    (Fin.cases b2_row71
    (Fin.cases b2_row72
    (Fin.cases b2_row73
    (Fin.cases b2_row74
    (Fin.cases b2_row75
    (Fin.cases b2_row76
    (Fin.cases b2_row77
    (Fin.cases b2_row78
    (Fin.cases b2_row79
    (Fin.cases b2_row80
    (Fin.cases b2_row81
    (Fin.cases b2_row82
    (Fin.cases b2_row83
    (Fin.cases b2_row84
    (Fin.cases b2_row85
    (Fin.cases b2_row86
    (Fin.cases b2_row87
    (Fin.cases b2_row88
    (Fin.cases b2_row89
    (Fin.cases b2_row90
    (Fin.cases b2_row91
    (Fin.cases b2_row92
    (Fin.cases b2_row93
    (Fin.cases b2_row94
    (Fin.cases b2_row95
    (Fin.cases b2_row96
    (Fin.cases b2_row97
    (Fin.cases b2_row98
    (Fin.cases b2_row99
    (Fin.cases b2_row100
    (Fin.cases b2_row101
    (Fin.cases b2_row102
    (Fin.cases b2_row103
    (Fin.cases b2_row104
    (Fin.cases b2_row105
    (Fin.cases b2_row106
    (Fin.cases b2_row107
    (Fin.cases b2_row108
    (Fin.cases b2_row109
    (Fin.cases b2_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_b2 : bMatrix * bMatrix = b2Matrix :=
  decode_mul _ _ _ b_small b_small b2_rows

end Lyons.Atlas111WordCertificate
