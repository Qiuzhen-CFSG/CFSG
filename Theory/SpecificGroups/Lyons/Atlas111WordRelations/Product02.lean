module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: b4 times b

These 111 row checks certify `b4Matrix * bMatrix = oneMatrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row0 :
    digitsEq 111 (rowProduct (b4Rows 0) bRows 111) (oneRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row1 :
    digitsEq 111 (rowProduct (b4Rows 1) bRows 111) (oneRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row2 :
    digitsEq 111 (rowProduct (b4Rows 2) bRows 111) (oneRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row3 :
    digitsEq 111 (rowProduct (b4Rows 3) bRows 111) (oneRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row4 :
    digitsEq 111 (rowProduct (b4Rows 4) bRows 111) (oneRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row5 :
    digitsEq 111 (rowProduct (b4Rows 5) bRows 111) (oneRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row6 :
    digitsEq 111 (rowProduct (b4Rows 6) bRows 111) (oneRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row7 :
    digitsEq 111 (rowProduct (b4Rows 7) bRows 111) (oneRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row8 :
    digitsEq 111 (rowProduct (b4Rows 8) bRows 111) (oneRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row9 :
    digitsEq 111 (rowProduct (b4Rows 9) bRows 111) (oneRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row10 :
    digitsEq 111 (rowProduct (b4Rows 10) bRows 111) (oneRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row11 :
    digitsEq 111 (rowProduct (b4Rows 11) bRows 111) (oneRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row12 :
    digitsEq 111 (rowProduct (b4Rows 12) bRows 111) (oneRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row13 :
    digitsEq 111 (rowProduct (b4Rows 13) bRows 111) (oneRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row14 :
    digitsEq 111 (rowProduct (b4Rows 14) bRows 111) (oneRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row15 :
    digitsEq 111 (rowProduct (b4Rows 15) bRows 111) (oneRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row16 :
    digitsEq 111 (rowProduct (b4Rows 16) bRows 111) (oneRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row17 :
    digitsEq 111 (rowProduct (b4Rows 17) bRows 111) (oneRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row18 :
    digitsEq 111 (rowProduct (b4Rows 18) bRows 111) (oneRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row19 :
    digitsEq 111 (rowProduct (b4Rows 19) bRows 111) (oneRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row20 :
    digitsEq 111 (rowProduct (b4Rows 20) bRows 111) (oneRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row21 :
    digitsEq 111 (rowProduct (b4Rows 21) bRows 111) (oneRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row22 :
    digitsEq 111 (rowProduct (b4Rows 22) bRows 111) (oneRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row23 :
    digitsEq 111 (rowProduct (b4Rows 23) bRows 111) (oneRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row24 :
    digitsEq 111 (rowProduct (b4Rows 24) bRows 111) (oneRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row25 :
    digitsEq 111 (rowProduct (b4Rows 25) bRows 111) (oneRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row26 :
    digitsEq 111 (rowProduct (b4Rows 26) bRows 111) (oneRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row27 :
    digitsEq 111 (rowProduct (b4Rows 27) bRows 111) (oneRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row28 :
    digitsEq 111 (rowProduct (b4Rows 28) bRows 111) (oneRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row29 :
    digitsEq 111 (rowProduct (b4Rows 29) bRows 111) (oneRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row30 :
    digitsEq 111 (rowProduct (b4Rows 30) bRows 111) (oneRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row31 :
    digitsEq 111 (rowProduct (b4Rows 31) bRows 111) (oneRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row32 :
    digitsEq 111 (rowProduct (b4Rows 32) bRows 111) (oneRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row33 :
    digitsEq 111 (rowProduct (b4Rows 33) bRows 111) (oneRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row34 :
    digitsEq 111 (rowProduct (b4Rows 34) bRows 111) (oneRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row35 :
    digitsEq 111 (rowProduct (b4Rows 35) bRows 111) (oneRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row36 :
    digitsEq 111 (rowProduct (b4Rows 36) bRows 111) (oneRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row37 :
    digitsEq 111 (rowProduct (b4Rows 37) bRows 111) (oneRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row38 :
    digitsEq 111 (rowProduct (b4Rows 38) bRows 111) (oneRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row39 :
    digitsEq 111 (rowProduct (b4Rows 39) bRows 111) (oneRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row40 :
    digitsEq 111 (rowProduct (b4Rows 40) bRows 111) (oneRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row41 :
    digitsEq 111 (rowProduct (b4Rows 41) bRows 111) (oneRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row42 :
    digitsEq 111 (rowProduct (b4Rows 42) bRows 111) (oneRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row43 :
    digitsEq 111 (rowProduct (b4Rows 43) bRows 111) (oneRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row44 :
    digitsEq 111 (rowProduct (b4Rows 44) bRows 111) (oneRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row45 :
    digitsEq 111 (rowProduct (b4Rows 45) bRows 111) (oneRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row46 :
    digitsEq 111 (rowProduct (b4Rows 46) bRows 111) (oneRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row47 :
    digitsEq 111 (rowProduct (b4Rows 47) bRows 111) (oneRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row48 :
    digitsEq 111 (rowProduct (b4Rows 48) bRows 111) (oneRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row49 :
    digitsEq 111 (rowProduct (b4Rows 49) bRows 111) (oneRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row50 :
    digitsEq 111 (rowProduct (b4Rows 50) bRows 111) (oneRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row51 :
    digitsEq 111 (rowProduct (b4Rows 51) bRows 111) (oneRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row52 :
    digitsEq 111 (rowProduct (b4Rows 52) bRows 111) (oneRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row53 :
    digitsEq 111 (rowProduct (b4Rows 53) bRows 111) (oneRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row54 :
    digitsEq 111 (rowProduct (b4Rows 54) bRows 111) (oneRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row55 :
    digitsEq 111 (rowProduct (b4Rows 55) bRows 111) (oneRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row56 :
    digitsEq 111 (rowProduct (b4Rows 56) bRows 111) (oneRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row57 :
    digitsEq 111 (rowProduct (b4Rows 57) bRows 111) (oneRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row58 :
    digitsEq 111 (rowProduct (b4Rows 58) bRows 111) (oneRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row59 :
    digitsEq 111 (rowProduct (b4Rows 59) bRows 111) (oneRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row60 :
    digitsEq 111 (rowProduct (b4Rows 60) bRows 111) (oneRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row61 :
    digitsEq 111 (rowProduct (b4Rows 61) bRows 111) (oneRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row62 :
    digitsEq 111 (rowProduct (b4Rows 62) bRows 111) (oneRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row63 :
    digitsEq 111 (rowProduct (b4Rows 63) bRows 111) (oneRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row64 :
    digitsEq 111 (rowProduct (b4Rows 64) bRows 111) (oneRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row65 :
    digitsEq 111 (rowProduct (b4Rows 65) bRows 111) (oneRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row66 :
    digitsEq 111 (rowProduct (b4Rows 66) bRows 111) (oneRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row67 :
    digitsEq 111 (rowProduct (b4Rows 67) bRows 111) (oneRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row68 :
    digitsEq 111 (rowProduct (b4Rows 68) bRows 111) (oneRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row69 :
    digitsEq 111 (rowProduct (b4Rows 69) bRows 111) (oneRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row70 :
    digitsEq 111 (rowProduct (b4Rows 70) bRows 111) (oneRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row71 :
    digitsEq 111 (rowProduct (b4Rows 71) bRows 111) (oneRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row72 :
    digitsEq 111 (rowProduct (b4Rows 72) bRows 111) (oneRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row73 :
    digitsEq 111 (rowProduct (b4Rows 73) bRows 111) (oneRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row74 :
    digitsEq 111 (rowProduct (b4Rows 74) bRows 111) (oneRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row75 :
    digitsEq 111 (rowProduct (b4Rows 75) bRows 111) (oneRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row76 :
    digitsEq 111 (rowProduct (b4Rows 76) bRows 111) (oneRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row77 :
    digitsEq 111 (rowProduct (b4Rows 77) bRows 111) (oneRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row78 :
    digitsEq 111 (rowProduct (b4Rows 78) bRows 111) (oneRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row79 :
    digitsEq 111 (rowProduct (b4Rows 79) bRows 111) (oneRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row80 :
    digitsEq 111 (rowProduct (b4Rows 80) bRows 111) (oneRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row81 :
    digitsEq 111 (rowProduct (b4Rows 81) bRows 111) (oneRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row82 :
    digitsEq 111 (rowProduct (b4Rows 82) bRows 111) (oneRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row83 :
    digitsEq 111 (rowProduct (b4Rows 83) bRows 111) (oneRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row84 :
    digitsEq 111 (rowProduct (b4Rows 84) bRows 111) (oneRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row85 :
    digitsEq 111 (rowProduct (b4Rows 85) bRows 111) (oneRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row86 :
    digitsEq 111 (rowProduct (b4Rows 86) bRows 111) (oneRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row87 :
    digitsEq 111 (rowProduct (b4Rows 87) bRows 111) (oneRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row88 :
    digitsEq 111 (rowProduct (b4Rows 88) bRows 111) (oneRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row89 :
    digitsEq 111 (rowProduct (b4Rows 89) bRows 111) (oneRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row90 :
    digitsEq 111 (rowProduct (b4Rows 90) bRows 111) (oneRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row91 :
    digitsEq 111 (rowProduct (b4Rows 91) bRows 111) (oneRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row92 :
    digitsEq 111 (rowProduct (b4Rows 92) bRows 111) (oneRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row93 :
    digitsEq 111 (rowProduct (b4Rows 93) bRows 111) (oneRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row94 :
    digitsEq 111 (rowProduct (b4Rows 94) bRows 111) (oneRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row95 :
    digitsEq 111 (rowProduct (b4Rows 95) bRows 111) (oneRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row96 :
    digitsEq 111 (rowProduct (b4Rows 96) bRows 111) (oneRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row97 :
    digitsEq 111 (rowProduct (b4Rows 97) bRows 111) (oneRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row98 :
    digitsEq 111 (rowProduct (b4Rows 98) bRows 111) (oneRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row99 :
    digitsEq 111 (rowProduct (b4Rows 99) bRows 111) (oneRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row100 :
    digitsEq 111 (rowProduct (b4Rows 100) bRows 111) (oneRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row101 :
    digitsEq 111 (rowProduct (b4Rows 101) bRows 111) (oneRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row102 :
    digitsEq 111 (rowProduct (b4Rows 102) bRows 111) (oneRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row103 :
    digitsEq 111 (rowProduct (b4Rows 103) bRows 111) (oneRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row104 :
    digitsEq 111 (rowProduct (b4Rows 104) bRows 111) (oneRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row105 :
    digitsEq 111 (rowProduct (b4Rows 105) bRows 111) (oneRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row106 :
    digitsEq 111 (rowProduct (b4Rows 106) bRows 111) (oneRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row107 :
    digitsEq 111 (rowProduct (b4Rows 107) bRows 111) (oneRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row108 :
    digitsEq 111 (rowProduct (b4Rows 108) bRows 111) (oneRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row109 :
    digitsEq 111 (rowProduct (b4Rows 109) bRows 111) (oneRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem b5_row110 :
    digitsEq 111 (rowProduct (b4Rows 110) bRows 111) (oneRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem b5_rows : ∀ i,
    digitsEq 111 (rowProduct (b4Rows i) bRows 111) (oneRows i) = true :=
  (Fin.cases b5_row0
    (Fin.cases b5_row1
    (Fin.cases b5_row2
    (Fin.cases b5_row3
    (Fin.cases b5_row4
    (Fin.cases b5_row5
    (Fin.cases b5_row6
    (Fin.cases b5_row7
    (Fin.cases b5_row8
    (Fin.cases b5_row9
    (Fin.cases b5_row10
    (Fin.cases b5_row11
    (Fin.cases b5_row12
    (Fin.cases b5_row13
    (Fin.cases b5_row14
    (Fin.cases b5_row15
    (Fin.cases b5_row16
    (Fin.cases b5_row17
    (Fin.cases b5_row18
    (Fin.cases b5_row19
    (Fin.cases b5_row20
    (Fin.cases b5_row21
    (Fin.cases b5_row22
    (Fin.cases b5_row23
    (Fin.cases b5_row24
    (Fin.cases b5_row25
    (Fin.cases b5_row26
    (Fin.cases b5_row27
    (Fin.cases b5_row28
    (Fin.cases b5_row29
    (Fin.cases b5_row30
    (Fin.cases b5_row31
    (Fin.cases b5_row32
    (Fin.cases b5_row33
    (Fin.cases b5_row34
    (Fin.cases b5_row35
    (Fin.cases b5_row36
    (Fin.cases b5_row37
    (Fin.cases b5_row38
    (Fin.cases b5_row39
    (Fin.cases b5_row40
    (Fin.cases b5_row41
    (Fin.cases b5_row42
    (Fin.cases b5_row43
    (Fin.cases b5_row44
    (Fin.cases b5_row45
    (Fin.cases b5_row46
    (Fin.cases b5_row47
    (Fin.cases b5_row48
    (Fin.cases b5_row49
    (Fin.cases b5_row50
    (Fin.cases b5_row51
    (Fin.cases b5_row52
    (Fin.cases b5_row53
    (Fin.cases b5_row54
    (Fin.cases b5_row55
    (Fin.cases b5_row56
    (Fin.cases b5_row57
    (Fin.cases b5_row58
    (Fin.cases b5_row59
    (Fin.cases b5_row60
    (Fin.cases b5_row61
    (Fin.cases b5_row62
    (Fin.cases b5_row63
    (Fin.cases b5_row64
    (Fin.cases b5_row65
    (Fin.cases b5_row66
    (Fin.cases b5_row67
    (Fin.cases b5_row68
    (Fin.cases b5_row69
    (Fin.cases b5_row70
    (Fin.cases b5_row71
    (Fin.cases b5_row72
    (Fin.cases b5_row73
    (Fin.cases b5_row74
    (Fin.cases b5_row75
    (Fin.cases b5_row76
    (Fin.cases b5_row77
    (Fin.cases b5_row78
    (Fin.cases b5_row79
    (Fin.cases b5_row80
    (Fin.cases b5_row81
    (Fin.cases b5_row82
    (Fin.cases b5_row83
    (Fin.cases b5_row84
    (Fin.cases b5_row85
    (Fin.cases b5_row86
    (Fin.cases b5_row87
    (Fin.cases b5_row88
    (Fin.cases b5_row89
    (Fin.cases b5_row90
    (Fin.cases b5_row91
    (Fin.cases b5_row92
    (Fin.cases b5_row93
    (Fin.cases b5_row94
    (Fin.cases b5_row95
    (Fin.cases b5_row96
    (Fin.cases b5_row97
    (Fin.cases b5_row98
    (Fin.cases b5_row99
    (Fin.cases b5_row100
    (Fin.cases b5_row101
    (Fin.cases b5_row102
    (Fin.cases b5_row103
    (Fin.cases b5_row104
    (Fin.cases b5_row105
    (Fin.cases b5_row106
    (Fin.cases b5_row107
    (Fin.cases b5_row108
    (Fin.cases b5_row109
    (Fin.cases b5_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_b5 : b4Matrix * bMatrix = oneMatrix :=
  decode_mul _ _ _ b4_small b_small b5_rows

end Lyons.Atlas111WordCertificate
