module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: a times b

These 111 row checks certify `aMatrix * bMatrix = abMatrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row0 :
    digitsEq 111 (rowProduct (aRows 0) bRows 111) (abRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row1 :
    digitsEq 111 (rowProduct (aRows 1) bRows 111) (abRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row2 :
    digitsEq 111 (rowProduct (aRows 2) bRows 111) (abRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row3 :
    digitsEq 111 (rowProduct (aRows 3) bRows 111) (abRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row4 :
    digitsEq 111 (rowProduct (aRows 4) bRows 111) (abRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row5 :
    digitsEq 111 (rowProduct (aRows 5) bRows 111) (abRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row6 :
    digitsEq 111 (rowProduct (aRows 6) bRows 111) (abRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row7 :
    digitsEq 111 (rowProduct (aRows 7) bRows 111) (abRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row8 :
    digitsEq 111 (rowProduct (aRows 8) bRows 111) (abRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row9 :
    digitsEq 111 (rowProduct (aRows 9) bRows 111) (abRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row10 :
    digitsEq 111 (rowProduct (aRows 10) bRows 111) (abRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row11 :
    digitsEq 111 (rowProduct (aRows 11) bRows 111) (abRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row12 :
    digitsEq 111 (rowProduct (aRows 12) bRows 111) (abRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row13 :
    digitsEq 111 (rowProduct (aRows 13) bRows 111) (abRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row14 :
    digitsEq 111 (rowProduct (aRows 14) bRows 111) (abRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row15 :
    digitsEq 111 (rowProduct (aRows 15) bRows 111) (abRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row16 :
    digitsEq 111 (rowProduct (aRows 16) bRows 111) (abRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row17 :
    digitsEq 111 (rowProduct (aRows 17) bRows 111) (abRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row18 :
    digitsEq 111 (rowProduct (aRows 18) bRows 111) (abRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row19 :
    digitsEq 111 (rowProduct (aRows 19) bRows 111) (abRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row20 :
    digitsEq 111 (rowProduct (aRows 20) bRows 111) (abRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row21 :
    digitsEq 111 (rowProduct (aRows 21) bRows 111) (abRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row22 :
    digitsEq 111 (rowProduct (aRows 22) bRows 111) (abRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row23 :
    digitsEq 111 (rowProduct (aRows 23) bRows 111) (abRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row24 :
    digitsEq 111 (rowProduct (aRows 24) bRows 111) (abRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row25 :
    digitsEq 111 (rowProduct (aRows 25) bRows 111) (abRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row26 :
    digitsEq 111 (rowProduct (aRows 26) bRows 111) (abRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row27 :
    digitsEq 111 (rowProduct (aRows 27) bRows 111) (abRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row28 :
    digitsEq 111 (rowProduct (aRows 28) bRows 111) (abRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row29 :
    digitsEq 111 (rowProduct (aRows 29) bRows 111) (abRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row30 :
    digitsEq 111 (rowProduct (aRows 30) bRows 111) (abRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row31 :
    digitsEq 111 (rowProduct (aRows 31) bRows 111) (abRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row32 :
    digitsEq 111 (rowProduct (aRows 32) bRows 111) (abRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row33 :
    digitsEq 111 (rowProduct (aRows 33) bRows 111) (abRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row34 :
    digitsEq 111 (rowProduct (aRows 34) bRows 111) (abRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row35 :
    digitsEq 111 (rowProduct (aRows 35) bRows 111) (abRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row36 :
    digitsEq 111 (rowProduct (aRows 36) bRows 111) (abRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row37 :
    digitsEq 111 (rowProduct (aRows 37) bRows 111) (abRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row38 :
    digitsEq 111 (rowProduct (aRows 38) bRows 111) (abRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row39 :
    digitsEq 111 (rowProduct (aRows 39) bRows 111) (abRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row40 :
    digitsEq 111 (rowProduct (aRows 40) bRows 111) (abRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row41 :
    digitsEq 111 (rowProduct (aRows 41) bRows 111) (abRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row42 :
    digitsEq 111 (rowProduct (aRows 42) bRows 111) (abRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row43 :
    digitsEq 111 (rowProduct (aRows 43) bRows 111) (abRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row44 :
    digitsEq 111 (rowProduct (aRows 44) bRows 111) (abRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row45 :
    digitsEq 111 (rowProduct (aRows 45) bRows 111) (abRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row46 :
    digitsEq 111 (rowProduct (aRows 46) bRows 111) (abRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row47 :
    digitsEq 111 (rowProduct (aRows 47) bRows 111) (abRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row48 :
    digitsEq 111 (rowProduct (aRows 48) bRows 111) (abRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row49 :
    digitsEq 111 (rowProduct (aRows 49) bRows 111) (abRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row50 :
    digitsEq 111 (rowProduct (aRows 50) bRows 111) (abRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row51 :
    digitsEq 111 (rowProduct (aRows 51) bRows 111) (abRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row52 :
    digitsEq 111 (rowProduct (aRows 52) bRows 111) (abRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row53 :
    digitsEq 111 (rowProduct (aRows 53) bRows 111) (abRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row54 :
    digitsEq 111 (rowProduct (aRows 54) bRows 111) (abRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row55 :
    digitsEq 111 (rowProduct (aRows 55) bRows 111) (abRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row56 :
    digitsEq 111 (rowProduct (aRows 56) bRows 111) (abRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row57 :
    digitsEq 111 (rowProduct (aRows 57) bRows 111) (abRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row58 :
    digitsEq 111 (rowProduct (aRows 58) bRows 111) (abRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row59 :
    digitsEq 111 (rowProduct (aRows 59) bRows 111) (abRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row60 :
    digitsEq 111 (rowProduct (aRows 60) bRows 111) (abRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row61 :
    digitsEq 111 (rowProduct (aRows 61) bRows 111) (abRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row62 :
    digitsEq 111 (rowProduct (aRows 62) bRows 111) (abRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row63 :
    digitsEq 111 (rowProduct (aRows 63) bRows 111) (abRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row64 :
    digitsEq 111 (rowProduct (aRows 64) bRows 111) (abRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row65 :
    digitsEq 111 (rowProduct (aRows 65) bRows 111) (abRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row66 :
    digitsEq 111 (rowProduct (aRows 66) bRows 111) (abRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row67 :
    digitsEq 111 (rowProduct (aRows 67) bRows 111) (abRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row68 :
    digitsEq 111 (rowProduct (aRows 68) bRows 111) (abRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row69 :
    digitsEq 111 (rowProduct (aRows 69) bRows 111) (abRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row70 :
    digitsEq 111 (rowProduct (aRows 70) bRows 111) (abRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row71 :
    digitsEq 111 (rowProduct (aRows 71) bRows 111) (abRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row72 :
    digitsEq 111 (rowProduct (aRows 72) bRows 111) (abRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row73 :
    digitsEq 111 (rowProduct (aRows 73) bRows 111) (abRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row74 :
    digitsEq 111 (rowProduct (aRows 74) bRows 111) (abRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row75 :
    digitsEq 111 (rowProduct (aRows 75) bRows 111) (abRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row76 :
    digitsEq 111 (rowProduct (aRows 76) bRows 111) (abRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row77 :
    digitsEq 111 (rowProduct (aRows 77) bRows 111) (abRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row78 :
    digitsEq 111 (rowProduct (aRows 78) bRows 111) (abRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row79 :
    digitsEq 111 (rowProduct (aRows 79) bRows 111) (abRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row80 :
    digitsEq 111 (rowProduct (aRows 80) bRows 111) (abRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row81 :
    digitsEq 111 (rowProduct (aRows 81) bRows 111) (abRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row82 :
    digitsEq 111 (rowProduct (aRows 82) bRows 111) (abRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row83 :
    digitsEq 111 (rowProduct (aRows 83) bRows 111) (abRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row84 :
    digitsEq 111 (rowProduct (aRows 84) bRows 111) (abRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row85 :
    digitsEq 111 (rowProduct (aRows 85) bRows 111) (abRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row86 :
    digitsEq 111 (rowProduct (aRows 86) bRows 111) (abRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row87 :
    digitsEq 111 (rowProduct (aRows 87) bRows 111) (abRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row88 :
    digitsEq 111 (rowProduct (aRows 88) bRows 111) (abRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row89 :
    digitsEq 111 (rowProduct (aRows 89) bRows 111) (abRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row90 :
    digitsEq 111 (rowProduct (aRows 90) bRows 111) (abRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row91 :
    digitsEq 111 (rowProduct (aRows 91) bRows 111) (abRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row92 :
    digitsEq 111 (rowProduct (aRows 92) bRows 111) (abRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row93 :
    digitsEq 111 (rowProduct (aRows 93) bRows 111) (abRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row94 :
    digitsEq 111 (rowProduct (aRows 94) bRows 111) (abRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row95 :
    digitsEq 111 (rowProduct (aRows 95) bRows 111) (abRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row96 :
    digitsEq 111 (rowProduct (aRows 96) bRows 111) (abRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row97 :
    digitsEq 111 (rowProduct (aRows 97) bRows 111) (abRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row98 :
    digitsEq 111 (rowProduct (aRows 98) bRows 111) (abRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row99 :
    digitsEq 111 (rowProduct (aRows 99) bRows 111) (abRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row100 :
    digitsEq 111 (rowProduct (aRows 100) bRows 111) (abRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row101 :
    digitsEq 111 (rowProduct (aRows 101) bRows 111) (abRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row102 :
    digitsEq 111 (rowProduct (aRows 102) bRows 111) (abRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row103 :
    digitsEq 111 (rowProduct (aRows 103) bRows 111) (abRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row104 :
    digitsEq 111 (rowProduct (aRows 104) bRows 111) (abRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row105 :
    digitsEq 111 (rowProduct (aRows 105) bRows 111) (abRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row106 :
    digitsEq 111 (rowProduct (aRows 106) bRows 111) (abRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row107 :
    digitsEq 111 (rowProduct (aRows 107) bRows 111) (abRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row108 :
    digitsEq 111 (rowProduct (aRows 108) bRows 111) (abRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row109 :
    digitsEq 111 (rowProduct (aRows 109) bRows 111) (abRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab_row110 :
    digitsEq 111 (rowProduct (aRows 110) bRows 111) (abRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem ab_rows : ∀ i,
    digitsEq 111 (rowProduct (aRows i) bRows 111) (abRows i) = true :=
  (Fin.cases ab_row0
    (Fin.cases ab_row1
    (Fin.cases ab_row2
    (Fin.cases ab_row3
    (Fin.cases ab_row4
    (Fin.cases ab_row5
    (Fin.cases ab_row6
    (Fin.cases ab_row7
    (Fin.cases ab_row8
    (Fin.cases ab_row9
    (Fin.cases ab_row10
    (Fin.cases ab_row11
    (Fin.cases ab_row12
    (Fin.cases ab_row13
    (Fin.cases ab_row14
    (Fin.cases ab_row15
    (Fin.cases ab_row16
    (Fin.cases ab_row17
    (Fin.cases ab_row18
    (Fin.cases ab_row19
    (Fin.cases ab_row20
    (Fin.cases ab_row21
    (Fin.cases ab_row22
    (Fin.cases ab_row23
    (Fin.cases ab_row24
    (Fin.cases ab_row25
    (Fin.cases ab_row26
    (Fin.cases ab_row27
    (Fin.cases ab_row28
    (Fin.cases ab_row29
    (Fin.cases ab_row30
    (Fin.cases ab_row31
    (Fin.cases ab_row32
    (Fin.cases ab_row33
    (Fin.cases ab_row34
    (Fin.cases ab_row35
    (Fin.cases ab_row36
    (Fin.cases ab_row37
    (Fin.cases ab_row38
    (Fin.cases ab_row39
    (Fin.cases ab_row40
    (Fin.cases ab_row41
    (Fin.cases ab_row42
    (Fin.cases ab_row43
    (Fin.cases ab_row44
    (Fin.cases ab_row45
    (Fin.cases ab_row46
    (Fin.cases ab_row47
    (Fin.cases ab_row48
    (Fin.cases ab_row49
    (Fin.cases ab_row50
    (Fin.cases ab_row51
    (Fin.cases ab_row52
    (Fin.cases ab_row53
    (Fin.cases ab_row54
    (Fin.cases ab_row55
    (Fin.cases ab_row56
    (Fin.cases ab_row57
    (Fin.cases ab_row58
    (Fin.cases ab_row59
    (Fin.cases ab_row60
    (Fin.cases ab_row61
    (Fin.cases ab_row62
    (Fin.cases ab_row63
    (Fin.cases ab_row64
    (Fin.cases ab_row65
    (Fin.cases ab_row66
    (Fin.cases ab_row67
    (Fin.cases ab_row68
    (Fin.cases ab_row69
    (Fin.cases ab_row70
    (Fin.cases ab_row71
    (Fin.cases ab_row72
    (Fin.cases ab_row73
    (Fin.cases ab_row74
    (Fin.cases ab_row75
    (Fin.cases ab_row76
    (Fin.cases ab_row77
    (Fin.cases ab_row78
    (Fin.cases ab_row79
    (Fin.cases ab_row80
    (Fin.cases ab_row81
    (Fin.cases ab_row82
    (Fin.cases ab_row83
    (Fin.cases ab_row84
    (Fin.cases ab_row85
    (Fin.cases ab_row86
    (Fin.cases ab_row87
    (Fin.cases ab_row88
    (Fin.cases ab_row89
    (Fin.cases ab_row90
    (Fin.cases ab_row91
    (Fin.cases ab_row92
    (Fin.cases ab_row93
    (Fin.cases ab_row94
    (Fin.cases ab_row95
    (Fin.cases ab_row96
    (Fin.cases ab_row97
    (Fin.cases ab_row98
    (Fin.cases ab_row99
    (Fin.cases ab_row100
    (Fin.cases ab_row101
    (Fin.cases ab_row102
    (Fin.cases ab_row103
    (Fin.cases ab_row104
    (Fin.cases ab_row105
    (Fin.cases ab_row106
    (Fin.cases ab_row107
    (Fin.cases ab_row108
    (Fin.cases ab_row109
    (Fin.cases ab_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_ab : aMatrix * bMatrix = abMatrix :=
  decode_mul _ _ _ a_small b_small ab_rows

end Lyons.Atlas111WordCertificate
