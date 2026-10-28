module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: ab3 times b

These 111 row checks certify `ab3Matrix * bMatrix = wMatrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row0 :
    digitsEq 111 (rowProduct (ab3Rows 0) bRows 111) (wRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row1 :
    digitsEq 111 (rowProduct (ab3Rows 1) bRows 111) (wRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row2 :
    digitsEq 111 (rowProduct (ab3Rows 2) bRows 111) (wRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row3 :
    digitsEq 111 (rowProduct (ab3Rows 3) bRows 111) (wRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row4 :
    digitsEq 111 (rowProduct (ab3Rows 4) bRows 111) (wRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row5 :
    digitsEq 111 (rowProduct (ab3Rows 5) bRows 111) (wRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row6 :
    digitsEq 111 (rowProduct (ab3Rows 6) bRows 111) (wRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row7 :
    digitsEq 111 (rowProduct (ab3Rows 7) bRows 111) (wRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row8 :
    digitsEq 111 (rowProduct (ab3Rows 8) bRows 111) (wRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row9 :
    digitsEq 111 (rowProduct (ab3Rows 9) bRows 111) (wRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row10 :
    digitsEq 111 (rowProduct (ab3Rows 10) bRows 111) (wRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row11 :
    digitsEq 111 (rowProduct (ab3Rows 11) bRows 111) (wRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row12 :
    digitsEq 111 (rowProduct (ab3Rows 12) bRows 111) (wRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row13 :
    digitsEq 111 (rowProduct (ab3Rows 13) bRows 111) (wRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row14 :
    digitsEq 111 (rowProduct (ab3Rows 14) bRows 111) (wRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row15 :
    digitsEq 111 (rowProduct (ab3Rows 15) bRows 111) (wRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row16 :
    digitsEq 111 (rowProduct (ab3Rows 16) bRows 111) (wRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row17 :
    digitsEq 111 (rowProduct (ab3Rows 17) bRows 111) (wRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row18 :
    digitsEq 111 (rowProduct (ab3Rows 18) bRows 111) (wRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row19 :
    digitsEq 111 (rowProduct (ab3Rows 19) bRows 111) (wRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row20 :
    digitsEq 111 (rowProduct (ab3Rows 20) bRows 111) (wRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row21 :
    digitsEq 111 (rowProduct (ab3Rows 21) bRows 111) (wRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row22 :
    digitsEq 111 (rowProduct (ab3Rows 22) bRows 111) (wRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row23 :
    digitsEq 111 (rowProduct (ab3Rows 23) bRows 111) (wRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row24 :
    digitsEq 111 (rowProduct (ab3Rows 24) bRows 111) (wRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row25 :
    digitsEq 111 (rowProduct (ab3Rows 25) bRows 111) (wRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row26 :
    digitsEq 111 (rowProduct (ab3Rows 26) bRows 111) (wRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row27 :
    digitsEq 111 (rowProduct (ab3Rows 27) bRows 111) (wRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row28 :
    digitsEq 111 (rowProduct (ab3Rows 28) bRows 111) (wRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row29 :
    digitsEq 111 (rowProduct (ab3Rows 29) bRows 111) (wRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row30 :
    digitsEq 111 (rowProduct (ab3Rows 30) bRows 111) (wRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row31 :
    digitsEq 111 (rowProduct (ab3Rows 31) bRows 111) (wRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row32 :
    digitsEq 111 (rowProduct (ab3Rows 32) bRows 111) (wRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row33 :
    digitsEq 111 (rowProduct (ab3Rows 33) bRows 111) (wRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row34 :
    digitsEq 111 (rowProduct (ab3Rows 34) bRows 111) (wRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row35 :
    digitsEq 111 (rowProduct (ab3Rows 35) bRows 111) (wRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row36 :
    digitsEq 111 (rowProduct (ab3Rows 36) bRows 111) (wRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row37 :
    digitsEq 111 (rowProduct (ab3Rows 37) bRows 111) (wRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row38 :
    digitsEq 111 (rowProduct (ab3Rows 38) bRows 111) (wRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row39 :
    digitsEq 111 (rowProduct (ab3Rows 39) bRows 111) (wRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row40 :
    digitsEq 111 (rowProduct (ab3Rows 40) bRows 111) (wRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row41 :
    digitsEq 111 (rowProduct (ab3Rows 41) bRows 111) (wRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row42 :
    digitsEq 111 (rowProduct (ab3Rows 42) bRows 111) (wRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row43 :
    digitsEq 111 (rowProduct (ab3Rows 43) bRows 111) (wRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row44 :
    digitsEq 111 (rowProduct (ab3Rows 44) bRows 111) (wRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row45 :
    digitsEq 111 (rowProduct (ab3Rows 45) bRows 111) (wRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row46 :
    digitsEq 111 (rowProduct (ab3Rows 46) bRows 111) (wRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row47 :
    digitsEq 111 (rowProduct (ab3Rows 47) bRows 111) (wRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row48 :
    digitsEq 111 (rowProduct (ab3Rows 48) bRows 111) (wRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row49 :
    digitsEq 111 (rowProduct (ab3Rows 49) bRows 111) (wRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row50 :
    digitsEq 111 (rowProduct (ab3Rows 50) bRows 111) (wRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row51 :
    digitsEq 111 (rowProduct (ab3Rows 51) bRows 111) (wRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row52 :
    digitsEq 111 (rowProduct (ab3Rows 52) bRows 111) (wRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row53 :
    digitsEq 111 (rowProduct (ab3Rows 53) bRows 111) (wRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row54 :
    digitsEq 111 (rowProduct (ab3Rows 54) bRows 111) (wRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row55 :
    digitsEq 111 (rowProduct (ab3Rows 55) bRows 111) (wRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row56 :
    digitsEq 111 (rowProduct (ab3Rows 56) bRows 111) (wRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row57 :
    digitsEq 111 (rowProduct (ab3Rows 57) bRows 111) (wRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row58 :
    digitsEq 111 (rowProduct (ab3Rows 58) bRows 111) (wRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row59 :
    digitsEq 111 (rowProduct (ab3Rows 59) bRows 111) (wRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row60 :
    digitsEq 111 (rowProduct (ab3Rows 60) bRows 111) (wRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row61 :
    digitsEq 111 (rowProduct (ab3Rows 61) bRows 111) (wRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row62 :
    digitsEq 111 (rowProduct (ab3Rows 62) bRows 111) (wRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row63 :
    digitsEq 111 (rowProduct (ab3Rows 63) bRows 111) (wRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row64 :
    digitsEq 111 (rowProduct (ab3Rows 64) bRows 111) (wRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row65 :
    digitsEq 111 (rowProduct (ab3Rows 65) bRows 111) (wRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row66 :
    digitsEq 111 (rowProduct (ab3Rows 66) bRows 111) (wRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row67 :
    digitsEq 111 (rowProduct (ab3Rows 67) bRows 111) (wRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row68 :
    digitsEq 111 (rowProduct (ab3Rows 68) bRows 111) (wRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row69 :
    digitsEq 111 (rowProduct (ab3Rows 69) bRows 111) (wRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row70 :
    digitsEq 111 (rowProduct (ab3Rows 70) bRows 111) (wRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row71 :
    digitsEq 111 (rowProduct (ab3Rows 71) bRows 111) (wRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row72 :
    digitsEq 111 (rowProduct (ab3Rows 72) bRows 111) (wRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row73 :
    digitsEq 111 (rowProduct (ab3Rows 73) bRows 111) (wRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row74 :
    digitsEq 111 (rowProduct (ab3Rows 74) bRows 111) (wRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row75 :
    digitsEq 111 (rowProduct (ab3Rows 75) bRows 111) (wRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row76 :
    digitsEq 111 (rowProduct (ab3Rows 76) bRows 111) (wRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row77 :
    digitsEq 111 (rowProduct (ab3Rows 77) bRows 111) (wRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row78 :
    digitsEq 111 (rowProduct (ab3Rows 78) bRows 111) (wRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row79 :
    digitsEq 111 (rowProduct (ab3Rows 79) bRows 111) (wRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row80 :
    digitsEq 111 (rowProduct (ab3Rows 80) bRows 111) (wRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row81 :
    digitsEq 111 (rowProduct (ab3Rows 81) bRows 111) (wRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row82 :
    digitsEq 111 (rowProduct (ab3Rows 82) bRows 111) (wRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row83 :
    digitsEq 111 (rowProduct (ab3Rows 83) bRows 111) (wRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row84 :
    digitsEq 111 (rowProduct (ab3Rows 84) bRows 111) (wRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row85 :
    digitsEq 111 (rowProduct (ab3Rows 85) bRows 111) (wRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row86 :
    digitsEq 111 (rowProduct (ab3Rows 86) bRows 111) (wRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row87 :
    digitsEq 111 (rowProduct (ab3Rows 87) bRows 111) (wRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row88 :
    digitsEq 111 (rowProduct (ab3Rows 88) bRows 111) (wRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row89 :
    digitsEq 111 (rowProduct (ab3Rows 89) bRows 111) (wRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row90 :
    digitsEq 111 (rowProduct (ab3Rows 90) bRows 111) (wRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row91 :
    digitsEq 111 (rowProduct (ab3Rows 91) bRows 111) (wRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row92 :
    digitsEq 111 (rowProduct (ab3Rows 92) bRows 111) (wRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row93 :
    digitsEq 111 (rowProduct (ab3Rows 93) bRows 111) (wRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row94 :
    digitsEq 111 (rowProduct (ab3Rows 94) bRows 111) (wRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row95 :
    digitsEq 111 (rowProduct (ab3Rows 95) bRows 111) (wRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row96 :
    digitsEq 111 (rowProduct (ab3Rows 96) bRows 111) (wRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row97 :
    digitsEq 111 (rowProduct (ab3Rows 97) bRows 111) (wRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row98 :
    digitsEq 111 (rowProduct (ab3Rows 98) bRows 111) (wRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row99 :
    digitsEq 111 (rowProduct (ab3Rows 99) bRows 111) (wRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row100 :
    digitsEq 111 (rowProduct (ab3Rows 100) bRows 111) (wRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row101 :
    digitsEq 111 (rowProduct (ab3Rows 101) bRows 111) (wRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row102 :
    digitsEq 111 (rowProduct (ab3Rows 102) bRows 111) (wRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row103 :
    digitsEq 111 (rowProduct (ab3Rows 103) bRows 111) (wRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row104 :
    digitsEq 111 (rowProduct (ab3Rows 104) bRows 111) (wRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row105 :
    digitsEq 111 (rowProduct (ab3Rows 105) bRows 111) (wRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row106 :
    digitsEq 111 (rowProduct (ab3Rows 106) bRows 111) (wRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row107 :
    digitsEq 111 (rowProduct (ab3Rows 107) bRows 111) (wRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row108 :
    digitsEq 111 (rowProduct (ab3Rows 108) bRows 111) (wRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row109 :
    digitsEq 111 (rowProduct (ab3Rows 109) bRows 111) (wRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w_row110 :
    digitsEq 111 (rowProduct (ab3Rows 110) bRows 111) (wRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem w_rows : ∀ i,
    digitsEq 111 (rowProduct (ab3Rows i) bRows 111) (wRows i) = true :=
  (Fin.cases w_row0
    (Fin.cases w_row1
    (Fin.cases w_row2
    (Fin.cases w_row3
    (Fin.cases w_row4
    (Fin.cases w_row5
    (Fin.cases w_row6
    (Fin.cases w_row7
    (Fin.cases w_row8
    (Fin.cases w_row9
    (Fin.cases w_row10
    (Fin.cases w_row11
    (Fin.cases w_row12
    (Fin.cases w_row13
    (Fin.cases w_row14
    (Fin.cases w_row15
    (Fin.cases w_row16
    (Fin.cases w_row17
    (Fin.cases w_row18
    (Fin.cases w_row19
    (Fin.cases w_row20
    (Fin.cases w_row21
    (Fin.cases w_row22
    (Fin.cases w_row23
    (Fin.cases w_row24
    (Fin.cases w_row25
    (Fin.cases w_row26
    (Fin.cases w_row27
    (Fin.cases w_row28
    (Fin.cases w_row29
    (Fin.cases w_row30
    (Fin.cases w_row31
    (Fin.cases w_row32
    (Fin.cases w_row33
    (Fin.cases w_row34
    (Fin.cases w_row35
    (Fin.cases w_row36
    (Fin.cases w_row37
    (Fin.cases w_row38
    (Fin.cases w_row39
    (Fin.cases w_row40
    (Fin.cases w_row41
    (Fin.cases w_row42
    (Fin.cases w_row43
    (Fin.cases w_row44
    (Fin.cases w_row45
    (Fin.cases w_row46
    (Fin.cases w_row47
    (Fin.cases w_row48
    (Fin.cases w_row49
    (Fin.cases w_row50
    (Fin.cases w_row51
    (Fin.cases w_row52
    (Fin.cases w_row53
    (Fin.cases w_row54
    (Fin.cases w_row55
    (Fin.cases w_row56
    (Fin.cases w_row57
    (Fin.cases w_row58
    (Fin.cases w_row59
    (Fin.cases w_row60
    (Fin.cases w_row61
    (Fin.cases w_row62
    (Fin.cases w_row63
    (Fin.cases w_row64
    (Fin.cases w_row65
    (Fin.cases w_row66
    (Fin.cases w_row67
    (Fin.cases w_row68
    (Fin.cases w_row69
    (Fin.cases w_row70
    (Fin.cases w_row71
    (Fin.cases w_row72
    (Fin.cases w_row73
    (Fin.cases w_row74
    (Fin.cases w_row75
    (Fin.cases w_row76
    (Fin.cases w_row77
    (Fin.cases w_row78
    (Fin.cases w_row79
    (Fin.cases w_row80
    (Fin.cases w_row81
    (Fin.cases w_row82
    (Fin.cases w_row83
    (Fin.cases w_row84
    (Fin.cases w_row85
    (Fin.cases w_row86
    (Fin.cases w_row87
    (Fin.cases w_row88
    (Fin.cases w_row89
    (Fin.cases w_row90
    (Fin.cases w_row91
    (Fin.cases w_row92
    (Fin.cases w_row93
    (Fin.cases w_row94
    (Fin.cases w_row95
    (Fin.cases w_row96
    (Fin.cases w_row97
    (Fin.cases w_row98
    (Fin.cases w_row99
    (Fin.cases w_row100
    (Fin.cases w_row101
    (Fin.cases w_row102
    (Fin.cases w_row103
    (Fin.cases w_row104
    (Fin.cases w_row105
    (Fin.cases w_row106
    (Fin.cases w_row107
    (Fin.cases w_row108
    (Fin.cases w_row109
    (Fin.cases w_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_w : ab3Matrix * bMatrix = wMatrix :=
  decode_mul _ _ _ ab3_small b_small w_rows

end Lyons.Atlas111WordCertificate
