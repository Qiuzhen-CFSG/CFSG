module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: w32 times w

These 111 row checks certify `w32Matrix * wMatrix = w33Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row0 :
    digitsEq 111 (rowProduct (w32Rows 0) wRows 111) (w33Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row1 :
    digitsEq 111 (rowProduct (w32Rows 1) wRows 111) (w33Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row2 :
    digitsEq 111 (rowProduct (w32Rows 2) wRows 111) (w33Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row3 :
    digitsEq 111 (rowProduct (w32Rows 3) wRows 111) (w33Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row4 :
    digitsEq 111 (rowProduct (w32Rows 4) wRows 111) (w33Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row5 :
    digitsEq 111 (rowProduct (w32Rows 5) wRows 111) (w33Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row6 :
    digitsEq 111 (rowProduct (w32Rows 6) wRows 111) (w33Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row7 :
    digitsEq 111 (rowProduct (w32Rows 7) wRows 111) (w33Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row8 :
    digitsEq 111 (rowProduct (w32Rows 8) wRows 111) (w33Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row9 :
    digitsEq 111 (rowProduct (w32Rows 9) wRows 111) (w33Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row10 :
    digitsEq 111 (rowProduct (w32Rows 10) wRows 111) (w33Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row11 :
    digitsEq 111 (rowProduct (w32Rows 11) wRows 111) (w33Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row12 :
    digitsEq 111 (rowProduct (w32Rows 12) wRows 111) (w33Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row13 :
    digitsEq 111 (rowProduct (w32Rows 13) wRows 111) (w33Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row14 :
    digitsEq 111 (rowProduct (w32Rows 14) wRows 111) (w33Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row15 :
    digitsEq 111 (rowProduct (w32Rows 15) wRows 111) (w33Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row16 :
    digitsEq 111 (rowProduct (w32Rows 16) wRows 111) (w33Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row17 :
    digitsEq 111 (rowProduct (w32Rows 17) wRows 111) (w33Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row18 :
    digitsEq 111 (rowProduct (w32Rows 18) wRows 111) (w33Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row19 :
    digitsEq 111 (rowProduct (w32Rows 19) wRows 111) (w33Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row20 :
    digitsEq 111 (rowProduct (w32Rows 20) wRows 111) (w33Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row21 :
    digitsEq 111 (rowProduct (w32Rows 21) wRows 111) (w33Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row22 :
    digitsEq 111 (rowProduct (w32Rows 22) wRows 111) (w33Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row23 :
    digitsEq 111 (rowProduct (w32Rows 23) wRows 111) (w33Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row24 :
    digitsEq 111 (rowProduct (w32Rows 24) wRows 111) (w33Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row25 :
    digitsEq 111 (rowProduct (w32Rows 25) wRows 111) (w33Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row26 :
    digitsEq 111 (rowProduct (w32Rows 26) wRows 111) (w33Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row27 :
    digitsEq 111 (rowProduct (w32Rows 27) wRows 111) (w33Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row28 :
    digitsEq 111 (rowProduct (w32Rows 28) wRows 111) (w33Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row29 :
    digitsEq 111 (rowProduct (w32Rows 29) wRows 111) (w33Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row30 :
    digitsEq 111 (rowProduct (w32Rows 30) wRows 111) (w33Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row31 :
    digitsEq 111 (rowProduct (w32Rows 31) wRows 111) (w33Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row32 :
    digitsEq 111 (rowProduct (w32Rows 32) wRows 111) (w33Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row33 :
    digitsEq 111 (rowProduct (w32Rows 33) wRows 111) (w33Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row34 :
    digitsEq 111 (rowProduct (w32Rows 34) wRows 111) (w33Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row35 :
    digitsEq 111 (rowProduct (w32Rows 35) wRows 111) (w33Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row36 :
    digitsEq 111 (rowProduct (w32Rows 36) wRows 111) (w33Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row37 :
    digitsEq 111 (rowProduct (w32Rows 37) wRows 111) (w33Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row38 :
    digitsEq 111 (rowProduct (w32Rows 38) wRows 111) (w33Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row39 :
    digitsEq 111 (rowProduct (w32Rows 39) wRows 111) (w33Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row40 :
    digitsEq 111 (rowProduct (w32Rows 40) wRows 111) (w33Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row41 :
    digitsEq 111 (rowProduct (w32Rows 41) wRows 111) (w33Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row42 :
    digitsEq 111 (rowProduct (w32Rows 42) wRows 111) (w33Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row43 :
    digitsEq 111 (rowProduct (w32Rows 43) wRows 111) (w33Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row44 :
    digitsEq 111 (rowProduct (w32Rows 44) wRows 111) (w33Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row45 :
    digitsEq 111 (rowProduct (w32Rows 45) wRows 111) (w33Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row46 :
    digitsEq 111 (rowProduct (w32Rows 46) wRows 111) (w33Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row47 :
    digitsEq 111 (rowProduct (w32Rows 47) wRows 111) (w33Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row48 :
    digitsEq 111 (rowProduct (w32Rows 48) wRows 111) (w33Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row49 :
    digitsEq 111 (rowProduct (w32Rows 49) wRows 111) (w33Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row50 :
    digitsEq 111 (rowProduct (w32Rows 50) wRows 111) (w33Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row51 :
    digitsEq 111 (rowProduct (w32Rows 51) wRows 111) (w33Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row52 :
    digitsEq 111 (rowProduct (w32Rows 52) wRows 111) (w33Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row53 :
    digitsEq 111 (rowProduct (w32Rows 53) wRows 111) (w33Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row54 :
    digitsEq 111 (rowProduct (w32Rows 54) wRows 111) (w33Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row55 :
    digitsEq 111 (rowProduct (w32Rows 55) wRows 111) (w33Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row56 :
    digitsEq 111 (rowProduct (w32Rows 56) wRows 111) (w33Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row57 :
    digitsEq 111 (rowProduct (w32Rows 57) wRows 111) (w33Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row58 :
    digitsEq 111 (rowProduct (w32Rows 58) wRows 111) (w33Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row59 :
    digitsEq 111 (rowProduct (w32Rows 59) wRows 111) (w33Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row60 :
    digitsEq 111 (rowProduct (w32Rows 60) wRows 111) (w33Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row61 :
    digitsEq 111 (rowProduct (w32Rows 61) wRows 111) (w33Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row62 :
    digitsEq 111 (rowProduct (w32Rows 62) wRows 111) (w33Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row63 :
    digitsEq 111 (rowProduct (w32Rows 63) wRows 111) (w33Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row64 :
    digitsEq 111 (rowProduct (w32Rows 64) wRows 111) (w33Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row65 :
    digitsEq 111 (rowProduct (w32Rows 65) wRows 111) (w33Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row66 :
    digitsEq 111 (rowProduct (w32Rows 66) wRows 111) (w33Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row67 :
    digitsEq 111 (rowProduct (w32Rows 67) wRows 111) (w33Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row68 :
    digitsEq 111 (rowProduct (w32Rows 68) wRows 111) (w33Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row69 :
    digitsEq 111 (rowProduct (w32Rows 69) wRows 111) (w33Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row70 :
    digitsEq 111 (rowProduct (w32Rows 70) wRows 111) (w33Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row71 :
    digitsEq 111 (rowProduct (w32Rows 71) wRows 111) (w33Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row72 :
    digitsEq 111 (rowProduct (w32Rows 72) wRows 111) (w33Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row73 :
    digitsEq 111 (rowProduct (w32Rows 73) wRows 111) (w33Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row74 :
    digitsEq 111 (rowProduct (w32Rows 74) wRows 111) (w33Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row75 :
    digitsEq 111 (rowProduct (w32Rows 75) wRows 111) (w33Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row76 :
    digitsEq 111 (rowProduct (w32Rows 76) wRows 111) (w33Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row77 :
    digitsEq 111 (rowProduct (w32Rows 77) wRows 111) (w33Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row78 :
    digitsEq 111 (rowProduct (w32Rows 78) wRows 111) (w33Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row79 :
    digitsEq 111 (rowProduct (w32Rows 79) wRows 111) (w33Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row80 :
    digitsEq 111 (rowProduct (w32Rows 80) wRows 111) (w33Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row81 :
    digitsEq 111 (rowProduct (w32Rows 81) wRows 111) (w33Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row82 :
    digitsEq 111 (rowProduct (w32Rows 82) wRows 111) (w33Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row83 :
    digitsEq 111 (rowProduct (w32Rows 83) wRows 111) (w33Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row84 :
    digitsEq 111 (rowProduct (w32Rows 84) wRows 111) (w33Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row85 :
    digitsEq 111 (rowProduct (w32Rows 85) wRows 111) (w33Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row86 :
    digitsEq 111 (rowProduct (w32Rows 86) wRows 111) (w33Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row87 :
    digitsEq 111 (rowProduct (w32Rows 87) wRows 111) (w33Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row88 :
    digitsEq 111 (rowProduct (w32Rows 88) wRows 111) (w33Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row89 :
    digitsEq 111 (rowProduct (w32Rows 89) wRows 111) (w33Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row90 :
    digitsEq 111 (rowProduct (w32Rows 90) wRows 111) (w33Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row91 :
    digitsEq 111 (rowProduct (w32Rows 91) wRows 111) (w33Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row92 :
    digitsEq 111 (rowProduct (w32Rows 92) wRows 111) (w33Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row93 :
    digitsEq 111 (rowProduct (w32Rows 93) wRows 111) (w33Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row94 :
    digitsEq 111 (rowProduct (w32Rows 94) wRows 111) (w33Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row95 :
    digitsEq 111 (rowProduct (w32Rows 95) wRows 111) (w33Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row96 :
    digitsEq 111 (rowProduct (w32Rows 96) wRows 111) (w33Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row97 :
    digitsEq 111 (rowProduct (w32Rows 97) wRows 111) (w33Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row98 :
    digitsEq 111 (rowProduct (w32Rows 98) wRows 111) (w33Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row99 :
    digitsEq 111 (rowProduct (w32Rows 99) wRows 111) (w33Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row100 :
    digitsEq 111 (rowProduct (w32Rows 100) wRows 111) (w33Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row101 :
    digitsEq 111 (rowProduct (w32Rows 101) wRows 111) (w33Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row102 :
    digitsEq 111 (rowProduct (w32Rows 102) wRows 111) (w33Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row103 :
    digitsEq 111 (rowProduct (w32Rows 103) wRows 111) (w33Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row104 :
    digitsEq 111 (rowProduct (w32Rows 104) wRows 111) (w33Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row105 :
    digitsEq 111 (rowProduct (w32Rows 105) wRows 111) (w33Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row106 :
    digitsEq 111 (rowProduct (w32Rows 106) wRows 111) (w33Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row107 :
    digitsEq 111 (rowProduct (w32Rows 107) wRows 111) (w33Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row108 :
    digitsEq 111 (rowProduct (w32Rows 108) wRows 111) (w33Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row109 :
    digitsEq 111 (rowProduct (w32Rows 109) wRows 111) (w33Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem w33_row110 :
    digitsEq 111 (rowProduct (w32Rows 110) wRows 111) (w33Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem w33_rows : ∀ i,
    digitsEq 111 (rowProduct (w32Rows i) wRows 111) (w33Rows i) = true :=
  (Fin.cases w33_row0
    (Fin.cases w33_row1
    (Fin.cases w33_row2
    (Fin.cases w33_row3
    (Fin.cases w33_row4
    (Fin.cases w33_row5
    (Fin.cases w33_row6
    (Fin.cases w33_row7
    (Fin.cases w33_row8
    (Fin.cases w33_row9
    (Fin.cases w33_row10
    (Fin.cases w33_row11
    (Fin.cases w33_row12
    (Fin.cases w33_row13
    (Fin.cases w33_row14
    (Fin.cases w33_row15
    (Fin.cases w33_row16
    (Fin.cases w33_row17
    (Fin.cases w33_row18
    (Fin.cases w33_row19
    (Fin.cases w33_row20
    (Fin.cases w33_row21
    (Fin.cases w33_row22
    (Fin.cases w33_row23
    (Fin.cases w33_row24
    (Fin.cases w33_row25
    (Fin.cases w33_row26
    (Fin.cases w33_row27
    (Fin.cases w33_row28
    (Fin.cases w33_row29
    (Fin.cases w33_row30
    (Fin.cases w33_row31
    (Fin.cases w33_row32
    (Fin.cases w33_row33
    (Fin.cases w33_row34
    (Fin.cases w33_row35
    (Fin.cases w33_row36
    (Fin.cases w33_row37
    (Fin.cases w33_row38
    (Fin.cases w33_row39
    (Fin.cases w33_row40
    (Fin.cases w33_row41
    (Fin.cases w33_row42
    (Fin.cases w33_row43
    (Fin.cases w33_row44
    (Fin.cases w33_row45
    (Fin.cases w33_row46
    (Fin.cases w33_row47
    (Fin.cases w33_row48
    (Fin.cases w33_row49
    (Fin.cases w33_row50
    (Fin.cases w33_row51
    (Fin.cases w33_row52
    (Fin.cases w33_row53
    (Fin.cases w33_row54
    (Fin.cases w33_row55
    (Fin.cases w33_row56
    (Fin.cases w33_row57
    (Fin.cases w33_row58
    (Fin.cases w33_row59
    (Fin.cases w33_row60
    (Fin.cases w33_row61
    (Fin.cases w33_row62
    (Fin.cases w33_row63
    (Fin.cases w33_row64
    (Fin.cases w33_row65
    (Fin.cases w33_row66
    (Fin.cases w33_row67
    (Fin.cases w33_row68
    (Fin.cases w33_row69
    (Fin.cases w33_row70
    (Fin.cases w33_row71
    (Fin.cases w33_row72
    (Fin.cases w33_row73
    (Fin.cases w33_row74
    (Fin.cases w33_row75
    (Fin.cases w33_row76
    (Fin.cases w33_row77
    (Fin.cases w33_row78
    (Fin.cases w33_row79
    (Fin.cases w33_row80
    (Fin.cases w33_row81
    (Fin.cases w33_row82
    (Fin.cases w33_row83
    (Fin.cases w33_row84
    (Fin.cases w33_row85
    (Fin.cases w33_row86
    (Fin.cases w33_row87
    (Fin.cases w33_row88
    (Fin.cases w33_row89
    (Fin.cases w33_row90
    (Fin.cases w33_row91
    (Fin.cases w33_row92
    (Fin.cases w33_row93
    (Fin.cases w33_row94
    (Fin.cases w33_row95
    (Fin.cases w33_row96
    (Fin.cases w33_row97
    (Fin.cases w33_row98
    (Fin.cases w33_row99
    (Fin.cases w33_row100
    (Fin.cases w33_row101
    (Fin.cases w33_row102
    (Fin.cases w33_row103
    (Fin.cases w33_row104
    (Fin.cases w33_row105
    (Fin.cases w33_row106
    (Fin.cases w33_row107
    (Fin.cases w33_row108
    (Fin.cases w33_row109
    (Fin.cases w33_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_w33 : w32Matrix * wMatrix = w33Matrix :=
  decode_mul _ _ _ w32_small w_small w33_rows

end Lyons.Atlas111WordCertificate
