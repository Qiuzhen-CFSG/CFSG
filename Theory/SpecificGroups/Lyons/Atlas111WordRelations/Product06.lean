module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Data

/-!
# Certified Lyons multiplication: ab3 times ab3

These 111 row checks certify `ab3Matrix * ab3Matrix = ab6Matrix`.
The carry-free arithmetic soundness theorem gives the matrix identity.
Source: `../Atlas111Source/` and `../Atlas111WordSource/Generate.py`.
All closed certificates are checked by the Lean kernel.
-/

namespace Lyons.Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row0 :
    digitsEq 111 (rowProduct (ab3Rows 0) ab3Rows 111) (ab6Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row1 :
    digitsEq 111 (rowProduct (ab3Rows 1) ab3Rows 111) (ab6Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row2 :
    digitsEq 111 (rowProduct (ab3Rows 2) ab3Rows 111) (ab6Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row3 :
    digitsEq 111 (rowProduct (ab3Rows 3) ab3Rows 111) (ab6Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row4 :
    digitsEq 111 (rowProduct (ab3Rows 4) ab3Rows 111) (ab6Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row5 :
    digitsEq 111 (rowProduct (ab3Rows 5) ab3Rows 111) (ab6Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row6 :
    digitsEq 111 (rowProduct (ab3Rows 6) ab3Rows 111) (ab6Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row7 :
    digitsEq 111 (rowProduct (ab3Rows 7) ab3Rows 111) (ab6Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row8 :
    digitsEq 111 (rowProduct (ab3Rows 8) ab3Rows 111) (ab6Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row9 :
    digitsEq 111 (rowProduct (ab3Rows 9) ab3Rows 111) (ab6Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row10 :
    digitsEq 111 (rowProduct (ab3Rows 10) ab3Rows 111) (ab6Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row11 :
    digitsEq 111 (rowProduct (ab3Rows 11) ab3Rows 111) (ab6Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row12 :
    digitsEq 111 (rowProduct (ab3Rows 12) ab3Rows 111) (ab6Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row13 :
    digitsEq 111 (rowProduct (ab3Rows 13) ab3Rows 111) (ab6Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row14 :
    digitsEq 111 (rowProduct (ab3Rows 14) ab3Rows 111) (ab6Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row15 :
    digitsEq 111 (rowProduct (ab3Rows 15) ab3Rows 111) (ab6Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row16 :
    digitsEq 111 (rowProduct (ab3Rows 16) ab3Rows 111) (ab6Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row17 :
    digitsEq 111 (rowProduct (ab3Rows 17) ab3Rows 111) (ab6Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row18 :
    digitsEq 111 (rowProduct (ab3Rows 18) ab3Rows 111) (ab6Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row19 :
    digitsEq 111 (rowProduct (ab3Rows 19) ab3Rows 111) (ab6Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row20 :
    digitsEq 111 (rowProduct (ab3Rows 20) ab3Rows 111) (ab6Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row21 :
    digitsEq 111 (rowProduct (ab3Rows 21) ab3Rows 111) (ab6Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row22 :
    digitsEq 111 (rowProduct (ab3Rows 22) ab3Rows 111) (ab6Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row23 :
    digitsEq 111 (rowProduct (ab3Rows 23) ab3Rows 111) (ab6Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row24 :
    digitsEq 111 (rowProduct (ab3Rows 24) ab3Rows 111) (ab6Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row25 :
    digitsEq 111 (rowProduct (ab3Rows 25) ab3Rows 111) (ab6Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row26 :
    digitsEq 111 (rowProduct (ab3Rows 26) ab3Rows 111) (ab6Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row27 :
    digitsEq 111 (rowProduct (ab3Rows 27) ab3Rows 111) (ab6Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row28 :
    digitsEq 111 (rowProduct (ab3Rows 28) ab3Rows 111) (ab6Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row29 :
    digitsEq 111 (rowProduct (ab3Rows 29) ab3Rows 111) (ab6Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row30 :
    digitsEq 111 (rowProduct (ab3Rows 30) ab3Rows 111) (ab6Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row31 :
    digitsEq 111 (rowProduct (ab3Rows 31) ab3Rows 111) (ab6Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row32 :
    digitsEq 111 (rowProduct (ab3Rows 32) ab3Rows 111) (ab6Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row33 :
    digitsEq 111 (rowProduct (ab3Rows 33) ab3Rows 111) (ab6Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row34 :
    digitsEq 111 (rowProduct (ab3Rows 34) ab3Rows 111) (ab6Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row35 :
    digitsEq 111 (rowProduct (ab3Rows 35) ab3Rows 111) (ab6Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row36 :
    digitsEq 111 (rowProduct (ab3Rows 36) ab3Rows 111) (ab6Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row37 :
    digitsEq 111 (rowProduct (ab3Rows 37) ab3Rows 111) (ab6Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row38 :
    digitsEq 111 (rowProduct (ab3Rows 38) ab3Rows 111) (ab6Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row39 :
    digitsEq 111 (rowProduct (ab3Rows 39) ab3Rows 111) (ab6Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row40 :
    digitsEq 111 (rowProduct (ab3Rows 40) ab3Rows 111) (ab6Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row41 :
    digitsEq 111 (rowProduct (ab3Rows 41) ab3Rows 111) (ab6Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row42 :
    digitsEq 111 (rowProduct (ab3Rows 42) ab3Rows 111) (ab6Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row43 :
    digitsEq 111 (rowProduct (ab3Rows 43) ab3Rows 111) (ab6Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row44 :
    digitsEq 111 (rowProduct (ab3Rows 44) ab3Rows 111) (ab6Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row45 :
    digitsEq 111 (rowProduct (ab3Rows 45) ab3Rows 111) (ab6Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row46 :
    digitsEq 111 (rowProduct (ab3Rows 46) ab3Rows 111) (ab6Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row47 :
    digitsEq 111 (rowProduct (ab3Rows 47) ab3Rows 111) (ab6Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row48 :
    digitsEq 111 (rowProduct (ab3Rows 48) ab3Rows 111) (ab6Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row49 :
    digitsEq 111 (rowProduct (ab3Rows 49) ab3Rows 111) (ab6Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row50 :
    digitsEq 111 (rowProduct (ab3Rows 50) ab3Rows 111) (ab6Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row51 :
    digitsEq 111 (rowProduct (ab3Rows 51) ab3Rows 111) (ab6Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row52 :
    digitsEq 111 (rowProduct (ab3Rows 52) ab3Rows 111) (ab6Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row53 :
    digitsEq 111 (rowProduct (ab3Rows 53) ab3Rows 111) (ab6Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row54 :
    digitsEq 111 (rowProduct (ab3Rows 54) ab3Rows 111) (ab6Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row55 :
    digitsEq 111 (rowProduct (ab3Rows 55) ab3Rows 111) (ab6Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row56 :
    digitsEq 111 (rowProduct (ab3Rows 56) ab3Rows 111) (ab6Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row57 :
    digitsEq 111 (rowProduct (ab3Rows 57) ab3Rows 111) (ab6Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row58 :
    digitsEq 111 (rowProduct (ab3Rows 58) ab3Rows 111) (ab6Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row59 :
    digitsEq 111 (rowProduct (ab3Rows 59) ab3Rows 111) (ab6Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row60 :
    digitsEq 111 (rowProduct (ab3Rows 60) ab3Rows 111) (ab6Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row61 :
    digitsEq 111 (rowProduct (ab3Rows 61) ab3Rows 111) (ab6Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row62 :
    digitsEq 111 (rowProduct (ab3Rows 62) ab3Rows 111) (ab6Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row63 :
    digitsEq 111 (rowProduct (ab3Rows 63) ab3Rows 111) (ab6Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row64 :
    digitsEq 111 (rowProduct (ab3Rows 64) ab3Rows 111) (ab6Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row65 :
    digitsEq 111 (rowProduct (ab3Rows 65) ab3Rows 111) (ab6Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row66 :
    digitsEq 111 (rowProduct (ab3Rows 66) ab3Rows 111) (ab6Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row67 :
    digitsEq 111 (rowProduct (ab3Rows 67) ab3Rows 111) (ab6Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row68 :
    digitsEq 111 (rowProduct (ab3Rows 68) ab3Rows 111) (ab6Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row69 :
    digitsEq 111 (rowProduct (ab3Rows 69) ab3Rows 111) (ab6Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row70 :
    digitsEq 111 (rowProduct (ab3Rows 70) ab3Rows 111) (ab6Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row71 :
    digitsEq 111 (rowProduct (ab3Rows 71) ab3Rows 111) (ab6Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row72 :
    digitsEq 111 (rowProduct (ab3Rows 72) ab3Rows 111) (ab6Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row73 :
    digitsEq 111 (rowProduct (ab3Rows 73) ab3Rows 111) (ab6Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row74 :
    digitsEq 111 (rowProduct (ab3Rows 74) ab3Rows 111) (ab6Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row75 :
    digitsEq 111 (rowProduct (ab3Rows 75) ab3Rows 111) (ab6Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row76 :
    digitsEq 111 (rowProduct (ab3Rows 76) ab3Rows 111) (ab6Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row77 :
    digitsEq 111 (rowProduct (ab3Rows 77) ab3Rows 111) (ab6Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row78 :
    digitsEq 111 (rowProduct (ab3Rows 78) ab3Rows 111) (ab6Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row79 :
    digitsEq 111 (rowProduct (ab3Rows 79) ab3Rows 111) (ab6Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row80 :
    digitsEq 111 (rowProduct (ab3Rows 80) ab3Rows 111) (ab6Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row81 :
    digitsEq 111 (rowProduct (ab3Rows 81) ab3Rows 111) (ab6Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row82 :
    digitsEq 111 (rowProduct (ab3Rows 82) ab3Rows 111) (ab6Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row83 :
    digitsEq 111 (rowProduct (ab3Rows 83) ab3Rows 111) (ab6Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row84 :
    digitsEq 111 (rowProduct (ab3Rows 84) ab3Rows 111) (ab6Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row85 :
    digitsEq 111 (rowProduct (ab3Rows 85) ab3Rows 111) (ab6Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row86 :
    digitsEq 111 (rowProduct (ab3Rows 86) ab3Rows 111) (ab6Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row87 :
    digitsEq 111 (rowProduct (ab3Rows 87) ab3Rows 111) (ab6Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row88 :
    digitsEq 111 (rowProduct (ab3Rows 88) ab3Rows 111) (ab6Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row89 :
    digitsEq 111 (rowProduct (ab3Rows 89) ab3Rows 111) (ab6Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row90 :
    digitsEq 111 (rowProduct (ab3Rows 90) ab3Rows 111) (ab6Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row91 :
    digitsEq 111 (rowProduct (ab3Rows 91) ab3Rows 111) (ab6Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row92 :
    digitsEq 111 (rowProduct (ab3Rows 92) ab3Rows 111) (ab6Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row93 :
    digitsEq 111 (rowProduct (ab3Rows 93) ab3Rows 111) (ab6Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row94 :
    digitsEq 111 (rowProduct (ab3Rows 94) ab3Rows 111) (ab6Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row95 :
    digitsEq 111 (rowProduct (ab3Rows 95) ab3Rows 111) (ab6Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row96 :
    digitsEq 111 (rowProduct (ab3Rows 96) ab3Rows 111) (ab6Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row97 :
    digitsEq 111 (rowProduct (ab3Rows 97) ab3Rows 111) (ab6Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row98 :
    digitsEq 111 (rowProduct (ab3Rows 98) ab3Rows 111) (ab6Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row99 :
    digitsEq 111 (rowProduct (ab3Rows 99) ab3Rows 111) (ab6Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row100 :
    digitsEq 111 (rowProduct (ab3Rows 100) ab3Rows 111) (ab6Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row101 :
    digitsEq 111 (rowProduct (ab3Rows 101) ab3Rows 111) (ab6Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row102 :
    digitsEq 111 (rowProduct (ab3Rows 102) ab3Rows 111) (ab6Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row103 :
    digitsEq 111 (rowProduct (ab3Rows 103) ab3Rows 111) (ab6Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row104 :
    digitsEq 111 (rowProduct (ab3Rows 104) ab3Rows 111) (ab6Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row105 :
    digitsEq 111 (rowProduct (ab3Rows 105) ab3Rows 111) (ab6Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row106 :
    digitsEq 111 (rowProduct (ab3Rows 106) ab3Rows 111) (ab6Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row107 :
    digitsEq 111 (rowProduct (ab3Rows 107) ab3Rows 111) (ab6Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row108 :
    digitsEq 111 (rowProduct (ab3Rows 108) ab3Rows 111) (ab6Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row109 :
    digitsEq 111 (rowProduct (ab3Rows 109) ab3Rows 111) (ab6Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab6_row110 :
    digitsEq 111 (rowProduct (ab3Rows 110) ab3Rows 111) (ab6Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem ab6_rows : ∀ i,
    digitsEq 111 (rowProduct (ab3Rows i) ab3Rows 111) (ab6Rows i) = true :=
  (Fin.cases ab6_row0
    (Fin.cases ab6_row1
    (Fin.cases ab6_row2
    (Fin.cases ab6_row3
    (Fin.cases ab6_row4
    (Fin.cases ab6_row5
    (Fin.cases ab6_row6
    (Fin.cases ab6_row7
    (Fin.cases ab6_row8
    (Fin.cases ab6_row9
    (Fin.cases ab6_row10
    (Fin.cases ab6_row11
    (Fin.cases ab6_row12
    (Fin.cases ab6_row13
    (Fin.cases ab6_row14
    (Fin.cases ab6_row15
    (Fin.cases ab6_row16
    (Fin.cases ab6_row17
    (Fin.cases ab6_row18
    (Fin.cases ab6_row19
    (Fin.cases ab6_row20
    (Fin.cases ab6_row21
    (Fin.cases ab6_row22
    (Fin.cases ab6_row23
    (Fin.cases ab6_row24
    (Fin.cases ab6_row25
    (Fin.cases ab6_row26
    (Fin.cases ab6_row27
    (Fin.cases ab6_row28
    (Fin.cases ab6_row29
    (Fin.cases ab6_row30
    (Fin.cases ab6_row31
    (Fin.cases ab6_row32
    (Fin.cases ab6_row33
    (Fin.cases ab6_row34
    (Fin.cases ab6_row35
    (Fin.cases ab6_row36
    (Fin.cases ab6_row37
    (Fin.cases ab6_row38
    (Fin.cases ab6_row39
    (Fin.cases ab6_row40
    (Fin.cases ab6_row41
    (Fin.cases ab6_row42
    (Fin.cases ab6_row43
    (Fin.cases ab6_row44
    (Fin.cases ab6_row45
    (Fin.cases ab6_row46
    (Fin.cases ab6_row47
    (Fin.cases ab6_row48
    (Fin.cases ab6_row49
    (Fin.cases ab6_row50
    (Fin.cases ab6_row51
    (Fin.cases ab6_row52
    (Fin.cases ab6_row53
    (Fin.cases ab6_row54
    (Fin.cases ab6_row55
    (Fin.cases ab6_row56
    (Fin.cases ab6_row57
    (Fin.cases ab6_row58
    (Fin.cases ab6_row59
    (Fin.cases ab6_row60
    (Fin.cases ab6_row61
    (Fin.cases ab6_row62
    (Fin.cases ab6_row63
    (Fin.cases ab6_row64
    (Fin.cases ab6_row65
    (Fin.cases ab6_row66
    (Fin.cases ab6_row67
    (Fin.cases ab6_row68
    (Fin.cases ab6_row69
    (Fin.cases ab6_row70
    (Fin.cases ab6_row71
    (Fin.cases ab6_row72
    (Fin.cases ab6_row73
    (Fin.cases ab6_row74
    (Fin.cases ab6_row75
    (Fin.cases ab6_row76
    (Fin.cases ab6_row77
    (Fin.cases ab6_row78
    (Fin.cases ab6_row79
    (Fin.cases ab6_row80
    (Fin.cases ab6_row81
    (Fin.cases ab6_row82
    (Fin.cases ab6_row83
    (Fin.cases ab6_row84
    (Fin.cases ab6_row85
    (Fin.cases ab6_row86
    (Fin.cases ab6_row87
    (Fin.cases ab6_row88
    (Fin.cases ab6_row89
    (Fin.cases ab6_row90
    (Fin.cases ab6_row91
    (Fin.cases ab6_row92
    (Fin.cases ab6_row93
    (Fin.cases ab6_row94
    (Fin.cases ab6_row95
    (Fin.cases ab6_row96
    (Fin.cases ab6_row97
    (Fin.cases ab6_row98
    (Fin.cases ab6_row99
    (Fin.cases ab6_row100
    (Fin.cases ab6_row101
    (Fin.cases ab6_row102
    (Fin.cases ab6_row103
    (Fin.cases ab6_row104
    (Fin.cases ab6_row105
    (Fin.cases ab6_row106
    (Fin.cases ab6_row107
    (Fin.cases ab6_row108
    (Fin.cases ab6_row109
    (Fin.cases ab6_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Checked multiplication in the actual matrix algebra. -/
public theorem mul_ab6 : ab3Matrix * ab3Matrix = ab6Matrix :=
  decode_mul _ _ _ ab3_small ab3_small ab6_rows

end Lyons.Atlas111WordCertificate
