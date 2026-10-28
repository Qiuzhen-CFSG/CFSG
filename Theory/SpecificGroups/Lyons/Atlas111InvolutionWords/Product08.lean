module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: rtInv times rt

The carry-free arithmetic soundness theorem converts the 111
closed row checks into the displayed matrix identity.

Source and reproducible candidate generation:
`Atlas111InvolutionSource/GenerateWords.py` and the attributed
original matrices in `Atlas111Source/`. All checks run in Lean's kernel.
-/

namespace Lyons.Atlas111InvolutionWords

open Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row0 :
    digitsEq 111 (rowProduct (rtInvRows 0) rtRows 111) (oneRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row1 :
    digitsEq 111 (rowProduct (rtInvRows 1) rtRows 111) (oneRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row2 :
    digitsEq 111 (rowProduct (rtInvRows 2) rtRows 111) (oneRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row3 :
    digitsEq 111 (rowProduct (rtInvRows 3) rtRows 111) (oneRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row4 :
    digitsEq 111 (rowProduct (rtInvRows 4) rtRows 111) (oneRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row5 :
    digitsEq 111 (rowProduct (rtInvRows 5) rtRows 111) (oneRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row6 :
    digitsEq 111 (rowProduct (rtInvRows 6) rtRows 111) (oneRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row7 :
    digitsEq 111 (rowProduct (rtInvRows 7) rtRows 111) (oneRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row8 :
    digitsEq 111 (rowProduct (rtInvRows 8) rtRows 111) (oneRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row9 :
    digitsEq 111 (rowProduct (rtInvRows 9) rtRows 111) (oneRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row10 :
    digitsEq 111 (rowProduct (rtInvRows 10) rtRows 111) (oneRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row11 :
    digitsEq 111 (rowProduct (rtInvRows 11) rtRows 111) (oneRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row12 :
    digitsEq 111 (rowProduct (rtInvRows 12) rtRows 111) (oneRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row13 :
    digitsEq 111 (rowProduct (rtInvRows 13) rtRows 111) (oneRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row14 :
    digitsEq 111 (rowProduct (rtInvRows 14) rtRows 111) (oneRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row15 :
    digitsEq 111 (rowProduct (rtInvRows 15) rtRows 111) (oneRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row16 :
    digitsEq 111 (rowProduct (rtInvRows 16) rtRows 111) (oneRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row17 :
    digitsEq 111 (rowProduct (rtInvRows 17) rtRows 111) (oneRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row18 :
    digitsEq 111 (rowProduct (rtInvRows 18) rtRows 111) (oneRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row19 :
    digitsEq 111 (rowProduct (rtInvRows 19) rtRows 111) (oneRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row20 :
    digitsEq 111 (rowProduct (rtInvRows 20) rtRows 111) (oneRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row21 :
    digitsEq 111 (rowProduct (rtInvRows 21) rtRows 111) (oneRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row22 :
    digitsEq 111 (rowProduct (rtInvRows 22) rtRows 111) (oneRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row23 :
    digitsEq 111 (rowProduct (rtInvRows 23) rtRows 111) (oneRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row24 :
    digitsEq 111 (rowProduct (rtInvRows 24) rtRows 111) (oneRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row25 :
    digitsEq 111 (rowProduct (rtInvRows 25) rtRows 111) (oneRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row26 :
    digitsEq 111 (rowProduct (rtInvRows 26) rtRows 111) (oneRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row27 :
    digitsEq 111 (rowProduct (rtInvRows 27) rtRows 111) (oneRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row28 :
    digitsEq 111 (rowProduct (rtInvRows 28) rtRows 111) (oneRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row29 :
    digitsEq 111 (rowProduct (rtInvRows 29) rtRows 111) (oneRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row30 :
    digitsEq 111 (rowProduct (rtInvRows 30) rtRows 111) (oneRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row31 :
    digitsEq 111 (rowProduct (rtInvRows 31) rtRows 111) (oneRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row32 :
    digitsEq 111 (rowProduct (rtInvRows 32) rtRows 111) (oneRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row33 :
    digitsEq 111 (rowProduct (rtInvRows 33) rtRows 111) (oneRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row34 :
    digitsEq 111 (rowProduct (rtInvRows 34) rtRows 111) (oneRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row35 :
    digitsEq 111 (rowProduct (rtInvRows 35) rtRows 111) (oneRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row36 :
    digitsEq 111 (rowProduct (rtInvRows 36) rtRows 111) (oneRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row37 :
    digitsEq 111 (rowProduct (rtInvRows 37) rtRows 111) (oneRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row38 :
    digitsEq 111 (rowProduct (rtInvRows 38) rtRows 111) (oneRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row39 :
    digitsEq 111 (rowProduct (rtInvRows 39) rtRows 111) (oneRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row40 :
    digitsEq 111 (rowProduct (rtInvRows 40) rtRows 111) (oneRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row41 :
    digitsEq 111 (rowProduct (rtInvRows 41) rtRows 111) (oneRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row42 :
    digitsEq 111 (rowProduct (rtInvRows 42) rtRows 111) (oneRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row43 :
    digitsEq 111 (rowProduct (rtInvRows 43) rtRows 111) (oneRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row44 :
    digitsEq 111 (rowProduct (rtInvRows 44) rtRows 111) (oneRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row45 :
    digitsEq 111 (rowProduct (rtInvRows 45) rtRows 111) (oneRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row46 :
    digitsEq 111 (rowProduct (rtInvRows 46) rtRows 111) (oneRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row47 :
    digitsEq 111 (rowProduct (rtInvRows 47) rtRows 111) (oneRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row48 :
    digitsEq 111 (rowProduct (rtInvRows 48) rtRows 111) (oneRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row49 :
    digitsEq 111 (rowProduct (rtInvRows 49) rtRows 111) (oneRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row50 :
    digitsEq 111 (rowProduct (rtInvRows 50) rtRows 111) (oneRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row51 :
    digitsEq 111 (rowProduct (rtInvRows 51) rtRows 111) (oneRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row52 :
    digitsEq 111 (rowProduct (rtInvRows 52) rtRows 111) (oneRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row53 :
    digitsEq 111 (rowProduct (rtInvRows 53) rtRows 111) (oneRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row54 :
    digitsEq 111 (rowProduct (rtInvRows 54) rtRows 111) (oneRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row55 :
    digitsEq 111 (rowProduct (rtInvRows 55) rtRows 111) (oneRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row56 :
    digitsEq 111 (rowProduct (rtInvRows 56) rtRows 111) (oneRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row57 :
    digitsEq 111 (rowProduct (rtInvRows 57) rtRows 111) (oneRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row58 :
    digitsEq 111 (rowProduct (rtInvRows 58) rtRows 111) (oneRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row59 :
    digitsEq 111 (rowProduct (rtInvRows 59) rtRows 111) (oneRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row60 :
    digitsEq 111 (rowProduct (rtInvRows 60) rtRows 111) (oneRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row61 :
    digitsEq 111 (rowProduct (rtInvRows 61) rtRows 111) (oneRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row62 :
    digitsEq 111 (rowProduct (rtInvRows 62) rtRows 111) (oneRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row63 :
    digitsEq 111 (rowProduct (rtInvRows 63) rtRows 111) (oneRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row64 :
    digitsEq 111 (rowProduct (rtInvRows 64) rtRows 111) (oneRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row65 :
    digitsEq 111 (rowProduct (rtInvRows 65) rtRows 111) (oneRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row66 :
    digitsEq 111 (rowProduct (rtInvRows 66) rtRows 111) (oneRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row67 :
    digitsEq 111 (rowProduct (rtInvRows 67) rtRows 111) (oneRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row68 :
    digitsEq 111 (rowProduct (rtInvRows 68) rtRows 111) (oneRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row69 :
    digitsEq 111 (rowProduct (rtInvRows 69) rtRows 111) (oneRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row70 :
    digitsEq 111 (rowProduct (rtInvRows 70) rtRows 111) (oneRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row71 :
    digitsEq 111 (rowProduct (rtInvRows 71) rtRows 111) (oneRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row72 :
    digitsEq 111 (rowProduct (rtInvRows 72) rtRows 111) (oneRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row73 :
    digitsEq 111 (rowProduct (rtInvRows 73) rtRows 111) (oneRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row74 :
    digitsEq 111 (rowProduct (rtInvRows 74) rtRows 111) (oneRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row75 :
    digitsEq 111 (rowProduct (rtInvRows 75) rtRows 111) (oneRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row76 :
    digitsEq 111 (rowProduct (rtInvRows 76) rtRows 111) (oneRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row77 :
    digitsEq 111 (rowProduct (rtInvRows 77) rtRows 111) (oneRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row78 :
    digitsEq 111 (rowProduct (rtInvRows 78) rtRows 111) (oneRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row79 :
    digitsEq 111 (rowProduct (rtInvRows 79) rtRows 111) (oneRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row80 :
    digitsEq 111 (rowProduct (rtInvRows 80) rtRows 111) (oneRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row81 :
    digitsEq 111 (rowProduct (rtInvRows 81) rtRows 111) (oneRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row82 :
    digitsEq 111 (rowProduct (rtInvRows 82) rtRows 111) (oneRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row83 :
    digitsEq 111 (rowProduct (rtInvRows 83) rtRows 111) (oneRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row84 :
    digitsEq 111 (rowProduct (rtInvRows 84) rtRows 111) (oneRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row85 :
    digitsEq 111 (rowProduct (rtInvRows 85) rtRows 111) (oneRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row86 :
    digitsEq 111 (rowProduct (rtInvRows 86) rtRows 111) (oneRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row87 :
    digitsEq 111 (rowProduct (rtInvRows 87) rtRows 111) (oneRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row88 :
    digitsEq 111 (rowProduct (rtInvRows 88) rtRows 111) (oneRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row89 :
    digitsEq 111 (rowProduct (rtInvRows 89) rtRows 111) (oneRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row90 :
    digitsEq 111 (rowProduct (rtInvRows 90) rtRows 111) (oneRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row91 :
    digitsEq 111 (rowProduct (rtInvRows 91) rtRows 111) (oneRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row92 :
    digitsEq 111 (rowProduct (rtInvRows 92) rtRows 111) (oneRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row93 :
    digitsEq 111 (rowProduct (rtInvRows 93) rtRows 111) (oneRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row94 :
    digitsEq 111 (rowProduct (rtInvRows 94) rtRows 111) (oneRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row95 :
    digitsEq 111 (rowProduct (rtInvRows 95) rtRows 111) (oneRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row96 :
    digitsEq 111 (rowProduct (rtInvRows 96) rtRows 111) (oneRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row97 :
    digitsEq 111 (rowProduct (rtInvRows 97) rtRows 111) (oneRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row98 :
    digitsEq 111 (rowProduct (rtInvRows 98) rtRows 111) (oneRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row99 :
    digitsEq 111 (rowProduct (rtInvRows 99) rtRows 111) (oneRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row100 :
    digitsEq 111 (rowProduct (rtInvRows 100) rtRows 111) (oneRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row101 :
    digitsEq 111 (rowProduct (rtInvRows 101) rtRows 111) (oneRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row102 :
    digitsEq 111 (rowProduct (rtInvRows 102) rtRows 111) (oneRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row103 :
    digitsEq 111 (rowProduct (rtInvRows 103) rtRows 111) (oneRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row104 :
    digitsEq 111 (rowProduct (rtInvRows 104) rtRows 111) (oneRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row105 :
    digitsEq 111 (rowProduct (rtInvRows 105) rtRows 111) (oneRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row106 :
    digitsEq 111 (rowProduct (rtInvRows 106) rtRows 111) (oneRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row107 :
    digitsEq 111 (rowProduct (rtInvRows 107) rtRows 111) (oneRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row108 :
    digitsEq 111 (rowProduct (rtInvRows 108) rtRows 111) (oneRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row109 :
    digitsEq 111 (rowProduct (rtInvRows 109) rtRows 111) (oneRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rtInvCheck_row110 :
    digitsEq 111 (rowProduct (rtInvRows 110) rtRows 111) (oneRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem rtInvCheck_rows : ∀ i,
    digitsEq 111 (rowProduct (rtInvRows i) rtRows 111) (oneRows i) = true :=
  (Fin.cases rtInvCheck_row0
    (Fin.cases rtInvCheck_row1
    (Fin.cases rtInvCheck_row2
    (Fin.cases rtInvCheck_row3
    (Fin.cases rtInvCheck_row4
    (Fin.cases rtInvCheck_row5
    (Fin.cases rtInvCheck_row6
    (Fin.cases rtInvCheck_row7
    (Fin.cases rtInvCheck_row8
    (Fin.cases rtInvCheck_row9
    (Fin.cases rtInvCheck_row10
    (Fin.cases rtInvCheck_row11
    (Fin.cases rtInvCheck_row12
    (Fin.cases rtInvCheck_row13
    (Fin.cases rtInvCheck_row14
    (Fin.cases rtInvCheck_row15
    (Fin.cases rtInvCheck_row16
    (Fin.cases rtInvCheck_row17
    (Fin.cases rtInvCheck_row18
    (Fin.cases rtInvCheck_row19
    (Fin.cases rtInvCheck_row20
    (Fin.cases rtInvCheck_row21
    (Fin.cases rtInvCheck_row22
    (Fin.cases rtInvCheck_row23
    (Fin.cases rtInvCheck_row24
    (Fin.cases rtInvCheck_row25
    (Fin.cases rtInvCheck_row26
    (Fin.cases rtInvCheck_row27
    (Fin.cases rtInvCheck_row28
    (Fin.cases rtInvCheck_row29
    (Fin.cases rtInvCheck_row30
    (Fin.cases rtInvCheck_row31
    (Fin.cases rtInvCheck_row32
    (Fin.cases rtInvCheck_row33
    (Fin.cases rtInvCheck_row34
    (Fin.cases rtInvCheck_row35
    (Fin.cases rtInvCheck_row36
    (Fin.cases rtInvCheck_row37
    (Fin.cases rtInvCheck_row38
    (Fin.cases rtInvCheck_row39
    (Fin.cases rtInvCheck_row40
    (Fin.cases rtInvCheck_row41
    (Fin.cases rtInvCheck_row42
    (Fin.cases rtInvCheck_row43
    (Fin.cases rtInvCheck_row44
    (Fin.cases rtInvCheck_row45
    (Fin.cases rtInvCheck_row46
    (Fin.cases rtInvCheck_row47
    (Fin.cases rtInvCheck_row48
    (Fin.cases rtInvCheck_row49
    (Fin.cases rtInvCheck_row50
    (Fin.cases rtInvCheck_row51
    (Fin.cases rtInvCheck_row52
    (Fin.cases rtInvCheck_row53
    (Fin.cases rtInvCheck_row54
    (Fin.cases rtInvCheck_row55
    (Fin.cases rtInvCheck_row56
    (Fin.cases rtInvCheck_row57
    (Fin.cases rtInvCheck_row58
    (Fin.cases rtInvCheck_row59
    (Fin.cases rtInvCheck_row60
    (Fin.cases rtInvCheck_row61
    (Fin.cases rtInvCheck_row62
    (Fin.cases rtInvCheck_row63
    (Fin.cases rtInvCheck_row64
    (Fin.cases rtInvCheck_row65
    (Fin.cases rtInvCheck_row66
    (Fin.cases rtInvCheck_row67
    (Fin.cases rtInvCheck_row68
    (Fin.cases rtInvCheck_row69
    (Fin.cases rtInvCheck_row70
    (Fin.cases rtInvCheck_row71
    (Fin.cases rtInvCheck_row72
    (Fin.cases rtInvCheck_row73
    (Fin.cases rtInvCheck_row74
    (Fin.cases rtInvCheck_row75
    (Fin.cases rtInvCheck_row76
    (Fin.cases rtInvCheck_row77
    (Fin.cases rtInvCheck_row78
    (Fin.cases rtInvCheck_row79
    (Fin.cases rtInvCheck_row80
    (Fin.cases rtInvCheck_row81
    (Fin.cases rtInvCheck_row82
    (Fin.cases rtInvCheck_row83
    (Fin.cases rtInvCheck_row84
    (Fin.cases rtInvCheck_row85
    (Fin.cases rtInvCheck_row86
    (Fin.cases rtInvCheck_row87
    (Fin.cases rtInvCheck_row88
    (Fin.cases rtInvCheck_row89
    (Fin.cases rtInvCheck_row90
    (Fin.cases rtInvCheck_row91
    (Fin.cases rtInvCheck_row92
    (Fin.cases rtInvCheck_row93
    (Fin.cases rtInvCheck_row94
    (Fin.cases rtInvCheck_row95
    (Fin.cases rtInvCheck_row96
    (Fin.cases rtInvCheck_row97
    (Fin.cases rtInvCheck_row98
    (Fin.cases rtInvCheck_row99
    (Fin.cases rtInvCheck_row100
    (Fin.cases rtInvCheck_row101
    (Fin.cases rtInvCheck_row102
    (Fin.cases rtInvCheck_row103
    (Fin.cases rtInvCheck_row104
    (Fin.cases rtInvCheck_row105
    (Fin.cases rtInvCheck_row106
    (Fin.cases rtInvCheck_row107
    (Fin.cases rtInvCheck_row108
    (Fin.cases rtInvCheck_row109
    (Fin.cases rtInvCheck_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_rtInvCheck : rtInvMatrix * rtMatrix = oneMatrix :=
  decode_mul _ _ _ rtInv_small rt_small rtInvCheck_rows

end Lyons.Atlas111InvolutionWords
