module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: seedInv times seed

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
private theorem seedInvCheck_row0 :
    digitsEq 111 (rowProduct (seedInvRows 0) seedRows 111) (oneRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row1 :
    digitsEq 111 (rowProduct (seedInvRows 1) seedRows 111) (oneRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row2 :
    digitsEq 111 (rowProduct (seedInvRows 2) seedRows 111) (oneRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row3 :
    digitsEq 111 (rowProduct (seedInvRows 3) seedRows 111) (oneRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row4 :
    digitsEq 111 (rowProduct (seedInvRows 4) seedRows 111) (oneRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row5 :
    digitsEq 111 (rowProduct (seedInvRows 5) seedRows 111) (oneRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row6 :
    digitsEq 111 (rowProduct (seedInvRows 6) seedRows 111) (oneRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row7 :
    digitsEq 111 (rowProduct (seedInvRows 7) seedRows 111) (oneRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row8 :
    digitsEq 111 (rowProduct (seedInvRows 8) seedRows 111) (oneRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row9 :
    digitsEq 111 (rowProduct (seedInvRows 9) seedRows 111) (oneRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row10 :
    digitsEq 111 (rowProduct (seedInvRows 10) seedRows 111) (oneRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row11 :
    digitsEq 111 (rowProduct (seedInvRows 11) seedRows 111) (oneRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row12 :
    digitsEq 111 (rowProduct (seedInvRows 12) seedRows 111) (oneRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row13 :
    digitsEq 111 (rowProduct (seedInvRows 13) seedRows 111) (oneRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row14 :
    digitsEq 111 (rowProduct (seedInvRows 14) seedRows 111) (oneRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row15 :
    digitsEq 111 (rowProduct (seedInvRows 15) seedRows 111) (oneRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row16 :
    digitsEq 111 (rowProduct (seedInvRows 16) seedRows 111) (oneRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row17 :
    digitsEq 111 (rowProduct (seedInvRows 17) seedRows 111) (oneRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row18 :
    digitsEq 111 (rowProduct (seedInvRows 18) seedRows 111) (oneRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row19 :
    digitsEq 111 (rowProduct (seedInvRows 19) seedRows 111) (oneRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row20 :
    digitsEq 111 (rowProduct (seedInvRows 20) seedRows 111) (oneRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row21 :
    digitsEq 111 (rowProduct (seedInvRows 21) seedRows 111) (oneRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row22 :
    digitsEq 111 (rowProduct (seedInvRows 22) seedRows 111) (oneRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row23 :
    digitsEq 111 (rowProduct (seedInvRows 23) seedRows 111) (oneRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row24 :
    digitsEq 111 (rowProduct (seedInvRows 24) seedRows 111) (oneRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row25 :
    digitsEq 111 (rowProduct (seedInvRows 25) seedRows 111) (oneRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row26 :
    digitsEq 111 (rowProduct (seedInvRows 26) seedRows 111) (oneRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row27 :
    digitsEq 111 (rowProduct (seedInvRows 27) seedRows 111) (oneRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row28 :
    digitsEq 111 (rowProduct (seedInvRows 28) seedRows 111) (oneRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row29 :
    digitsEq 111 (rowProduct (seedInvRows 29) seedRows 111) (oneRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row30 :
    digitsEq 111 (rowProduct (seedInvRows 30) seedRows 111) (oneRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row31 :
    digitsEq 111 (rowProduct (seedInvRows 31) seedRows 111) (oneRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row32 :
    digitsEq 111 (rowProduct (seedInvRows 32) seedRows 111) (oneRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row33 :
    digitsEq 111 (rowProduct (seedInvRows 33) seedRows 111) (oneRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row34 :
    digitsEq 111 (rowProduct (seedInvRows 34) seedRows 111) (oneRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row35 :
    digitsEq 111 (rowProduct (seedInvRows 35) seedRows 111) (oneRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row36 :
    digitsEq 111 (rowProduct (seedInvRows 36) seedRows 111) (oneRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row37 :
    digitsEq 111 (rowProduct (seedInvRows 37) seedRows 111) (oneRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row38 :
    digitsEq 111 (rowProduct (seedInvRows 38) seedRows 111) (oneRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row39 :
    digitsEq 111 (rowProduct (seedInvRows 39) seedRows 111) (oneRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row40 :
    digitsEq 111 (rowProduct (seedInvRows 40) seedRows 111) (oneRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row41 :
    digitsEq 111 (rowProduct (seedInvRows 41) seedRows 111) (oneRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row42 :
    digitsEq 111 (rowProduct (seedInvRows 42) seedRows 111) (oneRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row43 :
    digitsEq 111 (rowProduct (seedInvRows 43) seedRows 111) (oneRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row44 :
    digitsEq 111 (rowProduct (seedInvRows 44) seedRows 111) (oneRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row45 :
    digitsEq 111 (rowProduct (seedInvRows 45) seedRows 111) (oneRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row46 :
    digitsEq 111 (rowProduct (seedInvRows 46) seedRows 111) (oneRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row47 :
    digitsEq 111 (rowProduct (seedInvRows 47) seedRows 111) (oneRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row48 :
    digitsEq 111 (rowProduct (seedInvRows 48) seedRows 111) (oneRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row49 :
    digitsEq 111 (rowProduct (seedInvRows 49) seedRows 111) (oneRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row50 :
    digitsEq 111 (rowProduct (seedInvRows 50) seedRows 111) (oneRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row51 :
    digitsEq 111 (rowProduct (seedInvRows 51) seedRows 111) (oneRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row52 :
    digitsEq 111 (rowProduct (seedInvRows 52) seedRows 111) (oneRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row53 :
    digitsEq 111 (rowProduct (seedInvRows 53) seedRows 111) (oneRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row54 :
    digitsEq 111 (rowProduct (seedInvRows 54) seedRows 111) (oneRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row55 :
    digitsEq 111 (rowProduct (seedInvRows 55) seedRows 111) (oneRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row56 :
    digitsEq 111 (rowProduct (seedInvRows 56) seedRows 111) (oneRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row57 :
    digitsEq 111 (rowProduct (seedInvRows 57) seedRows 111) (oneRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row58 :
    digitsEq 111 (rowProduct (seedInvRows 58) seedRows 111) (oneRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row59 :
    digitsEq 111 (rowProduct (seedInvRows 59) seedRows 111) (oneRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row60 :
    digitsEq 111 (rowProduct (seedInvRows 60) seedRows 111) (oneRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row61 :
    digitsEq 111 (rowProduct (seedInvRows 61) seedRows 111) (oneRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row62 :
    digitsEq 111 (rowProduct (seedInvRows 62) seedRows 111) (oneRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row63 :
    digitsEq 111 (rowProduct (seedInvRows 63) seedRows 111) (oneRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row64 :
    digitsEq 111 (rowProduct (seedInvRows 64) seedRows 111) (oneRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row65 :
    digitsEq 111 (rowProduct (seedInvRows 65) seedRows 111) (oneRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row66 :
    digitsEq 111 (rowProduct (seedInvRows 66) seedRows 111) (oneRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row67 :
    digitsEq 111 (rowProduct (seedInvRows 67) seedRows 111) (oneRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row68 :
    digitsEq 111 (rowProduct (seedInvRows 68) seedRows 111) (oneRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row69 :
    digitsEq 111 (rowProduct (seedInvRows 69) seedRows 111) (oneRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row70 :
    digitsEq 111 (rowProduct (seedInvRows 70) seedRows 111) (oneRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row71 :
    digitsEq 111 (rowProduct (seedInvRows 71) seedRows 111) (oneRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row72 :
    digitsEq 111 (rowProduct (seedInvRows 72) seedRows 111) (oneRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row73 :
    digitsEq 111 (rowProduct (seedInvRows 73) seedRows 111) (oneRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row74 :
    digitsEq 111 (rowProduct (seedInvRows 74) seedRows 111) (oneRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row75 :
    digitsEq 111 (rowProduct (seedInvRows 75) seedRows 111) (oneRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row76 :
    digitsEq 111 (rowProduct (seedInvRows 76) seedRows 111) (oneRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row77 :
    digitsEq 111 (rowProduct (seedInvRows 77) seedRows 111) (oneRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row78 :
    digitsEq 111 (rowProduct (seedInvRows 78) seedRows 111) (oneRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row79 :
    digitsEq 111 (rowProduct (seedInvRows 79) seedRows 111) (oneRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row80 :
    digitsEq 111 (rowProduct (seedInvRows 80) seedRows 111) (oneRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row81 :
    digitsEq 111 (rowProduct (seedInvRows 81) seedRows 111) (oneRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row82 :
    digitsEq 111 (rowProduct (seedInvRows 82) seedRows 111) (oneRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row83 :
    digitsEq 111 (rowProduct (seedInvRows 83) seedRows 111) (oneRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row84 :
    digitsEq 111 (rowProduct (seedInvRows 84) seedRows 111) (oneRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row85 :
    digitsEq 111 (rowProduct (seedInvRows 85) seedRows 111) (oneRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row86 :
    digitsEq 111 (rowProduct (seedInvRows 86) seedRows 111) (oneRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row87 :
    digitsEq 111 (rowProduct (seedInvRows 87) seedRows 111) (oneRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row88 :
    digitsEq 111 (rowProduct (seedInvRows 88) seedRows 111) (oneRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row89 :
    digitsEq 111 (rowProduct (seedInvRows 89) seedRows 111) (oneRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row90 :
    digitsEq 111 (rowProduct (seedInvRows 90) seedRows 111) (oneRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row91 :
    digitsEq 111 (rowProduct (seedInvRows 91) seedRows 111) (oneRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row92 :
    digitsEq 111 (rowProduct (seedInvRows 92) seedRows 111) (oneRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row93 :
    digitsEq 111 (rowProduct (seedInvRows 93) seedRows 111) (oneRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row94 :
    digitsEq 111 (rowProduct (seedInvRows 94) seedRows 111) (oneRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row95 :
    digitsEq 111 (rowProduct (seedInvRows 95) seedRows 111) (oneRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row96 :
    digitsEq 111 (rowProduct (seedInvRows 96) seedRows 111) (oneRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row97 :
    digitsEq 111 (rowProduct (seedInvRows 97) seedRows 111) (oneRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row98 :
    digitsEq 111 (rowProduct (seedInvRows 98) seedRows 111) (oneRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row99 :
    digitsEq 111 (rowProduct (seedInvRows 99) seedRows 111) (oneRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row100 :
    digitsEq 111 (rowProduct (seedInvRows 100) seedRows 111) (oneRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row101 :
    digitsEq 111 (rowProduct (seedInvRows 101) seedRows 111) (oneRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row102 :
    digitsEq 111 (rowProduct (seedInvRows 102) seedRows 111) (oneRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row103 :
    digitsEq 111 (rowProduct (seedInvRows 103) seedRows 111) (oneRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row104 :
    digitsEq 111 (rowProduct (seedInvRows 104) seedRows 111) (oneRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row105 :
    digitsEq 111 (rowProduct (seedInvRows 105) seedRows 111) (oneRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row106 :
    digitsEq 111 (rowProduct (seedInvRows 106) seedRows 111) (oneRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row107 :
    digitsEq 111 (rowProduct (seedInvRows 107) seedRows 111) (oneRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row108 :
    digitsEq 111 (rowProduct (seedInvRows 108) seedRows 111) (oneRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row109 :
    digitsEq 111 (rowProduct (seedInvRows 109) seedRows 111) (oneRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvCheck_row110 :
    digitsEq 111 (rowProduct (seedInvRows 110) seedRows 111) (oneRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem seedInvCheck_rows : ∀ i,
    digitsEq 111 (rowProduct (seedInvRows i) seedRows 111) (oneRows i) = true :=
  (Fin.cases seedInvCheck_row0
    (Fin.cases seedInvCheck_row1
    (Fin.cases seedInvCheck_row2
    (Fin.cases seedInvCheck_row3
    (Fin.cases seedInvCheck_row4
    (Fin.cases seedInvCheck_row5
    (Fin.cases seedInvCheck_row6
    (Fin.cases seedInvCheck_row7
    (Fin.cases seedInvCheck_row8
    (Fin.cases seedInvCheck_row9
    (Fin.cases seedInvCheck_row10
    (Fin.cases seedInvCheck_row11
    (Fin.cases seedInvCheck_row12
    (Fin.cases seedInvCheck_row13
    (Fin.cases seedInvCheck_row14
    (Fin.cases seedInvCheck_row15
    (Fin.cases seedInvCheck_row16
    (Fin.cases seedInvCheck_row17
    (Fin.cases seedInvCheck_row18
    (Fin.cases seedInvCheck_row19
    (Fin.cases seedInvCheck_row20
    (Fin.cases seedInvCheck_row21
    (Fin.cases seedInvCheck_row22
    (Fin.cases seedInvCheck_row23
    (Fin.cases seedInvCheck_row24
    (Fin.cases seedInvCheck_row25
    (Fin.cases seedInvCheck_row26
    (Fin.cases seedInvCheck_row27
    (Fin.cases seedInvCheck_row28
    (Fin.cases seedInvCheck_row29
    (Fin.cases seedInvCheck_row30
    (Fin.cases seedInvCheck_row31
    (Fin.cases seedInvCheck_row32
    (Fin.cases seedInvCheck_row33
    (Fin.cases seedInvCheck_row34
    (Fin.cases seedInvCheck_row35
    (Fin.cases seedInvCheck_row36
    (Fin.cases seedInvCheck_row37
    (Fin.cases seedInvCheck_row38
    (Fin.cases seedInvCheck_row39
    (Fin.cases seedInvCheck_row40
    (Fin.cases seedInvCheck_row41
    (Fin.cases seedInvCheck_row42
    (Fin.cases seedInvCheck_row43
    (Fin.cases seedInvCheck_row44
    (Fin.cases seedInvCheck_row45
    (Fin.cases seedInvCheck_row46
    (Fin.cases seedInvCheck_row47
    (Fin.cases seedInvCheck_row48
    (Fin.cases seedInvCheck_row49
    (Fin.cases seedInvCheck_row50
    (Fin.cases seedInvCheck_row51
    (Fin.cases seedInvCheck_row52
    (Fin.cases seedInvCheck_row53
    (Fin.cases seedInvCheck_row54
    (Fin.cases seedInvCheck_row55
    (Fin.cases seedInvCheck_row56
    (Fin.cases seedInvCheck_row57
    (Fin.cases seedInvCheck_row58
    (Fin.cases seedInvCheck_row59
    (Fin.cases seedInvCheck_row60
    (Fin.cases seedInvCheck_row61
    (Fin.cases seedInvCheck_row62
    (Fin.cases seedInvCheck_row63
    (Fin.cases seedInvCheck_row64
    (Fin.cases seedInvCheck_row65
    (Fin.cases seedInvCheck_row66
    (Fin.cases seedInvCheck_row67
    (Fin.cases seedInvCheck_row68
    (Fin.cases seedInvCheck_row69
    (Fin.cases seedInvCheck_row70
    (Fin.cases seedInvCheck_row71
    (Fin.cases seedInvCheck_row72
    (Fin.cases seedInvCheck_row73
    (Fin.cases seedInvCheck_row74
    (Fin.cases seedInvCheck_row75
    (Fin.cases seedInvCheck_row76
    (Fin.cases seedInvCheck_row77
    (Fin.cases seedInvCheck_row78
    (Fin.cases seedInvCheck_row79
    (Fin.cases seedInvCheck_row80
    (Fin.cases seedInvCheck_row81
    (Fin.cases seedInvCheck_row82
    (Fin.cases seedInvCheck_row83
    (Fin.cases seedInvCheck_row84
    (Fin.cases seedInvCheck_row85
    (Fin.cases seedInvCheck_row86
    (Fin.cases seedInvCheck_row87
    (Fin.cases seedInvCheck_row88
    (Fin.cases seedInvCheck_row89
    (Fin.cases seedInvCheck_row90
    (Fin.cases seedInvCheck_row91
    (Fin.cases seedInvCheck_row92
    (Fin.cases seedInvCheck_row93
    (Fin.cases seedInvCheck_row94
    (Fin.cases seedInvCheck_row95
    (Fin.cases seedInvCheck_row96
    (Fin.cases seedInvCheck_row97
    (Fin.cases seedInvCheck_row98
    (Fin.cases seedInvCheck_row99
    (Fin.cases seedInvCheck_row100
    (Fin.cases seedInvCheck_row101
    (Fin.cases seedInvCheck_row102
    (Fin.cases seedInvCheck_row103
    (Fin.cases seedInvCheck_row104
    (Fin.cases seedInvCheck_row105
    (Fin.cases seedInvCheck_row106
    (Fin.cases seedInvCheck_row107
    (Fin.cases seedInvCheck_row108
    (Fin.cases seedInvCheck_row109
    (Fin.cases seedInvCheck_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_seedInvCheck : seedInvMatrix * seedMatrix = oneMatrix :=
  decode_mul _ _ _ seedInv_small seed_small seedInvCheck_rows

end Lyons.Atlas111InvolutionWords
