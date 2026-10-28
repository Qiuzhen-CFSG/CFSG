module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: seedInvT times seed

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
private theorem u_row0 :
    digitsEq 111 (rowProduct (seedInvTRows 0) seedRows 111) (uRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row1 :
    digitsEq 111 (rowProduct (seedInvTRows 1) seedRows 111) (uRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row2 :
    digitsEq 111 (rowProduct (seedInvTRows 2) seedRows 111) (uRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row3 :
    digitsEq 111 (rowProduct (seedInvTRows 3) seedRows 111) (uRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row4 :
    digitsEq 111 (rowProduct (seedInvTRows 4) seedRows 111) (uRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row5 :
    digitsEq 111 (rowProduct (seedInvTRows 5) seedRows 111) (uRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row6 :
    digitsEq 111 (rowProduct (seedInvTRows 6) seedRows 111) (uRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row7 :
    digitsEq 111 (rowProduct (seedInvTRows 7) seedRows 111) (uRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row8 :
    digitsEq 111 (rowProduct (seedInvTRows 8) seedRows 111) (uRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row9 :
    digitsEq 111 (rowProduct (seedInvTRows 9) seedRows 111) (uRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row10 :
    digitsEq 111 (rowProduct (seedInvTRows 10) seedRows 111) (uRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row11 :
    digitsEq 111 (rowProduct (seedInvTRows 11) seedRows 111) (uRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row12 :
    digitsEq 111 (rowProduct (seedInvTRows 12) seedRows 111) (uRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row13 :
    digitsEq 111 (rowProduct (seedInvTRows 13) seedRows 111) (uRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row14 :
    digitsEq 111 (rowProduct (seedInvTRows 14) seedRows 111) (uRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row15 :
    digitsEq 111 (rowProduct (seedInvTRows 15) seedRows 111) (uRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row16 :
    digitsEq 111 (rowProduct (seedInvTRows 16) seedRows 111) (uRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row17 :
    digitsEq 111 (rowProduct (seedInvTRows 17) seedRows 111) (uRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row18 :
    digitsEq 111 (rowProduct (seedInvTRows 18) seedRows 111) (uRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row19 :
    digitsEq 111 (rowProduct (seedInvTRows 19) seedRows 111) (uRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row20 :
    digitsEq 111 (rowProduct (seedInvTRows 20) seedRows 111) (uRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row21 :
    digitsEq 111 (rowProduct (seedInvTRows 21) seedRows 111) (uRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row22 :
    digitsEq 111 (rowProduct (seedInvTRows 22) seedRows 111) (uRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row23 :
    digitsEq 111 (rowProduct (seedInvTRows 23) seedRows 111) (uRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row24 :
    digitsEq 111 (rowProduct (seedInvTRows 24) seedRows 111) (uRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row25 :
    digitsEq 111 (rowProduct (seedInvTRows 25) seedRows 111) (uRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row26 :
    digitsEq 111 (rowProduct (seedInvTRows 26) seedRows 111) (uRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row27 :
    digitsEq 111 (rowProduct (seedInvTRows 27) seedRows 111) (uRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row28 :
    digitsEq 111 (rowProduct (seedInvTRows 28) seedRows 111) (uRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row29 :
    digitsEq 111 (rowProduct (seedInvTRows 29) seedRows 111) (uRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row30 :
    digitsEq 111 (rowProduct (seedInvTRows 30) seedRows 111) (uRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row31 :
    digitsEq 111 (rowProduct (seedInvTRows 31) seedRows 111) (uRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row32 :
    digitsEq 111 (rowProduct (seedInvTRows 32) seedRows 111) (uRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row33 :
    digitsEq 111 (rowProduct (seedInvTRows 33) seedRows 111) (uRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row34 :
    digitsEq 111 (rowProduct (seedInvTRows 34) seedRows 111) (uRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row35 :
    digitsEq 111 (rowProduct (seedInvTRows 35) seedRows 111) (uRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row36 :
    digitsEq 111 (rowProduct (seedInvTRows 36) seedRows 111) (uRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row37 :
    digitsEq 111 (rowProduct (seedInvTRows 37) seedRows 111) (uRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row38 :
    digitsEq 111 (rowProduct (seedInvTRows 38) seedRows 111) (uRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row39 :
    digitsEq 111 (rowProduct (seedInvTRows 39) seedRows 111) (uRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row40 :
    digitsEq 111 (rowProduct (seedInvTRows 40) seedRows 111) (uRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row41 :
    digitsEq 111 (rowProduct (seedInvTRows 41) seedRows 111) (uRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row42 :
    digitsEq 111 (rowProduct (seedInvTRows 42) seedRows 111) (uRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row43 :
    digitsEq 111 (rowProduct (seedInvTRows 43) seedRows 111) (uRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row44 :
    digitsEq 111 (rowProduct (seedInvTRows 44) seedRows 111) (uRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row45 :
    digitsEq 111 (rowProduct (seedInvTRows 45) seedRows 111) (uRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row46 :
    digitsEq 111 (rowProduct (seedInvTRows 46) seedRows 111) (uRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row47 :
    digitsEq 111 (rowProduct (seedInvTRows 47) seedRows 111) (uRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row48 :
    digitsEq 111 (rowProduct (seedInvTRows 48) seedRows 111) (uRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row49 :
    digitsEq 111 (rowProduct (seedInvTRows 49) seedRows 111) (uRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row50 :
    digitsEq 111 (rowProduct (seedInvTRows 50) seedRows 111) (uRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row51 :
    digitsEq 111 (rowProduct (seedInvTRows 51) seedRows 111) (uRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row52 :
    digitsEq 111 (rowProduct (seedInvTRows 52) seedRows 111) (uRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row53 :
    digitsEq 111 (rowProduct (seedInvTRows 53) seedRows 111) (uRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row54 :
    digitsEq 111 (rowProduct (seedInvTRows 54) seedRows 111) (uRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row55 :
    digitsEq 111 (rowProduct (seedInvTRows 55) seedRows 111) (uRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row56 :
    digitsEq 111 (rowProduct (seedInvTRows 56) seedRows 111) (uRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row57 :
    digitsEq 111 (rowProduct (seedInvTRows 57) seedRows 111) (uRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row58 :
    digitsEq 111 (rowProduct (seedInvTRows 58) seedRows 111) (uRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row59 :
    digitsEq 111 (rowProduct (seedInvTRows 59) seedRows 111) (uRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row60 :
    digitsEq 111 (rowProduct (seedInvTRows 60) seedRows 111) (uRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row61 :
    digitsEq 111 (rowProduct (seedInvTRows 61) seedRows 111) (uRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row62 :
    digitsEq 111 (rowProduct (seedInvTRows 62) seedRows 111) (uRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row63 :
    digitsEq 111 (rowProduct (seedInvTRows 63) seedRows 111) (uRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row64 :
    digitsEq 111 (rowProduct (seedInvTRows 64) seedRows 111) (uRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row65 :
    digitsEq 111 (rowProduct (seedInvTRows 65) seedRows 111) (uRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row66 :
    digitsEq 111 (rowProduct (seedInvTRows 66) seedRows 111) (uRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row67 :
    digitsEq 111 (rowProduct (seedInvTRows 67) seedRows 111) (uRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row68 :
    digitsEq 111 (rowProduct (seedInvTRows 68) seedRows 111) (uRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row69 :
    digitsEq 111 (rowProduct (seedInvTRows 69) seedRows 111) (uRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row70 :
    digitsEq 111 (rowProduct (seedInvTRows 70) seedRows 111) (uRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row71 :
    digitsEq 111 (rowProduct (seedInvTRows 71) seedRows 111) (uRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row72 :
    digitsEq 111 (rowProduct (seedInvTRows 72) seedRows 111) (uRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row73 :
    digitsEq 111 (rowProduct (seedInvTRows 73) seedRows 111) (uRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row74 :
    digitsEq 111 (rowProduct (seedInvTRows 74) seedRows 111) (uRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row75 :
    digitsEq 111 (rowProduct (seedInvTRows 75) seedRows 111) (uRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row76 :
    digitsEq 111 (rowProduct (seedInvTRows 76) seedRows 111) (uRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row77 :
    digitsEq 111 (rowProduct (seedInvTRows 77) seedRows 111) (uRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row78 :
    digitsEq 111 (rowProduct (seedInvTRows 78) seedRows 111) (uRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row79 :
    digitsEq 111 (rowProduct (seedInvTRows 79) seedRows 111) (uRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row80 :
    digitsEq 111 (rowProduct (seedInvTRows 80) seedRows 111) (uRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row81 :
    digitsEq 111 (rowProduct (seedInvTRows 81) seedRows 111) (uRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row82 :
    digitsEq 111 (rowProduct (seedInvTRows 82) seedRows 111) (uRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row83 :
    digitsEq 111 (rowProduct (seedInvTRows 83) seedRows 111) (uRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row84 :
    digitsEq 111 (rowProduct (seedInvTRows 84) seedRows 111) (uRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row85 :
    digitsEq 111 (rowProduct (seedInvTRows 85) seedRows 111) (uRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row86 :
    digitsEq 111 (rowProduct (seedInvTRows 86) seedRows 111) (uRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row87 :
    digitsEq 111 (rowProduct (seedInvTRows 87) seedRows 111) (uRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row88 :
    digitsEq 111 (rowProduct (seedInvTRows 88) seedRows 111) (uRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row89 :
    digitsEq 111 (rowProduct (seedInvTRows 89) seedRows 111) (uRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row90 :
    digitsEq 111 (rowProduct (seedInvTRows 90) seedRows 111) (uRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row91 :
    digitsEq 111 (rowProduct (seedInvTRows 91) seedRows 111) (uRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row92 :
    digitsEq 111 (rowProduct (seedInvTRows 92) seedRows 111) (uRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row93 :
    digitsEq 111 (rowProduct (seedInvTRows 93) seedRows 111) (uRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row94 :
    digitsEq 111 (rowProduct (seedInvTRows 94) seedRows 111) (uRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row95 :
    digitsEq 111 (rowProduct (seedInvTRows 95) seedRows 111) (uRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row96 :
    digitsEq 111 (rowProduct (seedInvTRows 96) seedRows 111) (uRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row97 :
    digitsEq 111 (rowProduct (seedInvTRows 97) seedRows 111) (uRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row98 :
    digitsEq 111 (rowProduct (seedInvTRows 98) seedRows 111) (uRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row99 :
    digitsEq 111 (rowProduct (seedInvTRows 99) seedRows 111) (uRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row100 :
    digitsEq 111 (rowProduct (seedInvTRows 100) seedRows 111) (uRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row101 :
    digitsEq 111 (rowProduct (seedInvTRows 101) seedRows 111) (uRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row102 :
    digitsEq 111 (rowProduct (seedInvTRows 102) seedRows 111) (uRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row103 :
    digitsEq 111 (rowProduct (seedInvTRows 103) seedRows 111) (uRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row104 :
    digitsEq 111 (rowProduct (seedInvTRows 104) seedRows 111) (uRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row105 :
    digitsEq 111 (rowProduct (seedInvTRows 105) seedRows 111) (uRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row106 :
    digitsEq 111 (rowProduct (seedInvTRows 106) seedRows 111) (uRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row107 :
    digitsEq 111 (rowProduct (seedInvTRows 107) seedRows 111) (uRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row108 :
    digitsEq 111 (rowProduct (seedInvTRows 108) seedRows 111) (uRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row109 :
    digitsEq 111 (rowProduct (seedInvTRows 109) seedRows 111) (uRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem u_row110 :
    digitsEq 111 (rowProduct (seedInvTRows 110) seedRows 111) (uRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem u_rows : ∀ i,
    digitsEq 111 (rowProduct (seedInvTRows i) seedRows 111) (uRows i) = true :=
  (Fin.cases u_row0
    (Fin.cases u_row1
    (Fin.cases u_row2
    (Fin.cases u_row3
    (Fin.cases u_row4
    (Fin.cases u_row5
    (Fin.cases u_row6
    (Fin.cases u_row7
    (Fin.cases u_row8
    (Fin.cases u_row9
    (Fin.cases u_row10
    (Fin.cases u_row11
    (Fin.cases u_row12
    (Fin.cases u_row13
    (Fin.cases u_row14
    (Fin.cases u_row15
    (Fin.cases u_row16
    (Fin.cases u_row17
    (Fin.cases u_row18
    (Fin.cases u_row19
    (Fin.cases u_row20
    (Fin.cases u_row21
    (Fin.cases u_row22
    (Fin.cases u_row23
    (Fin.cases u_row24
    (Fin.cases u_row25
    (Fin.cases u_row26
    (Fin.cases u_row27
    (Fin.cases u_row28
    (Fin.cases u_row29
    (Fin.cases u_row30
    (Fin.cases u_row31
    (Fin.cases u_row32
    (Fin.cases u_row33
    (Fin.cases u_row34
    (Fin.cases u_row35
    (Fin.cases u_row36
    (Fin.cases u_row37
    (Fin.cases u_row38
    (Fin.cases u_row39
    (Fin.cases u_row40
    (Fin.cases u_row41
    (Fin.cases u_row42
    (Fin.cases u_row43
    (Fin.cases u_row44
    (Fin.cases u_row45
    (Fin.cases u_row46
    (Fin.cases u_row47
    (Fin.cases u_row48
    (Fin.cases u_row49
    (Fin.cases u_row50
    (Fin.cases u_row51
    (Fin.cases u_row52
    (Fin.cases u_row53
    (Fin.cases u_row54
    (Fin.cases u_row55
    (Fin.cases u_row56
    (Fin.cases u_row57
    (Fin.cases u_row58
    (Fin.cases u_row59
    (Fin.cases u_row60
    (Fin.cases u_row61
    (Fin.cases u_row62
    (Fin.cases u_row63
    (Fin.cases u_row64
    (Fin.cases u_row65
    (Fin.cases u_row66
    (Fin.cases u_row67
    (Fin.cases u_row68
    (Fin.cases u_row69
    (Fin.cases u_row70
    (Fin.cases u_row71
    (Fin.cases u_row72
    (Fin.cases u_row73
    (Fin.cases u_row74
    (Fin.cases u_row75
    (Fin.cases u_row76
    (Fin.cases u_row77
    (Fin.cases u_row78
    (Fin.cases u_row79
    (Fin.cases u_row80
    (Fin.cases u_row81
    (Fin.cases u_row82
    (Fin.cases u_row83
    (Fin.cases u_row84
    (Fin.cases u_row85
    (Fin.cases u_row86
    (Fin.cases u_row87
    (Fin.cases u_row88
    (Fin.cases u_row89
    (Fin.cases u_row90
    (Fin.cases u_row91
    (Fin.cases u_row92
    (Fin.cases u_row93
    (Fin.cases u_row94
    (Fin.cases u_row95
    (Fin.cases u_row96
    (Fin.cases u_row97
    (Fin.cases u_row98
    (Fin.cases u_row99
    (Fin.cases u_row100
    (Fin.cases u_row101
    (Fin.cases u_row102
    (Fin.cases u_row103
    (Fin.cases u_row104
    (Fin.cases u_row105
    (Fin.cases u_row106
    (Fin.cases u_row107
    (Fin.cases u_row108
    (Fin.cases u_row109
    (Fin.cases u_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_u : seedInvTMatrix * seedMatrix = uMatrix :=
  decode_mul _ _ _ seedInvT_small seed_small u_rows

end Lyons.Atlas111InvolutionWords
