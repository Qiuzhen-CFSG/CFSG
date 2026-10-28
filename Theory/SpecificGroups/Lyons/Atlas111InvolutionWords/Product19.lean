module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: seedInv times ab7

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
private theorem seedInvT_row0 :
    digitsEq 111 (rowProduct (seedInvRows 0) ab7Rows 111) (seedInvTRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row1 :
    digitsEq 111 (rowProduct (seedInvRows 1) ab7Rows 111) (seedInvTRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row2 :
    digitsEq 111 (rowProduct (seedInvRows 2) ab7Rows 111) (seedInvTRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row3 :
    digitsEq 111 (rowProduct (seedInvRows 3) ab7Rows 111) (seedInvTRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row4 :
    digitsEq 111 (rowProduct (seedInvRows 4) ab7Rows 111) (seedInvTRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row5 :
    digitsEq 111 (rowProduct (seedInvRows 5) ab7Rows 111) (seedInvTRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row6 :
    digitsEq 111 (rowProduct (seedInvRows 6) ab7Rows 111) (seedInvTRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row7 :
    digitsEq 111 (rowProduct (seedInvRows 7) ab7Rows 111) (seedInvTRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row8 :
    digitsEq 111 (rowProduct (seedInvRows 8) ab7Rows 111) (seedInvTRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row9 :
    digitsEq 111 (rowProduct (seedInvRows 9) ab7Rows 111) (seedInvTRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row10 :
    digitsEq 111 (rowProduct (seedInvRows 10) ab7Rows 111) (seedInvTRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row11 :
    digitsEq 111 (rowProduct (seedInvRows 11) ab7Rows 111) (seedInvTRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row12 :
    digitsEq 111 (rowProduct (seedInvRows 12) ab7Rows 111) (seedInvTRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row13 :
    digitsEq 111 (rowProduct (seedInvRows 13) ab7Rows 111) (seedInvTRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row14 :
    digitsEq 111 (rowProduct (seedInvRows 14) ab7Rows 111) (seedInvTRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row15 :
    digitsEq 111 (rowProduct (seedInvRows 15) ab7Rows 111) (seedInvTRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row16 :
    digitsEq 111 (rowProduct (seedInvRows 16) ab7Rows 111) (seedInvTRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row17 :
    digitsEq 111 (rowProduct (seedInvRows 17) ab7Rows 111) (seedInvTRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row18 :
    digitsEq 111 (rowProduct (seedInvRows 18) ab7Rows 111) (seedInvTRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row19 :
    digitsEq 111 (rowProduct (seedInvRows 19) ab7Rows 111) (seedInvTRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row20 :
    digitsEq 111 (rowProduct (seedInvRows 20) ab7Rows 111) (seedInvTRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row21 :
    digitsEq 111 (rowProduct (seedInvRows 21) ab7Rows 111) (seedInvTRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row22 :
    digitsEq 111 (rowProduct (seedInvRows 22) ab7Rows 111) (seedInvTRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row23 :
    digitsEq 111 (rowProduct (seedInvRows 23) ab7Rows 111) (seedInvTRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row24 :
    digitsEq 111 (rowProduct (seedInvRows 24) ab7Rows 111) (seedInvTRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row25 :
    digitsEq 111 (rowProduct (seedInvRows 25) ab7Rows 111) (seedInvTRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row26 :
    digitsEq 111 (rowProduct (seedInvRows 26) ab7Rows 111) (seedInvTRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row27 :
    digitsEq 111 (rowProduct (seedInvRows 27) ab7Rows 111) (seedInvTRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row28 :
    digitsEq 111 (rowProduct (seedInvRows 28) ab7Rows 111) (seedInvTRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row29 :
    digitsEq 111 (rowProduct (seedInvRows 29) ab7Rows 111) (seedInvTRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row30 :
    digitsEq 111 (rowProduct (seedInvRows 30) ab7Rows 111) (seedInvTRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row31 :
    digitsEq 111 (rowProduct (seedInvRows 31) ab7Rows 111) (seedInvTRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row32 :
    digitsEq 111 (rowProduct (seedInvRows 32) ab7Rows 111) (seedInvTRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row33 :
    digitsEq 111 (rowProduct (seedInvRows 33) ab7Rows 111) (seedInvTRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row34 :
    digitsEq 111 (rowProduct (seedInvRows 34) ab7Rows 111) (seedInvTRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row35 :
    digitsEq 111 (rowProduct (seedInvRows 35) ab7Rows 111) (seedInvTRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row36 :
    digitsEq 111 (rowProduct (seedInvRows 36) ab7Rows 111) (seedInvTRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row37 :
    digitsEq 111 (rowProduct (seedInvRows 37) ab7Rows 111) (seedInvTRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row38 :
    digitsEq 111 (rowProduct (seedInvRows 38) ab7Rows 111) (seedInvTRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row39 :
    digitsEq 111 (rowProduct (seedInvRows 39) ab7Rows 111) (seedInvTRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row40 :
    digitsEq 111 (rowProduct (seedInvRows 40) ab7Rows 111) (seedInvTRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row41 :
    digitsEq 111 (rowProduct (seedInvRows 41) ab7Rows 111) (seedInvTRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row42 :
    digitsEq 111 (rowProduct (seedInvRows 42) ab7Rows 111) (seedInvTRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row43 :
    digitsEq 111 (rowProduct (seedInvRows 43) ab7Rows 111) (seedInvTRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row44 :
    digitsEq 111 (rowProduct (seedInvRows 44) ab7Rows 111) (seedInvTRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row45 :
    digitsEq 111 (rowProduct (seedInvRows 45) ab7Rows 111) (seedInvTRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row46 :
    digitsEq 111 (rowProduct (seedInvRows 46) ab7Rows 111) (seedInvTRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row47 :
    digitsEq 111 (rowProduct (seedInvRows 47) ab7Rows 111) (seedInvTRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row48 :
    digitsEq 111 (rowProduct (seedInvRows 48) ab7Rows 111) (seedInvTRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row49 :
    digitsEq 111 (rowProduct (seedInvRows 49) ab7Rows 111) (seedInvTRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row50 :
    digitsEq 111 (rowProduct (seedInvRows 50) ab7Rows 111) (seedInvTRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row51 :
    digitsEq 111 (rowProduct (seedInvRows 51) ab7Rows 111) (seedInvTRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row52 :
    digitsEq 111 (rowProduct (seedInvRows 52) ab7Rows 111) (seedInvTRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row53 :
    digitsEq 111 (rowProduct (seedInvRows 53) ab7Rows 111) (seedInvTRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row54 :
    digitsEq 111 (rowProduct (seedInvRows 54) ab7Rows 111) (seedInvTRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row55 :
    digitsEq 111 (rowProduct (seedInvRows 55) ab7Rows 111) (seedInvTRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row56 :
    digitsEq 111 (rowProduct (seedInvRows 56) ab7Rows 111) (seedInvTRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row57 :
    digitsEq 111 (rowProduct (seedInvRows 57) ab7Rows 111) (seedInvTRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row58 :
    digitsEq 111 (rowProduct (seedInvRows 58) ab7Rows 111) (seedInvTRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row59 :
    digitsEq 111 (rowProduct (seedInvRows 59) ab7Rows 111) (seedInvTRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row60 :
    digitsEq 111 (rowProduct (seedInvRows 60) ab7Rows 111) (seedInvTRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row61 :
    digitsEq 111 (rowProduct (seedInvRows 61) ab7Rows 111) (seedInvTRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row62 :
    digitsEq 111 (rowProduct (seedInvRows 62) ab7Rows 111) (seedInvTRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row63 :
    digitsEq 111 (rowProduct (seedInvRows 63) ab7Rows 111) (seedInvTRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row64 :
    digitsEq 111 (rowProduct (seedInvRows 64) ab7Rows 111) (seedInvTRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row65 :
    digitsEq 111 (rowProduct (seedInvRows 65) ab7Rows 111) (seedInvTRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row66 :
    digitsEq 111 (rowProduct (seedInvRows 66) ab7Rows 111) (seedInvTRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row67 :
    digitsEq 111 (rowProduct (seedInvRows 67) ab7Rows 111) (seedInvTRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row68 :
    digitsEq 111 (rowProduct (seedInvRows 68) ab7Rows 111) (seedInvTRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row69 :
    digitsEq 111 (rowProduct (seedInvRows 69) ab7Rows 111) (seedInvTRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row70 :
    digitsEq 111 (rowProduct (seedInvRows 70) ab7Rows 111) (seedInvTRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row71 :
    digitsEq 111 (rowProduct (seedInvRows 71) ab7Rows 111) (seedInvTRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row72 :
    digitsEq 111 (rowProduct (seedInvRows 72) ab7Rows 111) (seedInvTRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row73 :
    digitsEq 111 (rowProduct (seedInvRows 73) ab7Rows 111) (seedInvTRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row74 :
    digitsEq 111 (rowProduct (seedInvRows 74) ab7Rows 111) (seedInvTRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row75 :
    digitsEq 111 (rowProduct (seedInvRows 75) ab7Rows 111) (seedInvTRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row76 :
    digitsEq 111 (rowProduct (seedInvRows 76) ab7Rows 111) (seedInvTRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row77 :
    digitsEq 111 (rowProduct (seedInvRows 77) ab7Rows 111) (seedInvTRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row78 :
    digitsEq 111 (rowProduct (seedInvRows 78) ab7Rows 111) (seedInvTRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row79 :
    digitsEq 111 (rowProduct (seedInvRows 79) ab7Rows 111) (seedInvTRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row80 :
    digitsEq 111 (rowProduct (seedInvRows 80) ab7Rows 111) (seedInvTRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row81 :
    digitsEq 111 (rowProduct (seedInvRows 81) ab7Rows 111) (seedInvTRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row82 :
    digitsEq 111 (rowProduct (seedInvRows 82) ab7Rows 111) (seedInvTRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row83 :
    digitsEq 111 (rowProduct (seedInvRows 83) ab7Rows 111) (seedInvTRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row84 :
    digitsEq 111 (rowProduct (seedInvRows 84) ab7Rows 111) (seedInvTRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row85 :
    digitsEq 111 (rowProduct (seedInvRows 85) ab7Rows 111) (seedInvTRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row86 :
    digitsEq 111 (rowProduct (seedInvRows 86) ab7Rows 111) (seedInvTRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row87 :
    digitsEq 111 (rowProduct (seedInvRows 87) ab7Rows 111) (seedInvTRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row88 :
    digitsEq 111 (rowProduct (seedInvRows 88) ab7Rows 111) (seedInvTRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row89 :
    digitsEq 111 (rowProduct (seedInvRows 89) ab7Rows 111) (seedInvTRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row90 :
    digitsEq 111 (rowProduct (seedInvRows 90) ab7Rows 111) (seedInvTRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row91 :
    digitsEq 111 (rowProduct (seedInvRows 91) ab7Rows 111) (seedInvTRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row92 :
    digitsEq 111 (rowProduct (seedInvRows 92) ab7Rows 111) (seedInvTRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row93 :
    digitsEq 111 (rowProduct (seedInvRows 93) ab7Rows 111) (seedInvTRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row94 :
    digitsEq 111 (rowProduct (seedInvRows 94) ab7Rows 111) (seedInvTRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row95 :
    digitsEq 111 (rowProduct (seedInvRows 95) ab7Rows 111) (seedInvTRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row96 :
    digitsEq 111 (rowProduct (seedInvRows 96) ab7Rows 111) (seedInvTRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row97 :
    digitsEq 111 (rowProduct (seedInvRows 97) ab7Rows 111) (seedInvTRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row98 :
    digitsEq 111 (rowProduct (seedInvRows 98) ab7Rows 111) (seedInvTRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row99 :
    digitsEq 111 (rowProduct (seedInvRows 99) ab7Rows 111) (seedInvTRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row100 :
    digitsEq 111 (rowProduct (seedInvRows 100) ab7Rows 111) (seedInvTRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row101 :
    digitsEq 111 (rowProduct (seedInvRows 101) ab7Rows 111) (seedInvTRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row102 :
    digitsEq 111 (rowProduct (seedInvRows 102) ab7Rows 111) (seedInvTRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row103 :
    digitsEq 111 (rowProduct (seedInvRows 103) ab7Rows 111) (seedInvTRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row104 :
    digitsEq 111 (rowProduct (seedInvRows 104) ab7Rows 111) (seedInvTRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row105 :
    digitsEq 111 (rowProduct (seedInvRows 105) ab7Rows 111) (seedInvTRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row106 :
    digitsEq 111 (rowProduct (seedInvRows 106) ab7Rows 111) (seedInvTRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row107 :
    digitsEq 111 (rowProduct (seedInvRows 107) ab7Rows 111) (seedInvTRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row108 :
    digitsEq 111 (rowProduct (seedInvRows 108) ab7Rows 111) (seedInvTRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row109 :
    digitsEq 111 (rowProduct (seedInvRows 109) ab7Rows 111) (seedInvTRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seedInvT_row110 :
    digitsEq 111 (rowProduct (seedInvRows 110) ab7Rows 111) (seedInvTRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem seedInvT_rows : ∀ i,
    digitsEq 111 (rowProduct (seedInvRows i) ab7Rows 111) (seedInvTRows i) = true :=
  (Fin.cases seedInvT_row0
    (Fin.cases seedInvT_row1
    (Fin.cases seedInvT_row2
    (Fin.cases seedInvT_row3
    (Fin.cases seedInvT_row4
    (Fin.cases seedInvT_row5
    (Fin.cases seedInvT_row6
    (Fin.cases seedInvT_row7
    (Fin.cases seedInvT_row8
    (Fin.cases seedInvT_row9
    (Fin.cases seedInvT_row10
    (Fin.cases seedInvT_row11
    (Fin.cases seedInvT_row12
    (Fin.cases seedInvT_row13
    (Fin.cases seedInvT_row14
    (Fin.cases seedInvT_row15
    (Fin.cases seedInvT_row16
    (Fin.cases seedInvT_row17
    (Fin.cases seedInvT_row18
    (Fin.cases seedInvT_row19
    (Fin.cases seedInvT_row20
    (Fin.cases seedInvT_row21
    (Fin.cases seedInvT_row22
    (Fin.cases seedInvT_row23
    (Fin.cases seedInvT_row24
    (Fin.cases seedInvT_row25
    (Fin.cases seedInvT_row26
    (Fin.cases seedInvT_row27
    (Fin.cases seedInvT_row28
    (Fin.cases seedInvT_row29
    (Fin.cases seedInvT_row30
    (Fin.cases seedInvT_row31
    (Fin.cases seedInvT_row32
    (Fin.cases seedInvT_row33
    (Fin.cases seedInvT_row34
    (Fin.cases seedInvT_row35
    (Fin.cases seedInvT_row36
    (Fin.cases seedInvT_row37
    (Fin.cases seedInvT_row38
    (Fin.cases seedInvT_row39
    (Fin.cases seedInvT_row40
    (Fin.cases seedInvT_row41
    (Fin.cases seedInvT_row42
    (Fin.cases seedInvT_row43
    (Fin.cases seedInvT_row44
    (Fin.cases seedInvT_row45
    (Fin.cases seedInvT_row46
    (Fin.cases seedInvT_row47
    (Fin.cases seedInvT_row48
    (Fin.cases seedInvT_row49
    (Fin.cases seedInvT_row50
    (Fin.cases seedInvT_row51
    (Fin.cases seedInvT_row52
    (Fin.cases seedInvT_row53
    (Fin.cases seedInvT_row54
    (Fin.cases seedInvT_row55
    (Fin.cases seedInvT_row56
    (Fin.cases seedInvT_row57
    (Fin.cases seedInvT_row58
    (Fin.cases seedInvT_row59
    (Fin.cases seedInvT_row60
    (Fin.cases seedInvT_row61
    (Fin.cases seedInvT_row62
    (Fin.cases seedInvT_row63
    (Fin.cases seedInvT_row64
    (Fin.cases seedInvT_row65
    (Fin.cases seedInvT_row66
    (Fin.cases seedInvT_row67
    (Fin.cases seedInvT_row68
    (Fin.cases seedInvT_row69
    (Fin.cases seedInvT_row70
    (Fin.cases seedInvT_row71
    (Fin.cases seedInvT_row72
    (Fin.cases seedInvT_row73
    (Fin.cases seedInvT_row74
    (Fin.cases seedInvT_row75
    (Fin.cases seedInvT_row76
    (Fin.cases seedInvT_row77
    (Fin.cases seedInvT_row78
    (Fin.cases seedInvT_row79
    (Fin.cases seedInvT_row80
    (Fin.cases seedInvT_row81
    (Fin.cases seedInvT_row82
    (Fin.cases seedInvT_row83
    (Fin.cases seedInvT_row84
    (Fin.cases seedInvT_row85
    (Fin.cases seedInvT_row86
    (Fin.cases seedInvT_row87
    (Fin.cases seedInvT_row88
    (Fin.cases seedInvT_row89
    (Fin.cases seedInvT_row90
    (Fin.cases seedInvT_row91
    (Fin.cases seedInvT_row92
    (Fin.cases seedInvT_row93
    (Fin.cases seedInvT_row94
    (Fin.cases seedInvT_row95
    (Fin.cases seedInvT_row96
    (Fin.cases seedInvT_row97
    (Fin.cases seedInvT_row98
    (Fin.cases seedInvT_row99
    (Fin.cases seedInvT_row100
    (Fin.cases seedInvT_row101
    (Fin.cases seedInvT_row102
    (Fin.cases seedInvT_row103
    (Fin.cases seedInvT_row104
    (Fin.cases seedInvT_row105
    (Fin.cases seedInvT_row106
    (Fin.cases seedInvT_row107
    (Fin.cases seedInvT_row108
    (Fin.cases seedInvT_row109
    (Fin.cases seedInvT_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_seedInvT : seedInvMatrix * ab7Matrix = seedInvTMatrix :=
  decode_mul _ _ _ seedInv_small ab7_small seedInvT_rows

end Lyons.Atlas111InvolutionWords
