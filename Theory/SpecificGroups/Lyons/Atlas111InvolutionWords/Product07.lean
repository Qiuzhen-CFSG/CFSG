module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: r10 times ab7

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
private theorem rt_row0 :
    digitsEq 111 (rowProduct (r10Rows 0) ab7Rows 111) (rtRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row1 :
    digitsEq 111 (rowProduct (r10Rows 1) ab7Rows 111) (rtRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row2 :
    digitsEq 111 (rowProduct (r10Rows 2) ab7Rows 111) (rtRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row3 :
    digitsEq 111 (rowProduct (r10Rows 3) ab7Rows 111) (rtRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row4 :
    digitsEq 111 (rowProduct (r10Rows 4) ab7Rows 111) (rtRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row5 :
    digitsEq 111 (rowProduct (r10Rows 5) ab7Rows 111) (rtRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row6 :
    digitsEq 111 (rowProduct (r10Rows 6) ab7Rows 111) (rtRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row7 :
    digitsEq 111 (rowProduct (r10Rows 7) ab7Rows 111) (rtRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row8 :
    digitsEq 111 (rowProduct (r10Rows 8) ab7Rows 111) (rtRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row9 :
    digitsEq 111 (rowProduct (r10Rows 9) ab7Rows 111) (rtRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row10 :
    digitsEq 111 (rowProduct (r10Rows 10) ab7Rows 111) (rtRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row11 :
    digitsEq 111 (rowProduct (r10Rows 11) ab7Rows 111) (rtRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row12 :
    digitsEq 111 (rowProduct (r10Rows 12) ab7Rows 111) (rtRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row13 :
    digitsEq 111 (rowProduct (r10Rows 13) ab7Rows 111) (rtRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row14 :
    digitsEq 111 (rowProduct (r10Rows 14) ab7Rows 111) (rtRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row15 :
    digitsEq 111 (rowProduct (r10Rows 15) ab7Rows 111) (rtRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row16 :
    digitsEq 111 (rowProduct (r10Rows 16) ab7Rows 111) (rtRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row17 :
    digitsEq 111 (rowProduct (r10Rows 17) ab7Rows 111) (rtRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row18 :
    digitsEq 111 (rowProduct (r10Rows 18) ab7Rows 111) (rtRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row19 :
    digitsEq 111 (rowProduct (r10Rows 19) ab7Rows 111) (rtRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row20 :
    digitsEq 111 (rowProduct (r10Rows 20) ab7Rows 111) (rtRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row21 :
    digitsEq 111 (rowProduct (r10Rows 21) ab7Rows 111) (rtRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row22 :
    digitsEq 111 (rowProduct (r10Rows 22) ab7Rows 111) (rtRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row23 :
    digitsEq 111 (rowProduct (r10Rows 23) ab7Rows 111) (rtRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row24 :
    digitsEq 111 (rowProduct (r10Rows 24) ab7Rows 111) (rtRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row25 :
    digitsEq 111 (rowProduct (r10Rows 25) ab7Rows 111) (rtRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row26 :
    digitsEq 111 (rowProduct (r10Rows 26) ab7Rows 111) (rtRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row27 :
    digitsEq 111 (rowProduct (r10Rows 27) ab7Rows 111) (rtRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row28 :
    digitsEq 111 (rowProduct (r10Rows 28) ab7Rows 111) (rtRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row29 :
    digitsEq 111 (rowProduct (r10Rows 29) ab7Rows 111) (rtRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row30 :
    digitsEq 111 (rowProduct (r10Rows 30) ab7Rows 111) (rtRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row31 :
    digitsEq 111 (rowProduct (r10Rows 31) ab7Rows 111) (rtRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row32 :
    digitsEq 111 (rowProduct (r10Rows 32) ab7Rows 111) (rtRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row33 :
    digitsEq 111 (rowProduct (r10Rows 33) ab7Rows 111) (rtRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row34 :
    digitsEq 111 (rowProduct (r10Rows 34) ab7Rows 111) (rtRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row35 :
    digitsEq 111 (rowProduct (r10Rows 35) ab7Rows 111) (rtRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row36 :
    digitsEq 111 (rowProduct (r10Rows 36) ab7Rows 111) (rtRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row37 :
    digitsEq 111 (rowProduct (r10Rows 37) ab7Rows 111) (rtRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row38 :
    digitsEq 111 (rowProduct (r10Rows 38) ab7Rows 111) (rtRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row39 :
    digitsEq 111 (rowProduct (r10Rows 39) ab7Rows 111) (rtRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row40 :
    digitsEq 111 (rowProduct (r10Rows 40) ab7Rows 111) (rtRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row41 :
    digitsEq 111 (rowProduct (r10Rows 41) ab7Rows 111) (rtRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row42 :
    digitsEq 111 (rowProduct (r10Rows 42) ab7Rows 111) (rtRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row43 :
    digitsEq 111 (rowProduct (r10Rows 43) ab7Rows 111) (rtRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row44 :
    digitsEq 111 (rowProduct (r10Rows 44) ab7Rows 111) (rtRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row45 :
    digitsEq 111 (rowProduct (r10Rows 45) ab7Rows 111) (rtRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row46 :
    digitsEq 111 (rowProduct (r10Rows 46) ab7Rows 111) (rtRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row47 :
    digitsEq 111 (rowProduct (r10Rows 47) ab7Rows 111) (rtRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row48 :
    digitsEq 111 (rowProduct (r10Rows 48) ab7Rows 111) (rtRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row49 :
    digitsEq 111 (rowProduct (r10Rows 49) ab7Rows 111) (rtRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row50 :
    digitsEq 111 (rowProduct (r10Rows 50) ab7Rows 111) (rtRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row51 :
    digitsEq 111 (rowProduct (r10Rows 51) ab7Rows 111) (rtRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row52 :
    digitsEq 111 (rowProduct (r10Rows 52) ab7Rows 111) (rtRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row53 :
    digitsEq 111 (rowProduct (r10Rows 53) ab7Rows 111) (rtRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row54 :
    digitsEq 111 (rowProduct (r10Rows 54) ab7Rows 111) (rtRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row55 :
    digitsEq 111 (rowProduct (r10Rows 55) ab7Rows 111) (rtRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row56 :
    digitsEq 111 (rowProduct (r10Rows 56) ab7Rows 111) (rtRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row57 :
    digitsEq 111 (rowProduct (r10Rows 57) ab7Rows 111) (rtRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row58 :
    digitsEq 111 (rowProduct (r10Rows 58) ab7Rows 111) (rtRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row59 :
    digitsEq 111 (rowProduct (r10Rows 59) ab7Rows 111) (rtRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row60 :
    digitsEq 111 (rowProduct (r10Rows 60) ab7Rows 111) (rtRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row61 :
    digitsEq 111 (rowProduct (r10Rows 61) ab7Rows 111) (rtRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row62 :
    digitsEq 111 (rowProduct (r10Rows 62) ab7Rows 111) (rtRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row63 :
    digitsEq 111 (rowProduct (r10Rows 63) ab7Rows 111) (rtRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row64 :
    digitsEq 111 (rowProduct (r10Rows 64) ab7Rows 111) (rtRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row65 :
    digitsEq 111 (rowProduct (r10Rows 65) ab7Rows 111) (rtRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row66 :
    digitsEq 111 (rowProduct (r10Rows 66) ab7Rows 111) (rtRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row67 :
    digitsEq 111 (rowProduct (r10Rows 67) ab7Rows 111) (rtRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row68 :
    digitsEq 111 (rowProduct (r10Rows 68) ab7Rows 111) (rtRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row69 :
    digitsEq 111 (rowProduct (r10Rows 69) ab7Rows 111) (rtRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row70 :
    digitsEq 111 (rowProduct (r10Rows 70) ab7Rows 111) (rtRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row71 :
    digitsEq 111 (rowProduct (r10Rows 71) ab7Rows 111) (rtRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row72 :
    digitsEq 111 (rowProduct (r10Rows 72) ab7Rows 111) (rtRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row73 :
    digitsEq 111 (rowProduct (r10Rows 73) ab7Rows 111) (rtRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row74 :
    digitsEq 111 (rowProduct (r10Rows 74) ab7Rows 111) (rtRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row75 :
    digitsEq 111 (rowProduct (r10Rows 75) ab7Rows 111) (rtRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row76 :
    digitsEq 111 (rowProduct (r10Rows 76) ab7Rows 111) (rtRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row77 :
    digitsEq 111 (rowProduct (r10Rows 77) ab7Rows 111) (rtRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row78 :
    digitsEq 111 (rowProduct (r10Rows 78) ab7Rows 111) (rtRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row79 :
    digitsEq 111 (rowProduct (r10Rows 79) ab7Rows 111) (rtRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row80 :
    digitsEq 111 (rowProduct (r10Rows 80) ab7Rows 111) (rtRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row81 :
    digitsEq 111 (rowProduct (r10Rows 81) ab7Rows 111) (rtRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row82 :
    digitsEq 111 (rowProduct (r10Rows 82) ab7Rows 111) (rtRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row83 :
    digitsEq 111 (rowProduct (r10Rows 83) ab7Rows 111) (rtRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row84 :
    digitsEq 111 (rowProduct (r10Rows 84) ab7Rows 111) (rtRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row85 :
    digitsEq 111 (rowProduct (r10Rows 85) ab7Rows 111) (rtRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row86 :
    digitsEq 111 (rowProduct (r10Rows 86) ab7Rows 111) (rtRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row87 :
    digitsEq 111 (rowProduct (r10Rows 87) ab7Rows 111) (rtRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row88 :
    digitsEq 111 (rowProduct (r10Rows 88) ab7Rows 111) (rtRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row89 :
    digitsEq 111 (rowProduct (r10Rows 89) ab7Rows 111) (rtRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row90 :
    digitsEq 111 (rowProduct (r10Rows 90) ab7Rows 111) (rtRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row91 :
    digitsEq 111 (rowProduct (r10Rows 91) ab7Rows 111) (rtRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row92 :
    digitsEq 111 (rowProduct (r10Rows 92) ab7Rows 111) (rtRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row93 :
    digitsEq 111 (rowProduct (r10Rows 93) ab7Rows 111) (rtRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row94 :
    digitsEq 111 (rowProduct (r10Rows 94) ab7Rows 111) (rtRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row95 :
    digitsEq 111 (rowProduct (r10Rows 95) ab7Rows 111) (rtRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row96 :
    digitsEq 111 (rowProduct (r10Rows 96) ab7Rows 111) (rtRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row97 :
    digitsEq 111 (rowProduct (r10Rows 97) ab7Rows 111) (rtRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row98 :
    digitsEq 111 (rowProduct (r10Rows 98) ab7Rows 111) (rtRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row99 :
    digitsEq 111 (rowProduct (r10Rows 99) ab7Rows 111) (rtRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row100 :
    digitsEq 111 (rowProduct (r10Rows 100) ab7Rows 111) (rtRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row101 :
    digitsEq 111 (rowProduct (r10Rows 101) ab7Rows 111) (rtRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row102 :
    digitsEq 111 (rowProduct (r10Rows 102) ab7Rows 111) (rtRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row103 :
    digitsEq 111 (rowProduct (r10Rows 103) ab7Rows 111) (rtRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row104 :
    digitsEq 111 (rowProduct (r10Rows 104) ab7Rows 111) (rtRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row105 :
    digitsEq 111 (rowProduct (r10Rows 105) ab7Rows 111) (rtRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row106 :
    digitsEq 111 (rowProduct (r10Rows 106) ab7Rows 111) (rtRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row107 :
    digitsEq 111 (rowProduct (r10Rows 107) ab7Rows 111) (rtRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row108 :
    digitsEq 111 (rowProduct (r10Rows 108) ab7Rows 111) (rtRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row109 :
    digitsEq 111 (rowProduct (r10Rows 109) ab7Rows 111) (rtRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rt_row110 :
    digitsEq 111 (rowProduct (r10Rows 110) ab7Rows 111) (rtRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem rt_rows : ∀ i,
    digitsEq 111 (rowProduct (r10Rows i) ab7Rows 111) (rtRows i) = true :=
  (Fin.cases rt_row0
    (Fin.cases rt_row1
    (Fin.cases rt_row2
    (Fin.cases rt_row3
    (Fin.cases rt_row4
    (Fin.cases rt_row5
    (Fin.cases rt_row6
    (Fin.cases rt_row7
    (Fin.cases rt_row8
    (Fin.cases rt_row9
    (Fin.cases rt_row10
    (Fin.cases rt_row11
    (Fin.cases rt_row12
    (Fin.cases rt_row13
    (Fin.cases rt_row14
    (Fin.cases rt_row15
    (Fin.cases rt_row16
    (Fin.cases rt_row17
    (Fin.cases rt_row18
    (Fin.cases rt_row19
    (Fin.cases rt_row20
    (Fin.cases rt_row21
    (Fin.cases rt_row22
    (Fin.cases rt_row23
    (Fin.cases rt_row24
    (Fin.cases rt_row25
    (Fin.cases rt_row26
    (Fin.cases rt_row27
    (Fin.cases rt_row28
    (Fin.cases rt_row29
    (Fin.cases rt_row30
    (Fin.cases rt_row31
    (Fin.cases rt_row32
    (Fin.cases rt_row33
    (Fin.cases rt_row34
    (Fin.cases rt_row35
    (Fin.cases rt_row36
    (Fin.cases rt_row37
    (Fin.cases rt_row38
    (Fin.cases rt_row39
    (Fin.cases rt_row40
    (Fin.cases rt_row41
    (Fin.cases rt_row42
    (Fin.cases rt_row43
    (Fin.cases rt_row44
    (Fin.cases rt_row45
    (Fin.cases rt_row46
    (Fin.cases rt_row47
    (Fin.cases rt_row48
    (Fin.cases rt_row49
    (Fin.cases rt_row50
    (Fin.cases rt_row51
    (Fin.cases rt_row52
    (Fin.cases rt_row53
    (Fin.cases rt_row54
    (Fin.cases rt_row55
    (Fin.cases rt_row56
    (Fin.cases rt_row57
    (Fin.cases rt_row58
    (Fin.cases rt_row59
    (Fin.cases rt_row60
    (Fin.cases rt_row61
    (Fin.cases rt_row62
    (Fin.cases rt_row63
    (Fin.cases rt_row64
    (Fin.cases rt_row65
    (Fin.cases rt_row66
    (Fin.cases rt_row67
    (Fin.cases rt_row68
    (Fin.cases rt_row69
    (Fin.cases rt_row70
    (Fin.cases rt_row71
    (Fin.cases rt_row72
    (Fin.cases rt_row73
    (Fin.cases rt_row74
    (Fin.cases rt_row75
    (Fin.cases rt_row76
    (Fin.cases rt_row77
    (Fin.cases rt_row78
    (Fin.cases rt_row79
    (Fin.cases rt_row80
    (Fin.cases rt_row81
    (Fin.cases rt_row82
    (Fin.cases rt_row83
    (Fin.cases rt_row84
    (Fin.cases rt_row85
    (Fin.cases rt_row86
    (Fin.cases rt_row87
    (Fin.cases rt_row88
    (Fin.cases rt_row89
    (Fin.cases rt_row90
    (Fin.cases rt_row91
    (Fin.cases rt_row92
    (Fin.cases rt_row93
    (Fin.cases rt_row94
    (Fin.cases rt_row95
    (Fin.cases rt_row96
    (Fin.cases rt_row97
    (Fin.cases rt_row98
    (Fin.cases rt_row99
    (Fin.cases rt_row100
    (Fin.cases rt_row101
    (Fin.cases rt_row102
    (Fin.cases rt_row103
    (Fin.cases rt_row104
    (Fin.cases rt_row105
    (Fin.cases rt_row106
    (Fin.cases rt_row107
    (Fin.cases rt_row108
    (Fin.cases rt_row109
    (Fin.cases rt_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_rt : r10Matrix * ab7Matrix = rtMatrix :=
  decode_mul _ _ _ r10_small ab7_small rt_rows

end Lyons.Atlas111InvolutionWords
