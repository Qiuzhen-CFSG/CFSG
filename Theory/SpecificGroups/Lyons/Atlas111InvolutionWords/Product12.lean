module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: c4 times c

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
private theorem c5_row0 :
    digitsEq 111 (rowProduct (c4Rows 0) cRows 111) (c5Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row1 :
    digitsEq 111 (rowProduct (c4Rows 1) cRows 111) (c5Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row2 :
    digitsEq 111 (rowProduct (c4Rows 2) cRows 111) (c5Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row3 :
    digitsEq 111 (rowProduct (c4Rows 3) cRows 111) (c5Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row4 :
    digitsEq 111 (rowProduct (c4Rows 4) cRows 111) (c5Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row5 :
    digitsEq 111 (rowProduct (c4Rows 5) cRows 111) (c5Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row6 :
    digitsEq 111 (rowProduct (c4Rows 6) cRows 111) (c5Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row7 :
    digitsEq 111 (rowProduct (c4Rows 7) cRows 111) (c5Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row8 :
    digitsEq 111 (rowProduct (c4Rows 8) cRows 111) (c5Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row9 :
    digitsEq 111 (rowProduct (c4Rows 9) cRows 111) (c5Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row10 :
    digitsEq 111 (rowProduct (c4Rows 10) cRows 111) (c5Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row11 :
    digitsEq 111 (rowProduct (c4Rows 11) cRows 111) (c5Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row12 :
    digitsEq 111 (rowProduct (c4Rows 12) cRows 111) (c5Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row13 :
    digitsEq 111 (rowProduct (c4Rows 13) cRows 111) (c5Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row14 :
    digitsEq 111 (rowProduct (c4Rows 14) cRows 111) (c5Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row15 :
    digitsEq 111 (rowProduct (c4Rows 15) cRows 111) (c5Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row16 :
    digitsEq 111 (rowProduct (c4Rows 16) cRows 111) (c5Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row17 :
    digitsEq 111 (rowProduct (c4Rows 17) cRows 111) (c5Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row18 :
    digitsEq 111 (rowProduct (c4Rows 18) cRows 111) (c5Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row19 :
    digitsEq 111 (rowProduct (c4Rows 19) cRows 111) (c5Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row20 :
    digitsEq 111 (rowProduct (c4Rows 20) cRows 111) (c5Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row21 :
    digitsEq 111 (rowProduct (c4Rows 21) cRows 111) (c5Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row22 :
    digitsEq 111 (rowProduct (c4Rows 22) cRows 111) (c5Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row23 :
    digitsEq 111 (rowProduct (c4Rows 23) cRows 111) (c5Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row24 :
    digitsEq 111 (rowProduct (c4Rows 24) cRows 111) (c5Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row25 :
    digitsEq 111 (rowProduct (c4Rows 25) cRows 111) (c5Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row26 :
    digitsEq 111 (rowProduct (c4Rows 26) cRows 111) (c5Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row27 :
    digitsEq 111 (rowProduct (c4Rows 27) cRows 111) (c5Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row28 :
    digitsEq 111 (rowProduct (c4Rows 28) cRows 111) (c5Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row29 :
    digitsEq 111 (rowProduct (c4Rows 29) cRows 111) (c5Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row30 :
    digitsEq 111 (rowProduct (c4Rows 30) cRows 111) (c5Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row31 :
    digitsEq 111 (rowProduct (c4Rows 31) cRows 111) (c5Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row32 :
    digitsEq 111 (rowProduct (c4Rows 32) cRows 111) (c5Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row33 :
    digitsEq 111 (rowProduct (c4Rows 33) cRows 111) (c5Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row34 :
    digitsEq 111 (rowProduct (c4Rows 34) cRows 111) (c5Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row35 :
    digitsEq 111 (rowProduct (c4Rows 35) cRows 111) (c5Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row36 :
    digitsEq 111 (rowProduct (c4Rows 36) cRows 111) (c5Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row37 :
    digitsEq 111 (rowProduct (c4Rows 37) cRows 111) (c5Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row38 :
    digitsEq 111 (rowProduct (c4Rows 38) cRows 111) (c5Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row39 :
    digitsEq 111 (rowProduct (c4Rows 39) cRows 111) (c5Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row40 :
    digitsEq 111 (rowProduct (c4Rows 40) cRows 111) (c5Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row41 :
    digitsEq 111 (rowProduct (c4Rows 41) cRows 111) (c5Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row42 :
    digitsEq 111 (rowProduct (c4Rows 42) cRows 111) (c5Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row43 :
    digitsEq 111 (rowProduct (c4Rows 43) cRows 111) (c5Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row44 :
    digitsEq 111 (rowProduct (c4Rows 44) cRows 111) (c5Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row45 :
    digitsEq 111 (rowProduct (c4Rows 45) cRows 111) (c5Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row46 :
    digitsEq 111 (rowProduct (c4Rows 46) cRows 111) (c5Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row47 :
    digitsEq 111 (rowProduct (c4Rows 47) cRows 111) (c5Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row48 :
    digitsEq 111 (rowProduct (c4Rows 48) cRows 111) (c5Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row49 :
    digitsEq 111 (rowProduct (c4Rows 49) cRows 111) (c5Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row50 :
    digitsEq 111 (rowProduct (c4Rows 50) cRows 111) (c5Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row51 :
    digitsEq 111 (rowProduct (c4Rows 51) cRows 111) (c5Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row52 :
    digitsEq 111 (rowProduct (c4Rows 52) cRows 111) (c5Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row53 :
    digitsEq 111 (rowProduct (c4Rows 53) cRows 111) (c5Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row54 :
    digitsEq 111 (rowProduct (c4Rows 54) cRows 111) (c5Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row55 :
    digitsEq 111 (rowProduct (c4Rows 55) cRows 111) (c5Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row56 :
    digitsEq 111 (rowProduct (c4Rows 56) cRows 111) (c5Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row57 :
    digitsEq 111 (rowProduct (c4Rows 57) cRows 111) (c5Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row58 :
    digitsEq 111 (rowProduct (c4Rows 58) cRows 111) (c5Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row59 :
    digitsEq 111 (rowProduct (c4Rows 59) cRows 111) (c5Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row60 :
    digitsEq 111 (rowProduct (c4Rows 60) cRows 111) (c5Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row61 :
    digitsEq 111 (rowProduct (c4Rows 61) cRows 111) (c5Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row62 :
    digitsEq 111 (rowProduct (c4Rows 62) cRows 111) (c5Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row63 :
    digitsEq 111 (rowProduct (c4Rows 63) cRows 111) (c5Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row64 :
    digitsEq 111 (rowProduct (c4Rows 64) cRows 111) (c5Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row65 :
    digitsEq 111 (rowProduct (c4Rows 65) cRows 111) (c5Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row66 :
    digitsEq 111 (rowProduct (c4Rows 66) cRows 111) (c5Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row67 :
    digitsEq 111 (rowProduct (c4Rows 67) cRows 111) (c5Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row68 :
    digitsEq 111 (rowProduct (c4Rows 68) cRows 111) (c5Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row69 :
    digitsEq 111 (rowProduct (c4Rows 69) cRows 111) (c5Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row70 :
    digitsEq 111 (rowProduct (c4Rows 70) cRows 111) (c5Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row71 :
    digitsEq 111 (rowProduct (c4Rows 71) cRows 111) (c5Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row72 :
    digitsEq 111 (rowProduct (c4Rows 72) cRows 111) (c5Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row73 :
    digitsEq 111 (rowProduct (c4Rows 73) cRows 111) (c5Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row74 :
    digitsEq 111 (rowProduct (c4Rows 74) cRows 111) (c5Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row75 :
    digitsEq 111 (rowProduct (c4Rows 75) cRows 111) (c5Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row76 :
    digitsEq 111 (rowProduct (c4Rows 76) cRows 111) (c5Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row77 :
    digitsEq 111 (rowProduct (c4Rows 77) cRows 111) (c5Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row78 :
    digitsEq 111 (rowProduct (c4Rows 78) cRows 111) (c5Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row79 :
    digitsEq 111 (rowProduct (c4Rows 79) cRows 111) (c5Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row80 :
    digitsEq 111 (rowProduct (c4Rows 80) cRows 111) (c5Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row81 :
    digitsEq 111 (rowProduct (c4Rows 81) cRows 111) (c5Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row82 :
    digitsEq 111 (rowProduct (c4Rows 82) cRows 111) (c5Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row83 :
    digitsEq 111 (rowProduct (c4Rows 83) cRows 111) (c5Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row84 :
    digitsEq 111 (rowProduct (c4Rows 84) cRows 111) (c5Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row85 :
    digitsEq 111 (rowProduct (c4Rows 85) cRows 111) (c5Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row86 :
    digitsEq 111 (rowProduct (c4Rows 86) cRows 111) (c5Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row87 :
    digitsEq 111 (rowProduct (c4Rows 87) cRows 111) (c5Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row88 :
    digitsEq 111 (rowProduct (c4Rows 88) cRows 111) (c5Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row89 :
    digitsEq 111 (rowProduct (c4Rows 89) cRows 111) (c5Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row90 :
    digitsEq 111 (rowProduct (c4Rows 90) cRows 111) (c5Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row91 :
    digitsEq 111 (rowProduct (c4Rows 91) cRows 111) (c5Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row92 :
    digitsEq 111 (rowProduct (c4Rows 92) cRows 111) (c5Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row93 :
    digitsEq 111 (rowProduct (c4Rows 93) cRows 111) (c5Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row94 :
    digitsEq 111 (rowProduct (c4Rows 94) cRows 111) (c5Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row95 :
    digitsEq 111 (rowProduct (c4Rows 95) cRows 111) (c5Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row96 :
    digitsEq 111 (rowProduct (c4Rows 96) cRows 111) (c5Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row97 :
    digitsEq 111 (rowProduct (c4Rows 97) cRows 111) (c5Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row98 :
    digitsEq 111 (rowProduct (c4Rows 98) cRows 111) (c5Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row99 :
    digitsEq 111 (rowProduct (c4Rows 99) cRows 111) (c5Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row100 :
    digitsEq 111 (rowProduct (c4Rows 100) cRows 111) (c5Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row101 :
    digitsEq 111 (rowProduct (c4Rows 101) cRows 111) (c5Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row102 :
    digitsEq 111 (rowProduct (c4Rows 102) cRows 111) (c5Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row103 :
    digitsEq 111 (rowProduct (c4Rows 103) cRows 111) (c5Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row104 :
    digitsEq 111 (rowProduct (c4Rows 104) cRows 111) (c5Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row105 :
    digitsEq 111 (rowProduct (c4Rows 105) cRows 111) (c5Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row106 :
    digitsEq 111 (rowProduct (c4Rows 106) cRows 111) (c5Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row107 :
    digitsEq 111 (rowProduct (c4Rows 107) cRows 111) (c5Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row108 :
    digitsEq 111 (rowProduct (c4Rows 108) cRows 111) (c5Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row109 :
    digitsEq 111 (rowProduct (c4Rows 109) cRows 111) (c5Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c5_row110 :
    digitsEq 111 (rowProduct (c4Rows 110) cRows 111) (c5Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem c5_rows : ∀ i,
    digitsEq 111 (rowProduct (c4Rows i) cRows 111) (c5Rows i) = true :=
  (Fin.cases c5_row0
    (Fin.cases c5_row1
    (Fin.cases c5_row2
    (Fin.cases c5_row3
    (Fin.cases c5_row4
    (Fin.cases c5_row5
    (Fin.cases c5_row6
    (Fin.cases c5_row7
    (Fin.cases c5_row8
    (Fin.cases c5_row9
    (Fin.cases c5_row10
    (Fin.cases c5_row11
    (Fin.cases c5_row12
    (Fin.cases c5_row13
    (Fin.cases c5_row14
    (Fin.cases c5_row15
    (Fin.cases c5_row16
    (Fin.cases c5_row17
    (Fin.cases c5_row18
    (Fin.cases c5_row19
    (Fin.cases c5_row20
    (Fin.cases c5_row21
    (Fin.cases c5_row22
    (Fin.cases c5_row23
    (Fin.cases c5_row24
    (Fin.cases c5_row25
    (Fin.cases c5_row26
    (Fin.cases c5_row27
    (Fin.cases c5_row28
    (Fin.cases c5_row29
    (Fin.cases c5_row30
    (Fin.cases c5_row31
    (Fin.cases c5_row32
    (Fin.cases c5_row33
    (Fin.cases c5_row34
    (Fin.cases c5_row35
    (Fin.cases c5_row36
    (Fin.cases c5_row37
    (Fin.cases c5_row38
    (Fin.cases c5_row39
    (Fin.cases c5_row40
    (Fin.cases c5_row41
    (Fin.cases c5_row42
    (Fin.cases c5_row43
    (Fin.cases c5_row44
    (Fin.cases c5_row45
    (Fin.cases c5_row46
    (Fin.cases c5_row47
    (Fin.cases c5_row48
    (Fin.cases c5_row49
    (Fin.cases c5_row50
    (Fin.cases c5_row51
    (Fin.cases c5_row52
    (Fin.cases c5_row53
    (Fin.cases c5_row54
    (Fin.cases c5_row55
    (Fin.cases c5_row56
    (Fin.cases c5_row57
    (Fin.cases c5_row58
    (Fin.cases c5_row59
    (Fin.cases c5_row60
    (Fin.cases c5_row61
    (Fin.cases c5_row62
    (Fin.cases c5_row63
    (Fin.cases c5_row64
    (Fin.cases c5_row65
    (Fin.cases c5_row66
    (Fin.cases c5_row67
    (Fin.cases c5_row68
    (Fin.cases c5_row69
    (Fin.cases c5_row70
    (Fin.cases c5_row71
    (Fin.cases c5_row72
    (Fin.cases c5_row73
    (Fin.cases c5_row74
    (Fin.cases c5_row75
    (Fin.cases c5_row76
    (Fin.cases c5_row77
    (Fin.cases c5_row78
    (Fin.cases c5_row79
    (Fin.cases c5_row80
    (Fin.cases c5_row81
    (Fin.cases c5_row82
    (Fin.cases c5_row83
    (Fin.cases c5_row84
    (Fin.cases c5_row85
    (Fin.cases c5_row86
    (Fin.cases c5_row87
    (Fin.cases c5_row88
    (Fin.cases c5_row89
    (Fin.cases c5_row90
    (Fin.cases c5_row91
    (Fin.cases c5_row92
    (Fin.cases c5_row93
    (Fin.cases c5_row94
    (Fin.cases c5_row95
    (Fin.cases c5_row96
    (Fin.cases c5_row97
    (Fin.cases c5_row98
    (Fin.cases c5_row99
    (Fin.cases c5_row100
    (Fin.cases c5_row101
    (Fin.cases c5_row102
    (Fin.cases c5_row103
    (Fin.cases c5_row104
    (Fin.cases c5_row105
    (Fin.cases c5_row106
    (Fin.cases c5_row107
    (Fin.cases c5_row108
    (Fin.cases c5_row109
    (Fin.cases c5_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_c5 : c4Matrix * cMatrix = c5Matrix :=
  decode_mul _ _ _ c4_small c_small c5_rows

end Lyons.Atlas111InvolutionWords
