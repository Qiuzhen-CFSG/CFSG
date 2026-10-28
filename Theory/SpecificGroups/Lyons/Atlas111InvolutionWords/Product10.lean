module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: c times c

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
private theorem c2_row0 :
    digitsEq 111 (rowProduct (cRows 0) cRows 111) (c2Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row1 :
    digitsEq 111 (rowProduct (cRows 1) cRows 111) (c2Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row2 :
    digitsEq 111 (rowProduct (cRows 2) cRows 111) (c2Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row3 :
    digitsEq 111 (rowProduct (cRows 3) cRows 111) (c2Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row4 :
    digitsEq 111 (rowProduct (cRows 4) cRows 111) (c2Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row5 :
    digitsEq 111 (rowProduct (cRows 5) cRows 111) (c2Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row6 :
    digitsEq 111 (rowProduct (cRows 6) cRows 111) (c2Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row7 :
    digitsEq 111 (rowProduct (cRows 7) cRows 111) (c2Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row8 :
    digitsEq 111 (rowProduct (cRows 8) cRows 111) (c2Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row9 :
    digitsEq 111 (rowProduct (cRows 9) cRows 111) (c2Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row10 :
    digitsEq 111 (rowProduct (cRows 10) cRows 111) (c2Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row11 :
    digitsEq 111 (rowProduct (cRows 11) cRows 111) (c2Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row12 :
    digitsEq 111 (rowProduct (cRows 12) cRows 111) (c2Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row13 :
    digitsEq 111 (rowProduct (cRows 13) cRows 111) (c2Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row14 :
    digitsEq 111 (rowProduct (cRows 14) cRows 111) (c2Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row15 :
    digitsEq 111 (rowProduct (cRows 15) cRows 111) (c2Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row16 :
    digitsEq 111 (rowProduct (cRows 16) cRows 111) (c2Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row17 :
    digitsEq 111 (rowProduct (cRows 17) cRows 111) (c2Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row18 :
    digitsEq 111 (rowProduct (cRows 18) cRows 111) (c2Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row19 :
    digitsEq 111 (rowProduct (cRows 19) cRows 111) (c2Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row20 :
    digitsEq 111 (rowProduct (cRows 20) cRows 111) (c2Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row21 :
    digitsEq 111 (rowProduct (cRows 21) cRows 111) (c2Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row22 :
    digitsEq 111 (rowProduct (cRows 22) cRows 111) (c2Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row23 :
    digitsEq 111 (rowProduct (cRows 23) cRows 111) (c2Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row24 :
    digitsEq 111 (rowProduct (cRows 24) cRows 111) (c2Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row25 :
    digitsEq 111 (rowProduct (cRows 25) cRows 111) (c2Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row26 :
    digitsEq 111 (rowProduct (cRows 26) cRows 111) (c2Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row27 :
    digitsEq 111 (rowProduct (cRows 27) cRows 111) (c2Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row28 :
    digitsEq 111 (rowProduct (cRows 28) cRows 111) (c2Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row29 :
    digitsEq 111 (rowProduct (cRows 29) cRows 111) (c2Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row30 :
    digitsEq 111 (rowProduct (cRows 30) cRows 111) (c2Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row31 :
    digitsEq 111 (rowProduct (cRows 31) cRows 111) (c2Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row32 :
    digitsEq 111 (rowProduct (cRows 32) cRows 111) (c2Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row33 :
    digitsEq 111 (rowProduct (cRows 33) cRows 111) (c2Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row34 :
    digitsEq 111 (rowProduct (cRows 34) cRows 111) (c2Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row35 :
    digitsEq 111 (rowProduct (cRows 35) cRows 111) (c2Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row36 :
    digitsEq 111 (rowProduct (cRows 36) cRows 111) (c2Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row37 :
    digitsEq 111 (rowProduct (cRows 37) cRows 111) (c2Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row38 :
    digitsEq 111 (rowProduct (cRows 38) cRows 111) (c2Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row39 :
    digitsEq 111 (rowProduct (cRows 39) cRows 111) (c2Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row40 :
    digitsEq 111 (rowProduct (cRows 40) cRows 111) (c2Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row41 :
    digitsEq 111 (rowProduct (cRows 41) cRows 111) (c2Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row42 :
    digitsEq 111 (rowProduct (cRows 42) cRows 111) (c2Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row43 :
    digitsEq 111 (rowProduct (cRows 43) cRows 111) (c2Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row44 :
    digitsEq 111 (rowProduct (cRows 44) cRows 111) (c2Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row45 :
    digitsEq 111 (rowProduct (cRows 45) cRows 111) (c2Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row46 :
    digitsEq 111 (rowProduct (cRows 46) cRows 111) (c2Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row47 :
    digitsEq 111 (rowProduct (cRows 47) cRows 111) (c2Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row48 :
    digitsEq 111 (rowProduct (cRows 48) cRows 111) (c2Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row49 :
    digitsEq 111 (rowProduct (cRows 49) cRows 111) (c2Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row50 :
    digitsEq 111 (rowProduct (cRows 50) cRows 111) (c2Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row51 :
    digitsEq 111 (rowProduct (cRows 51) cRows 111) (c2Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row52 :
    digitsEq 111 (rowProduct (cRows 52) cRows 111) (c2Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row53 :
    digitsEq 111 (rowProduct (cRows 53) cRows 111) (c2Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row54 :
    digitsEq 111 (rowProduct (cRows 54) cRows 111) (c2Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row55 :
    digitsEq 111 (rowProduct (cRows 55) cRows 111) (c2Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row56 :
    digitsEq 111 (rowProduct (cRows 56) cRows 111) (c2Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row57 :
    digitsEq 111 (rowProduct (cRows 57) cRows 111) (c2Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row58 :
    digitsEq 111 (rowProduct (cRows 58) cRows 111) (c2Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row59 :
    digitsEq 111 (rowProduct (cRows 59) cRows 111) (c2Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row60 :
    digitsEq 111 (rowProduct (cRows 60) cRows 111) (c2Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row61 :
    digitsEq 111 (rowProduct (cRows 61) cRows 111) (c2Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row62 :
    digitsEq 111 (rowProduct (cRows 62) cRows 111) (c2Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row63 :
    digitsEq 111 (rowProduct (cRows 63) cRows 111) (c2Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row64 :
    digitsEq 111 (rowProduct (cRows 64) cRows 111) (c2Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row65 :
    digitsEq 111 (rowProduct (cRows 65) cRows 111) (c2Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row66 :
    digitsEq 111 (rowProduct (cRows 66) cRows 111) (c2Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row67 :
    digitsEq 111 (rowProduct (cRows 67) cRows 111) (c2Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row68 :
    digitsEq 111 (rowProduct (cRows 68) cRows 111) (c2Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row69 :
    digitsEq 111 (rowProduct (cRows 69) cRows 111) (c2Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row70 :
    digitsEq 111 (rowProduct (cRows 70) cRows 111) (c2Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row71 :
    digitsEq 111 (rowProduct (cRows 71) cRows 111) (c2Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row72 :
    digitsEq 111 (rowProduct (cRows 72) cRows 111) (c2Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row73 :
    digitsEq 111 (rowProduct (cRows 73) cRows 111) (c2Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row74 :
    digitsEq 111 (rowProduct (cRows 74) cRows 111) (c2Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row75 :
    digitsEq 111 (rowProduct (cRows 75) cRows 111) (c2Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row76 :
    digitsEq 111 (rowProduct (cRows 76) cRows 111) (c2Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row77 :
    digitsEq 111 (rowProduct (cRows 77) cRows 111) (c2Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row78 :
    digitsEq 111 (rowProduct (cRows 78) cRows 111) (c2Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row79 :
    digitsEq 111 (rowProduct (cRows 79) cRows 111) (c2Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row80 :
    digitsEq 111 (rowProduct (cRows 80) cRows 111) (c2Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row81 :
    digitsEq 111 (rowProduct (cRows 81) cRows 111) (c2Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row82 :
    digitsEq 111 (rowProduct (cRows 82) cRows 111) (c2Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row83 :
    digitsEq 111 (rowProduct (cRows 83) cRows 111) (c2Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row84 :
    digitsEq 111 (rowProduct (cRows 84) cRows 111) (c2Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row85 :
    digitsEq 111 (rowProduct (cRows 85) cRows 111) (c2Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row86 :
    digitsEq 111 (rowProduct (cRows 86) cRows 111) (c2Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row87 :
    digitsEq 111 (rowProduct (cRows 87) cRows 111) (c2Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row88 :
    digitsEq 111 (rowProduct (cRows 88) cRows 111) (c2Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row89 :
    digitsEq 111 (rowProduct (cRows 89) cRows 111) (c2Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row90 :
    digitsEq 111 (rowProduct (cRows 90) cRows 111) (c2Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row91 :
    digitsEq 111 (rowProduct (cRows 91) cRows 111) (c2Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row92 :
    digitsEq 111 (rowProduct (cRows 92) cRows 111) (c2Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row93 :
    digitsEq 111 (rowProduct (cRows 93) cRows 111) (c2Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row94 :
    digitsEq 111 (rowProduct (cRows 94) cRows 111) (c2Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row95 :
    digitsEq 111 (rowProduct (cRows 95) cRows 111) (c2Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row96 :
    digitsEq 111 (rowProduct (cRows 96) cRows 111) (c2Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row97 :
    digitsEq 111 (rowProduct (cRows 97) cRows 111) (c2Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row98 :
    digitsEq 111 (rowProduct (cRows 98) cRows 111) (c2Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row99 :
    digitsEq 111 (rowProduct (cRows 99) cRows 111) (c2Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row100 :
    digitsEq 111 (rowProduct (cRows 100) cRows 111) (c2Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row101 :
    digitsEq 111 (rowProduct (cRows 101) cRows 111) (c2Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row102 :
    digitsEq 111 (rowProduct (cRows 102) cRows 111) (c2Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row103 :
    digitsEq 111 (rowProduct (cRows 103) cRows 111) (c2Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row104 :
    digitsEq 111 (rowProduct (cRows 104) cRows 111) (c2Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row105 :
    digitsEq 111 (rowProduct (cRows 105) cRows 111) (c2Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row106 :
    digitsEq 111 (rowProduct (cRows 106) cRows 111) (c2Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row107 :
    digitsEq 111 (rowProduct (cRows 107) cRows 111) (c2Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row108 :
    digitsEq 111 (rowProduct (cRows 108) cRows 111) (c2Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row109 :
    digitsEq 111 (rowProduct (cRows 109) cRows 111) (c2Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c2_row110 :
    digitsEq 111 (rowProduct (cRows 110) cRows 111) (c2Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem c2_rows : ∀ i,
    digitsEq 111 (rowProduct (cRows i) cRows 111) (c2Rows i) = true :=
  (Fin.cases c2_row0
    (Fin.cases c2_row1
    (Fin.cases c2_row2
    (Fin.cases c2_row3
    (Fin.cases c2_row4
    (Fin.cases c2_row5
    (Fin.cases c2_row6
    (Fin.cases c2_row7
    (Fin.cases c2_row8
    (Fin.cases c2_row9
    (Fin.cases c2_row10
    (Fin.cases c2_row11
    (Fin.cases c2_row12
    (Fin.cases c2_row13
    (Fin.cases c2_row14
    (Fin.cases c2_row15
    (Fin.cases c2_row16
    (Fin.cases c2_row17
    (Fin.cases c2_row18
    (Fin.cases c2_row19
    (Fin.cases c2_row20
    (Fin.cases c2_row21
    (Fin.cases c2_row22
    (Fin.cases c2_row23
    (Fin.cases c2_row24
    (Fin.cases c2_row25
    (Fin.cases c2_row26
    (Fin.cases c2_row27
    (Fin.cases c2_row28
    (Fin.cases c2_row29
    (Fin.cases c2_row30
    (Fin.cases c2_row31
    (Fin.cases c2_row32
    (Fin.cases c2_row33
    (Fin.cases c2_row34
    (Fin.cases c2_row35
    (Fin.cases c2_row36
    (Fin.cases c2_row37
    (Fin.cases c2_row38
    (Fin.cases c2_row39
    (Fin.cases c2_row40
    (Fin.cases c2_row41
    (Fin.cases c2_row42
    (Fin.cases c2_row43
    (Fin.cases c2_row44
    (Fin.cases c2_row45
    (Fin.cases c2_row46
    (Fin.cases c2_row47
    (Fin.cases c2_row48
    (Fin.cases c2_row49
    (Fin.cases c2_row50
    (Fin.cases c2_row51
    (Fin.cases c2_row52
    (Fin.cases c2_row53
    (Fin.cases c2_row54
    (Fin.cases c2_row55
    (Fin.cases c2_row56
    (Fin.cases c2_row57
    (Fin.cases c2_row58
    (Fin.cases c2_row59
    (Fin.cases c2_row60
    (Fin.cases c2_row61
    (Fin.cases c2_row62
    (Fin.cases c2_row63
    (Fin.cases c2_row64
    (Fin.cases c2_row65
    (Fin.cases c2_row66
    (Fin.cases c2_row67
    (Fin.cases c2_row68
    (Fin.cases c2_row69
    (Fin.cases c2_row70
    (Fin.cases c2_row71
    (Fin.cases c2_row72
    (Fin.cases c2_row73
    (Fin.cases c2_row74
    (Fin.cases c2_row75
    (Fin.cases c2_row76
    (Fin.cases c2_row77
    (Fin.cases c2_row78
    (Fin.cases c2_row79
    (Fin.cases c2_row80
    (Fin.cases c2_row81
    (Fin.cases c2_row82
    (Fin.cases c2_row83
    (Fin.cases c2_row84
    (Fin.cases c2_row85
    (Fin.cases c2_row86
    (Fin.cases c2_row87
    (Fin.cases c2_row88
    (Fin.cases c2_row89
    (Fin.cases c2_row90
    (Fin.cases c2_row91
    (Fin.cases c2_row92
    (Fin.cases c2_row93
    (Fin.cases c2_row94
    (Fin.cases c2_row95
    (Fin.cases c2_row96
    (Fin.cases c2_row97
    (Fin.cases c2_row98
    (Fin.cases c2_row99
    (Fin.cases c2_row100
    (Fin.cases c2_row101
    (Fin.cases c2_row102
    (Fin.cases c2_row103
    (Fin.cases c2_row104
    (Fin.cases c2_row105
    (Fin.cases c2_row106
    (Fin.cases c2_row107
    (Fin.cases c2_row108
    (Fin.cases c2_row109
    (Fin.cases c2_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_c2 : cMatrix * cMatrix = c2Matrix :=
  decode_mul _ _ _ c_small c_small c2_rows

end Lyons.Atlas111InvolutionWords
