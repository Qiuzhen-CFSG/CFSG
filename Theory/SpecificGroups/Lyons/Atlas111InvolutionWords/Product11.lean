module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: c2 times c2

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
private theorem c4_row0 :
    digitsEq 111 (rowProduct (c2Rows 0) c2Rows 111) (c4Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row1 :
    digitsEq 111 (rowProduct (c2Rows 1) c2Rows 111) (c4Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row2 :
    digitsEq 111 (rowProduct (c2Rows 2) c2Rows 111) (c4Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row3 :
    digitsEq 111 (rowProduct (c2Rows 3) c2Rows 111) (c4Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row4 :
    digitsEq 111 (rowProduct (c2Rows 4) c2Rows 111) (c4Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row5 :
    digitsEq 111 (rowProduct (c2Rows 5) c2Rows 111) (c4Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row6 :
    digitsEq 111 (rowProduct (c2Rows 6) c2Rows 111) (c4Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row7 :
    digitsEq 111 (rowProduct (c2Rows 7) c2Rows 111) (c4Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row8 :
    digitsEq 111 (rowProduct (c2Rows 8) c2Rows 111) (c4Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row9 :
    digitsEq 111 (rowProduct (c2Rows 9) c2Rows 111) (c4Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row10 :
    digitsEq 111 (rowProduct (c2Rows 10) c2Rows 111) (c4Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row11 :
    digitsEq 111 (rowProduct (c2Rows 11) c2Rows 111) (c4Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row12 :
    digitsEq 111 (rowProduct (c2Rows 12) c2Rows 111) (c4Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row13 :
    digitsEq 111 (rowProduct (c2Rows 13) c2Rows 111) (c4Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row14 :
    digitsEq 111 (rowProduct (c2Rows 14) c2Rows 111) (c4Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row15 :
    digitsEq 111 (rowProduct (c2Rows 15) c2Rows 111) (c4Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row16 :
    digitsEq 111 (rowProduct (c2Rows 16) c2Rows 111) (c4Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row17 :
    digitsEq 111 (rowProduct (c2Rows 17) c2Rows 111) (c4Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row18 :
    digitsEq 111 (rowProduct (c2Rows 18) c2Rows 111) (c4Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row19 :
    digitsEq 111 (rowProduct (c2Rows 19) c2Rows 111) (c4Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row20 :
    digitsEq 111 (rowProduct (c2Rows 20) c2Rows 111) (c4Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row21 :
    digitsEq 111 (rowProduct (c2Rows 21) c2Rows 111) (c4Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row22 :
    digitsEq 111 (rowProduct (c2Rows 22) c2Rows 111) (c4Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row23 :
    digitsEq 111 (rowProduct (c2Rows 23) c2Rows 111) (c4Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row24 :
    digitsEq 111 (rowProduct (c2Rows 24) c2Rows 111) (c4Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row25 :
    digitsEq 111 (rowProduct (c2Rows 25) c2Rows 111) (c4Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row26 :
    digitsEq 111 (rowProduct (c2Rows 26) c2Rows 111) (c4Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row27 :
    digitsEq 111 (rowProduct (c2Rows 27) c2Rows 111) (c4Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row28 :
    digitsEq 111 (rowProduct (c2Rows 28) c2Rows 111) (c4Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row29 :
    digitsEq 111 (rowProduct (c2Rows 29) c2Rows 111) (c4Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row30 :
    digitsEq 111 (rowProduct (c2Rows 30) c2Rows 111) (c4Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row31 :
    digitsEq 111 (rowProduct (c2Rows 31) c2Rows 111) (c4Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row32 :
    digitsEq 111 (rowProduct (c2Rows 32) c2Rows 111) (c4Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row33 :
    digitsEq 111 (rowProduct (c2Rows 33) c2Rows 111) (c4Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row34 :
    digitsEq 111 (rowProduct (c2Rows 34) c2Rows 111) (c4Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row35 :
    digitsEq 111 (rowProduct (c2Rows 35) c2Rows 111) (c4Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row36 :
    digitsEq 111 (rowProduct (c2Rows 36) c2Rows 111) (c4Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row37 :
    digitsEq 111 (rowProduct (c2Rows 37) c2Rows 111) (c4Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row38 :
    digitsEq 111 (rowProduct (c2Rows 38) c2Rows 111) (c4Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row39 :
    digitsEq 111 (rowProduct (c2Rows 39) c2Rows 111) (c4Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row40 :
    digitsEq 111 (rowProduct (c2Rows 40) c2Rows 111) (c4Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row41 :
    digitsEq 111 (rowProduct (c2Rows 41) c2Rows 111) (c4Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row42 :
    digitsEq 111 (rowProduct (c2Rows 42) c2Rows 111) (c4Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row43 :
    digitsEq 111 (rowProduct (c2Rows 43) c2Rows 111) (c4Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row44 :
    digitsEq 111 (rowProduct (c2Rows 44) c2Rows 111) (c4Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row45 :
    digitsEq 111 (rowProduct (c2Rows 45) c2Rows 111) (c4Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row46 :
    digitsEq 111 (rowProduct (c2Rows 46) c2Rows 111) (c4Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row47 :
    digitsEq 111 (rowProduct (c2Rows 47) c2Rows 111) (c4Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row48 :
    digitsEq 111 (rowProduct (c2Rows 48) c2Rows 111) (c4Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row49 :
    digitsEq 111 (rowProduct (c2Rows 49) c2Rows 111) (c4Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row50 :
    digitsEq 111 (rowProduct (c2Rows 50) c2Rows 111) (c4Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row51 :
    digitsEq 111 (rowProduct (c2Rows 51) c2Rows 111) (c4Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row52 :
    digitsEq 111 (rowProduct (c2Rows 52) c2Rows 111) (c4Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row53 :
    digitsEq 111 (rowProduct (c2Rows 53) c2Rows 111) (c4Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row54 :
    digitsEq 111 (rowProduct (c2Rows 54) c2Rows 111) (c4Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row55 :
    digitsEq 111 (rowProduct (c2Rows 55) c2Rows 111) (c4Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row56 :
    digitsEq 111 (rowProduct (c2Rows 56) c2Rows 111) (c4Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row57 :
    digitsEq 111 (rowProduct (c2Rows 57) c2Rows 111) (c4Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row58 :
    digitsEq 111 (rowProduct (c2Rows 58) c2Rows 111) (c4Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row59 :
    digitsEq 111 (rowProduct (c2Rows 59) c2Rows 111) (c4Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row60 :
    digitsEq 111 (rowProduct (c2Rows 60) c2Rows 111) (c4Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row61 :
    digitsEq 111 (rowProduct (c2Rows 61) c2Rows 111) (c4Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row62 :
    digitsEq 111 (rowProduct (c2Rows 62) c2Rows 111) (c4Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row63 :
    digitsEq 111 (rowProduct (c2Rows 63) c2Rows 111) (c4Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row64 :
    digitsEq 111 (rowProduct (c2Rows 64) c2Rows 111) (c4Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row65 :
    digitsEq 111 (rowProduct (c2Rows 65) c2Rows 111) (c4Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row66 :
    digitsEq 111 (rowProduct (c2Rows 66) c2Rows 111) (c4Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row67 :
    digitsEq 111 (rowProduct (c2Rows 67) c2Rows 111) (c4Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row68 :
    digitsEq 111 (rowProduct (c2Rows 68) c2Rows 111) (c4Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row69 :
    digitsEq 111 (rowProduct (c2Rows 69) c2Rows 111) (c4Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row70 :
    digitsEq 111 (rowProduct (c2Rows 70) c2Rows 111) (c4Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row71 :
    digitsEq 111 (rowProduct (c2Rows 71) c2Rows 111) (c4Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row72 :
    digitsEq 111 (rowProduct (c2Rows 72) c2Rows 111) (c4Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row73 :
    digitsEq 111 (rowProduct (c2Rows 73) c2Rows 111) (c4Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row74 :
    digitsEq 111 (rowProduct (c2Rows 74) c2Rows 111) (c4Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row75 :
    digitsEq 111 (rowProduct (c2Rows 75) c2Rows 111) (c4Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row76 :
    digitsEq 111 (rowProduct (c2Rows 76) c2Rows 111) (c4Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row77 :
    digitsEq 111 (rowProduct (c2Rows 77) c2Rows 111) (c4Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row78 :
    digitsEq 111 (rowProduct (c2Rows 78) c2Rows 111) (c4Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row79 :
    digitsEq 111 (rowProduct (c2Rows 79) c2Rows 111) (c4Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row80 :
    digitsEq 111 (rowProduct (c2Rows 80) c2Rows 111) (c4Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row81 :
    digitsEq 111 (rowProduct (c2Rows 81) c2Rows 111) (c4Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row82 :
    digitsEq 111 (rowProduct (c2Rows 82) c2Rows 111) (c4Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row83 :
    digitsEq 111 (rowProduct (c2Rows 83) c2Rows 111) (c4Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row84 :
    digitsEq 111 (rowProduct (c2Rows 84) c2Rows 111) (c4Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row85 :
    digitsEq 111 (rowProduct (c2Rows 85) c2Rows 111) (c4Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row86 :
    digitsEq 111 (rowProduct (c2Rows 86) c2Rows 111) (c4Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row87 :
    digitsEq 111 (rowProduct (c2Rows 87) c2Rows 111) (c4Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row88 :
    digitsEq 111 (rowProduct (c2Rows 88) c2Rows 111) (c4Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row89 :
    digitsEq 111 (rowProduct (c2Rows 89) c2Rows 111) (c4Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row90 :
    digitsEq 111 (rowProduct (c2Rows 90) c2Rows 111) (c4Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row91 :
    digitsEq 111 (rowProduct (c2Rows 91) c2Rows 111) (c4Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row92 :
    digitsEq 111 (rowProduct (c2Rows 92) c2Rows 111) (c4Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row93 :
    digitsEq 111 (rowProduct (c2Rows 93) c2Rows 111) (c4Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row94 :
    digitsEq 111 (rowProduct (c2Rows 94) c2Rows 111) (c4Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row95 :
    digitsEq 111 (rowProduct (c2Rows 95) c2Rows 111) (c4Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row96 :
    digitsEq 111 (rowProduct (c2Rows 96) c2Rows 111) (c4Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row97 :
    digitsEq 111 (rowProduct (c2Rows 97) c2Rows 111) (c4Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row98 :
    digitsEq 111 (rowProduct (c2Rows 98) c2Rows 111) (c4Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row99 :
    digitsEq 111 (rowProduct (c2Rows 99) c2Rows 111) (c4Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row100 :
    digitsEq 111 (rowProduct (c2Rows 100) c2Rows 111) (c4Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row101 :
    digitsEq 111 (rowProduct (c2Rows 101) c2Rows 111) (c4Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row102 :
    digitsEq 111 (rowProduct (c2Rows 102) c2Rows 111) (c4Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row103 :
    digitsEq 111 (rowProduct (c2Rows 103) c2Rows 111) (c4Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row104 :
    digitsEq 111 (rowProduct (c2Rows 104) c2Rows 111) (c4Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row105 :
    digitsEq 111 (rowProduct (c2Rows 105) c2Rows 111) (c4Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row106 :
    digitsEq 111 (rowProduct (c2Rows 106) c2Rows 111) (c4Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row107 :
    digitsEq 111 (rowProduct (c2Rows 107) c2Rows 111) (c4Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row108 :
    digitsEq 111 (rowProduct (c2Rows 108) c2Rows 111) (c4Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row109 :
    digitsEq 111 (rowProduct (c2Rows 109) c2Rows 111) (c4Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c4_row110 :
    digitsEq 111 (rowProduct (c2Rows 110) c2Rows 111) (c4Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem c4_rows : ∀ i,
    digitsEq 111 (rowProduct (c2Rows i) c2Rows 111) (c4Rows i) = true :=
  (Fin.cases c4_row0
    (Fin.cases c4_row1
    (Fin.cases c4_row2
    (Fin.cases c4_row3
    (Fin.cases c4_row4
    (Fin.cases c4_row5
    (Fin.cases c4_row6
    (Fin.cases c4_row7
    (Fin.cases c4_row8
    (Fin.cases c4_row9
    (Fin.cases c4_row10
    (Fin.cases c4_row11
    (Fin.cases c4_row12
    (Fin.cases c4_row13
    (Fin.cases c4_row14
    (Fin.cases c4_row15
    (Fin.cases c4_row16
    (Fin.cases c4_row17
    (Fin.cases c4_row18
    (Fin.cases c4_row19
    (Fin.cases c4_row20
    (Fin.cases c4_row21
    (Fin.cases c4_row22
    (Fin.cases c4_row23
    (Fin.cases c4_row24
    (Fin.cases c4_row25
    (Fin.cases c4_row26
    (Fin.cases c4_row27
    (Fin.cases c4_row28
    (Fin.cases c4_row29
    (Fin.cases c4_row30
    (Fin.cases c4_row31
    (Fin.cases c4_row32
    (Fin.cases c4_row33
    (Fin.cases c4_row34
    (Fin.cases c4_row35
    (Fin.cases c4_row36
    (Fin.cases c4_row37
    (Fin.cases c4_row38
    (Fin.cases c4_row39
    (Fin.cases c4_row40
    (Fin.cases c4_row41
    (Fin.cases c4_row42
    (Fin.cases c4_row43
    (Fin.cases c4_row44
    (Fin.cases c4_row45
    (Fin.cases c4_row46
    (Fin.cases c4_row47
    (Fin.cases c4_row48
    (Fin.cases c4_row49
    (Fin.cases c4_row50
    (Fin.cases c4_row51
    (Fin.cases c4_row52
    (Fin.cases c4_row53
    (Fin.cases c4_row54
    (Fin.cases c4_row55
    (Fin.cases c4_row56
    (Fin.cases c4_row57
    (Fin.cases c4_row58
    (Fin.cases c4_row59
    (Fin.cases c4_row60
    (Fin.cases c4_row61
    (Fin.cases c4_row62
    (Fin.cases c4_row63
    (Fin.cases c4_row64
    (Fin.cases c4_row65
    (Fin.cases c4_row66
    (Fin.cases c4_row67
    (Fin.cases c4_row68
    (Fin.cases c4_row69
    (Fin.cases c4_row70
    (Fin.cases c4_row71
    (Fin.cases c4_row72
    (Fin.cases c4_row73
    (Fin.cases c4_row74
    (Fin.cases c4_row75
    (Fin.cases c4_row76
    (Fin.cases c4_row77
    (Fin.cases c4_row78
    (Fin.cases c4_row79
    (Fin.cases c4_row80
    (Fin.cases c4_row81
    (Fin.cases c4_row82
    (Fin.cases c4_row83
    (Fin.cases c4_row84
    (Fin.cases c4_row85
    (Fin.cases c4_row86
    (Fin.cases c4_row87
    (Fin.cases c4_row88
    (Fin.cases c4_row89
    (Fin.cases c4_row90
    (Fin.cases c4_row91
    (Fin.cases c4_row92
    (Fin.cases c4_row93
    (Fin.cases c4_row94
    (Fin.cases c4_row95
    (Fin.cases c4_row96
    (Fin.cases c4_row97
    (Fin.cases c4_row98
    (Fin.cases c4_row99
    (Fin.cases c4_row100
    (Fin.cases c4_row101
    (Fin.cases c4_row102
    (Fin.cases c4_row103
    (Fin.cases c4_row104
    (Fin.cases c4_row105
    (Fin.cases c4_row106
    (Fin.cases c4_row107
    (Fin.cases c4_row108
    (Fin.cases c4_row109
    (Fin.cases c4_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_c4 : c2Matrix * c2Matrix = c4Matrix :=
  decode_mul _ _ _ c2_small c2_small c4_rows

end Lyons.Atlas111InvolutionWords
