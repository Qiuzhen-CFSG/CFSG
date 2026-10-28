module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: c5 times c5

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
private theorem c10_row0 :
    digitsEq 111 (rowProduct (c5Rows 0) c5Rows 111) (c10Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row1 :
    digitsEq 111 (rowProduct (c5Rows 1) c5Rows 111) (c10Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row2 :
    digitsEq 111 (rowProduct (c5Rows 2) c5Rows 111) (c10Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row3 :
    digitsEq 111 (rowProduct (c5Rows 3) c5Rows 111) (c10Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row4 :
    digitsEq 111 (rowProduct (c5Rows 4) c5Rows 111) (c10Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row5 :
    digitsEq 111 (rowProduct (c5Rows 5) c5Rows 111) (c10Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row6 :
    digitsEq 111 (rowProduct (c5Rows 6) c5Rows 111) (c10Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row7 :
    digitsEq 111 (rowProduct (c5Rows 7) c5Rows 111) (c10Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row8 :
    digitsEq 111 (rowProduct (c5Rows 8) c5Rows 111) (c10Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row9 :
    digitsEq 111 (rowProduct (c5Rows 9) c5Rows 111) (c10Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row10 :
    digitsEq 111 (rowProduct (c5Rows 10) c5Rows 111) (c10Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row11 :
    digitsEq 111 (rowProduct (c5Rows 11) c5Rows 111) (c10Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row12 :
    digitsEq 111 (rowProduct (c5Rows 12) c5Rows 111) (c10Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row13 :
    digitsEq 111 (rowProduct (c5Rows 13) c5Rows 111) (c10Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row14 :
    digitsEq 111 (rowProduct (c5Rows 14) c5Rows 111) (c10Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row15 :
    digitsEq 111 (rowProduct (c5Rows 15) c5Rows 111) (c10Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row16 :
    digitsEq 111 (rowProduct (c5Rows 16) c5Rows 111) (c10Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row17 :
    digitsEq 111 (rowProduct (c5Rows 17) c5Rows 111) (c10Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row18 :
    digitsEq 111 (rowProduct (c5Rows 18) c5Rows 111) (c10Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row19 :
    digitsEq 111 (rowProduct (c5Rows 19) c5Rows 111) (c10Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row20 :
    digitsEq 111 (rowProduct (c5Rows 20) c5Rows 111) (c10Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row21 :
    digitsEq 111 (rowProduct (c5Rows 21) c5Rows 111) (c10Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row22 :
    digitsEq 111 (rowProduct (c5Rows 22) c5Rows 111) (c10Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row23 :
    digitsEq 111 (rowProduct (c5Rows 23) c5Rows 111) (c10Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row24 :
    digitsEq 111 (rowProduct (c5Rows 24) c5Rows 111) (c10Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row25 :
    digitsEq 111 (rowProduct (c5Rows 25) c5Rows 111) (c10Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row26 :
    digitsEq 111 (rowProduct (c5Rows 26) c5Rows 111) (c10Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row27 :
    digitsEq 111 (rowProduct (c5Rows 27) c5Rows 111) (c10Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row28 :
    digitsEq 111 (rowProduct (c5Rows 28) c5Rows 111) (c10Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row29 :
    digitsEq 111 (rowProduct (c5Rows 29) c5Rows 111) (c10Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row30 :
    digitsEq 111 (rowProduct (c5Rows 30) c5Rows 111) (c10Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row31 :
    digitsEq 111 (rowProduct (c5Rows 31) c5Rows 111) (c10Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row32 :
    digitsEq 111 (rowProduct (c5Rows 32) c5Rows 111) (c10Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row33 :
    digitsEq 111 (rowProduct (c5Rows 33) c5Rows 111) (c10Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row34 :
    digitsEq 111 (rowProduct (c5Rows 34) c5Rows 111) (c10Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row35 :
    digitsEq 111 (rowProduct (c5Rows 35) c5Rows 111) (c10Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row36 :
    digitsEq 111 (rowProduct (c5Rows 36) c5Rows 111) (c10Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row37 :
    digitsEq 111 (rowProduct (c5Rows 37) c5Rows 111) (c10Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row38 :
    digitsEq 111 (rowProduct (c5Rows 38) c5Rows 111) (c10Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row39 :
    digitsEq 111 (rowProduct (c5Rows 39) c5Rows 111) (c10Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row40 :
    digitsEq 111 (rowProduct (c5Rows 40) c5Rows 111) (c10Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row41 :
    digitsEq 111 (rowProduct (c5Rows 41) c5Rows 111) (c10Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row42 :
    digitsEq 111 (rowProduct (c5Rows 42) c5Rows 111) (c10Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row43 :
    digitsEq 111 (rowProduct (c5Rows 43) c5Rows 111) (c10Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row44 :
    digitsEq 111 (rowProduct (c5Rows 44) c5Rows 111) (c10Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row45 :
    digitsEq 111 (rowProduct (c5Rows 45) c5Rows 111) (c10Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row46 :
    digitsEq 111 (rowProduct (c5Rows 46) c5Rows 111) (c10Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row47 :
    digitsEq 111 (rowProduct (c5Rows 47) c5Rows 111) (c10Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row48 :
    digitsEq 111 (rowProduct (c5Rows 48) c5Rows 111) (c10Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row49 :
    digitsEq 111 (rowProduct (c5Rows 49) c5Rows 111) (c10Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row50 :
    digitsEq 111 (rowProduct (c5Rows 50) c5Rows 111) (c10Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row51 :
    digitsEq 111 (rowProduct (c5Rows 51) c5Rows 111) (c10Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row52 :
    digitsEq 111 (rowProduct (c5Rows 52) c5Rows 111) (c10Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row53 :
    digitsEq 111 (rowProduct (c5Rows 53) c5Rows 111) (c10Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row54 :
    digitsEq 111 (rowProduct (c5Rows 54) c5Rows 111) (c10Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row55 :
    digitsEq 111 (rowProduct (c5Rows 55) c5Rows 111) (c10Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row56 :
    digitsEq 111 (rowProduct (c5Rows 56) c5Rows 111) (c10Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row57 :
    digitsEq 111 (rowProduct (c5Rows 57) c5Rows 111) (c10Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row58 :
    digitsEq 111 (rowProduct (c5Rows 58) c5Rows 111) (c10Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row59 :
    digitsEq 111 (rowProduct (c5Rows 59) c5Rows 111) (c10Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row60 :
    digitsEq 111 (rowProduct (c5Rows 60) c5Rows 111) (c10Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row61 :
    digitsEq 111 (rowProduct (c5Rows 61) c5Rows 111) (c10Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row62 :
    digitsEq 111 (rowProduct (c5Rows 62) c5Rows 111) (c10Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row63 :
    digitsEq 111 (rowProduct (c5Rows 63) c5Rows 111) (c10Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row64 :
    digitsEq 111 (rowProduct (c5Rows 64) c5Rows 111) (c10Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row65 :
    digitsEq 111 (rowProduct (c5Rows 65) c5Rows 111) (c10Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row66 :
    digitsEq 111 (rowProduct (c5Rows 66) c5Rows 111) (c10Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row67 :
    digitsEq 111 (rowProduct (c5Rows 67) c5Rows 111) (c10Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row68 :
    digitsEq 111 (rowProduct (c5Rows 68) c5Rows 111) (c10Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row69 :
    digitsEq 111 (rowProduct (c5Rows 69) c5Rows 111) (c10Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row70 :
    digitsEq 111 (rowProduct (c5Rows 70) c5Rows 111) (c10Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row71 :
    digitsEq 111 (rowProduct (c5Rows 71) c5Rows 111) (c10Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row72 :
    digitsEq 111 (rowProduct (c5Rows 72) c5Rows 111) (c10Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row73 :
    digitsEq 111 (rowProduct (c5Rows 73) c5Rows 111) (c10Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row74 :
    digitsEq 111 (rowProduct (c5Rows 74) c5Rows 111) (c10Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row75 :
    digitsEq 111 (rowProduct (c5Rows 75) c5Rows 111) (c10Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row76 :
    digitsEq 111 (rowProduct (c5Rows 76) c5Rows 111) (c10Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row77 :
    digitsEq 111 (rowProduct (c5Rows 77) c5Rows 111) (c10Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row78 :
    digitsEq 111 (rowProduct (c5Rows 78) c5Rows 111) (c10Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row79 :
    digitsEq 111 (rowProduct (c5Rows 79) c5Rows 111) (c10Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row80 :
    digitsEq 111 (rowProduct (c5Rows 80) c5Rows 111) (c10Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row81 :
    digitsEq 111 (rowProduct (c5Rows 81) c5Rows 111) (c10Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row82 :
    digitsEq 111 (rowProduct (c5Rows 82) c5Rows 111) (c10Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row83 :
    digitsEq 111 (rowProduct (c5Rows 83) c5Rows 111) (c10Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row84 :
    digitsEq 111 (rowProduct (c5Rows 84) c5Rows 111) (c10Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row85 :
    digitsEq 111 (rowProduct (c5Rows 85) c5Rows 111) (c10Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row86 :
    digitsEq 111 (rowProduct (c5Rows 86) c5Rows 111) (c10Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row87 :
    digitsEq 111 (rowProduct (c5Rows 87) c5Rows 111) (c10Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row88 :
    digitsEq 111 (rowProduct (c5Rows 88) c5Rows 111) (c10Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row89 :
    digitsEq 111 (rowProduct (c5Rows 89) c5Rows 111) (c10Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row90 :
    digitsEq 111 (rowProduct (c5Rows 90) c5Rows 111) (c10Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row91 :
    digitsEq 111 (rowProduct (c5Rows 91) c5Rows 111) (c10Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row92 :
    digitsEq 111 (rowProduct (c5Rows 92) c5Rows 111) (c10Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row93 :
    digitsEq 111 (rowProduct (c5Rows 93) c5Rows 111) (c10Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row94 :
    digitsEq 111 (rowProduct (c5Rows 94) c5Rows 111) (c10Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row95 :
    digitsEq 111 (rowProduct (c5Rows 95) c5Rows 111) (c10Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row96 :
    digitsEq 111 (rowProduct (c5Rows 96) c5Rows 111) (c10Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row97 :
    digitsEq 111 (rowProduct (c5Rows 97) c5Rows 111) (c10Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row98 :
    digitsEq 111 (rowProduct (c5Rows 98) c5Rows 111) (c10Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row99 :
    digitsEq 111 (rowProduct (c5Rows 99) c5Rows 111) (c10Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row100 :
    digitsEq 111 (rowProduct (c5Rows 100) c5Rows 111) (c10Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row101 :
    digitsEq 111 (rowProduct (c5Rows 101) c5Rows 111) (c10Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row102 :
    digitsEq 111 (rowProduct (c5Rows 102) c5Rows 111) (c10Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row103 :
    digitsEq 111 (rowProduct (c5Rows 103) c5Rows 111) (c10Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row104 :
    digitsEq 111 (rowProduct (c5Rows 104) c5Rows 111) (c10Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row105 :
    digitsEq 111 (rowProduct (c5Rows 105) c5Rows 111) (c10Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row106 :
    digitsEq 111 (rowProduct (c5Rows 106) c5Rows 111) (c10Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row107 :
    digitsEq 111 (rowProduct (c5Rows 107) c5Rows 111) (c10Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row108 :
    digitsEq 111 (rowProduct (c5Rows 108) c5Rows 111) (c10Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row109 :
    digitsEq 111 (rowProduct (c5Rows 109) c5Rows 111) (c10Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c10_row110 :
    digitsEq 111 (rowProduct (c5Rows 110) c5Rows 111) (c10Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem c10_rows : ∀ i,
    digitsEq 111 (rowProduct (c5Rows i) c5Rows 111) (c10Rows i) = true :=
  (Fin.cases c10_row0
    (Fin.cases c10_row1
    (Fin.cases c10_row2
    (Fin.cases c10_row3
    (Fin.cases c10_row4
    (Fin.cases c10_row5
    (Fin.cases c10_row6
    (Fin.cases c10_row7
    (Fin.cases c10_row8
    (Fin.cases c10_row9
    (Fin.cases c10_row10
    (Fin.cases c10_row11
    (Fin.cases c10_row12
    (Fin.cases c10_row13
    (Fin.cases c10_row14
    (Fin.cases c10_row15
    (Fin.cases c10_row16
    (Fin.cases c10_row17
    (Fin.cases c10_row18
    (Fin.cases c10_row19
    (Fin.cases c10_row20
    (Fin.cases c10_row21
    (Fin.cases c10_row22
    (Fin.cases c10_row23
    (Fin.cases c10_row24
    (Fin.cases c10_row25
    (Fin.cases c10_row26
    (Fin.cases c10_row27
    (Fin.cases c10_row28
    (Fin.cases c10_row29
    (Fin.cases c10_row30
    (Fin.cases c10_row31
    (Fin.cases c10_row32
    (Fin.cases c10_row33
    (Fin.cases c10_row34
    (Fin.cases c10_row35
    (Fin.cases c10_row36
    (Fin.cases c10_row37
    (Fin.cases c10_row38
    (Fin.cases c10_row39
    (Fin.cases c10_row40
    (Fin.cases c10_row41
    (Fin.cases c10_row42
    (Fin.cases c10_row43
    (Fin.cases c10_row44
    (Fin.cases c10_row45
    (Fin.cases c10_row46
    (Fin.cases c10_row47
    (Fin.cases c10_row48
    (Fin.cases c10_row49
    (Fin.cases c10_row50
    (Fin.cases c10_row51
    (Fin.cases c10_row52
    (Fin.cases c10_row53
    (Fin.cases c10_row54
    (Fin.cases c10_row55
    (Fin.cases c10_row56
    (Fin.cases c10_row57
    (Fin.cases c10_row58
    (Fin.cases c10_row59
    (Fin.cases c10_row60
    (Fin.cases c10_row61
    (Fin.cases c10_row62
    (Fin.cases c10_row63
    (Fin.cases c10_row64
    (Fin.cases c10_row65
    (Fin.cases c10_row66
    (Fin.cases c10_row67
    (Fin.cases c10_row68
    (Fin.cases c10_row69
    (Fin.cases c10_row70
    (Fin.cases c10_row71
    (Fin.cases c10_row72
    (Fin.cases c10_row73
    (Fin.cases c10_row74
    (Fin.cases c10_row75
    (Fin.cases c10_row76
    (Fin.cases c10_row77
    (Fin.cases c10_row78
    (Fin.cases c10_row79
    (Fin.cases c10_row80
    (Fin.cases c10_row81
    (Fin.cases c10_row82
    (Fin.cases c10_row83
    (Fin.cases c10_row84
    (Fin.cases c10_row85
    (Fin.cases c10_row86
    (Fin.cases c10_row87
    (Fin.cases c10_row88
    (Fin.cases c10_row89
    (Fin.cases c10_row90
    (Fin.cases c10_row91
    (Fin.cases c10_row92
    (Fin.cases c10_row93
    (Fin.cases c10_row94
    (Fin.cases c10_row95
    (Fin.cases c10_row96
    (Fin.cases c10_row97
    (Fin.cases c10_row98
    (Fin.cases c10_row99
    (Fin.cases c10_row100
    (Fin.cases c10_row101
    (Fin.cases c10_row102
    (Fin.cases c10_row103
    (Fin.cases c10_row104
    (Fin.cases c10_row105
    (Fin.cases c10_row106
    (Fin.cases c10_row107
    (Fin.cases c10_row108
    (Fin.cases c10_row109
    (Fin.cases c10_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_c10 : c5Matrix * c5Matrix = c10Matrix :=
  decode_mul _ _ _ c5_small c5_small c10_rows

end Lyons.Atlas111InvolutionWords
