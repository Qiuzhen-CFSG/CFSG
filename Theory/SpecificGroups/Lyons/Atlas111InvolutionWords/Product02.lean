module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: ab times r5

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
private theorem r6_row0 :
    digitsEq 111 (rowProduct (abRows 0) r5Rows 111) (r6Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row1 :
    digitsEq 111 (rowProduct (abRows 1) r5Rows 111) (r6Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row2 :
    digitsEq 111 (rowProduct (abRows 2) r5Rows 111) (r6Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row3 :
    digitsEq 111 (rowProduct (abRows 3) r5Rows 111) (r6Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row4 :
    digitsEq 111 (rowProduct (abRows 4) r5Rows 111) (r6Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row5 :
    digitsEq 111 (rowProduct (abRows 5) r5Rows 111) (r6Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row6 :
    digitsEq 111 (rowProduct (abRows 6) r5Rows 111) (r6Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row7 :
    digitsEq 111 (rowProduct (abRows 7) r5Rows 111) (r6Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row8 :
    digitsEq 111 (rowProduct (abRows 8) r5Rows 111) (r6Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row9 :
    digitsEq 111 (rowProduct (abRows 9) r5Rows 111) (r6Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row10 :
    digitsEq 111 (rowProduct (abRows 10) r5Rows 111) (r6Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row11 :
    digitsEq 111 (rowProduct (abRows 11) r5Rows 111) (r6Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row12 :
    digitsEq 111 (rowProduct (abRows 12) r5Rows 111) (r6Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row13 :
    digitsEq 111 (rowProduct (abRows 13) r5Rows 111) (r6Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row14 :
    digitsEq 111 (rowProduct (abRows 14) r5Rows 111) (r6Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row15 :
    digitsEq 111 (rowProduct (abRows 15) r5Rows 111) (r6Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row16 :
    digitsEq 111 (rowProduct (abRows 16) r5Rows 111) (r6Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row17 :
    digitsEq 111 (rowProduct (abRows 17) r5Rows 111) (r6Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row18 :
    digitsEq 111 (rowProduct (abRows 18) r5Rows 111) (r6Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row19 :
    digitsEq 111 (rowProduct (abRows 19) r5Rows 111) (r6Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row20 :
    digitsEq 111 (rowProduct (abRows 20) r5Rows 111) (r6Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row21 :
    digitsEq 111 (rowProduct (abRows 21) r5Rows 111) (r6Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row22 :
    digitsEq 111 (rowProduct (abRows 22) r5Rows 111) (r6Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row23 :
    digitsEq 111 (rowProduct (abRows 23) r5Rows 111) (r6Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row24 :
    digitsEq 111 (rowProduct (abRows 24) r5Rows 111) (r6Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row25 :
    digitsEq 111 (rowProduct (abRows 25) r5Rows 111) (r6Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row26 :
    digitsEq 111 (rowProduct (abRows 26) r5Rows 111) (r6Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row27 :
    digitsEq 111 (rowProduct (abRows 27) r5Rows 111) (r6Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row28 :
    digitsEq 111 (rowProduct (abRows 28) r5Rows 111) (r6Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row29 :
    digitsEq 111 (rowProduct (abRows 29) r5Rows 111) (r6Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row30 :
    digitsEq 111 (rowProduct (abRows 30) r5Rows 111) (r6Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row31 :
    digitsEq 111 (rowProduct (abRows 31) r5Rows 111) (r6Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row32 :
    digitsEq 111 (rowProduct (abRows 32) r5Rows 111) (r6Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row33 :
    digitsEq 111 (rowProduct (abRows 33) r5Rows 111) (r6Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row34 :
    digitsEq 111 (rowProduct (abRows 34) r5Rows 111) (r6Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row35 :
    digitsEq 111 (rowProduct (abRows 35) r5Rows 111) (r6Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row36 :
    digitsEq 111 (rowProduct (abRows 36) r5Rows 111) (r6Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row37 :
    digitsEq 111 (rowProduct (abRows 37) r5Rows 111) (r6Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row38 :
    digitsEq 111 (rowProduct (abRows 38) r5Rows 111) (r6Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row39 :
    digitsEq 111 (rowProduct (abRows 39) r5Rows 111) (r6Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row40 :
    digitsEq 111 (rowProduct (abRows 40) r5Rows 111) (r6Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row41 :
    digitsEq 111 (rowProduct (abRows 41) r5Rows 111) (r6Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row42 :
    digitsEq 111 (rowProduct (abRows 42) r5Rows 111) (r6Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row43 :
    digitsEq 111 (rowProduct (abRows 43) r5Rows 111) (r6Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row44 :
    digitsEq 111 (rowProduct (abRows 44) r5Rows 111) (r6Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row45 :
    digitsEq 111 (rowProduct (abRows 45) r5Rows 111) (r6Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row46 :
    digitsEq 111 (rowProduct (abRows 46) r5Rows 111) (r6Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row47 :
    digitsEq 111 (rowProduct (abRows 47) r5Rows 111) (r6Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row48 :
    digitsEq 111 (rowProduct (abRows 48) r5Rows 111) (r6Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row49 :
    digitsEq 111 (rowProduct (abRows 49) r5Rows 111) (r6Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row50 :
    digitsEq 111 (rowProduct (abRows 50) r5Rows 111) (r6Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row51 :
    digitsEq 111 (rowProduct (abRows 51) r5Rows 111) (r6Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row52 :
    digitsEq 111 (rowProduct (abRows 52) r5Rows 111) (r6Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row53 :
    digitsEq 111 (rowProduct (abRows 53) r5Rows 111) (r6Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row54 :
    digitsEq 111 (rowProduct (abRows 54) r5Rows 111) (r6Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row55 :
    digitsEq 111 (rowProduct (abRows 55) r5Rows 111) (r6Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row56 :
    digitsEq 111 (rowProduct (abRows 56) r5Rows 111) (r6Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row57 :
    digitsEq 111 (rowProduct (abRows 57) r5Rows 111) (r6Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row58 :
    digitsEq 111 (rowProduct (abRows 58) r5Rows 111) (r6Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row59 :
    digitsEq 111 (rowProduct (abRows 59) r5Rows 111) (r6Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row60 :
    digitsEq 111 (rowProduct (abRows 60) r5Rows 111) (r6Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row61 :
    digitsEq 111 (rowProduct (abRows 61) r5Rows 111) (r6Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row62 :
    digitsEq 111 (rowProduct (abRows 62) r5Rows 111) (r6Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row63 :
    digitsEq 111 (rowProduct (abRows 63) r5Rows 111) (r6Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row64 :
    digitsEq 111 (rowProduct (abRows 64) r5Rows 111) (r6Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row65 :
    digitsEq 111 (rowProduct (abRows 65) r5Rows 111) (r6Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row66 :
    digitsEq 111 (rowProduct (abRows 66) r5Rows 111) (r6Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row67 :
    digitsEq 111 (rowProduct (abRows 67) r5Rows 111) (r6Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row68 :
    digitsEq 111 (rowProduct (abRows 68) r5Rows 111) (r6Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row69 :
    digitsEq 111 (rowProduct (abRows 69) r5Rows 111) (r6Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row70 :
    digitsEq 111 (rowProduct (abRows 70) r5Rows 111) (r6Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row71 :
    digitsEq 111 (rowProduct (abRows 71) r5Rows 111) (r6Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row72 :
    digitsEq 111 (rowProduct (abRows 72) r5Rows 111) (r6Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row73 :
    digitsEq 111 (rowProduct (abRows 73) r5Rows 111) (r6Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row74 :
    digitsEq 111 (rowProduct (abRows 74) r5Rows 111) (r6Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row75 :
    digitsEq 111 (rowProduct (abRows 75) r5Rows 111) (r6Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row76 :
    digitsEq 111 (rowProduct (abRows 76) r5Rows 111) (r6Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row77 :
    digitsEq 111 (rowProduct (abRows 77) r5Rows 111) (r6Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row78 :
    digitsEq 111 (rowProduct (abRows 78) r5Rows 111) (r6Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row79 :
    digitsEq 111 (rowProduct (abRows 79) r5Rows 111) (r6Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row80 :
    digitsEq 111 (rowProduct (abRows 80) r5Rows 111) (r6Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row81 :
    digitsEq 111 (rowProduct (abRows 81) r5Rows 111) (r6Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row82 :
    digitsEq 111 (rowProduct (abRows 82) r5Rows 111) (r6Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row83 :
    digitsEq 111 (rowProduct (abRows 83) r5Rows 111) (r6Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row84 :
    digitsEq 111 (rowProduct (abRows 84) r5Rows 111) (r6Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row85 :
    digitsEq 111 (rowProduct (abRows 85) r5Rows 111) (r6Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row86 :
    digitsEq 111 (rowProduct (abRows 86) r5Rows 111) (r6Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row87 :
    digitsEq 111 (rowProduct (abRows 87) r5Rows 111) (r6Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row88 :
    digitsEq 111 (rowProduct (abRows 88) r5Rows 111) (r6Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row89 :
    digitsEq 111 (rowProduct (abRows 89) r5Rows 111) (r6Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row90 :
    digitsEq 111 (rowProduct (abRows 90) r5Rows 111) (r6Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row91 :
    digitsEq 111 (rowProduct (abRows 91) r5Rows 111) (r6Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row92 :
    digitsEq 111 (rowProduct (abRows 92) r5Rows 111) (r6Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row93 :
    digitsEq 111 (rowProduct (abRows 93) r5Rows 111) (r6Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row94 :
    digitsEq 111 (rowProduct (abRows 94) r5Rows 111) (r6Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row95 :
    digitsEq 111 (rowProduct (abRows 95) r5Rows 111) (r6Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row96 :
    digitsEq 111 (rowProduct (abRows 96) r5Rows 111) (r6Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row97 :
    digitsEq 111 (rowProduct (abRows 97) r5Rows 111) (r6Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row98 :
    digitsEq 111 (rowProduct (abRows 98) r5Rows 111) (r6Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row99 :
    digitsEq 111 (rowProduct (abRows 99) r5Rows 111) (r6Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row100 :
    digitsEq 111 (rowProduct (abRows 100) r5Rows 111) (r6Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row101 :
    digitsEq 111 (rowProduct (abRows 101) r5Rows 111) (r6Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row102 :
    digitsEq 111 (rowProduct (abRows 102) r5Rows 111) (r6Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row103 :
    digitsEq 111 (rowProduct (abRows 103) r5Rows 111) (r6Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row104 :
    digitsEq 111 (rowProduct (abRows 104) r5Rows 111) (r6Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row105 :
    digitsEq 111 (rowProduct (abRows 105) r5Rows 111) (r6Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row106 :
    digitsEq 111 (rowProduct (abRows 106) r5Rows 111) (r6Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row107 :
    digitsEq 111 (rowProduct (abRows 107) r5Rows 111) (r6Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row108 :
    digitsEq 111 (rowProduct (abRows 108) r5Rows 111) (r6Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row109 :
    digitsEq 111 (rowProduct (abRows 109) r5Rows 111) (r6Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r6_row110 :
    digitsEq 111 (rowProduct (abRows 110) r5Rows 111) (r6Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem r6_rows : ∀ i,
    digitsEq 111 (rowProduct (abRows i) r5Rows 111) (r6Rows i) = true :=
  (Fin.cases r6_row0
    (Fin.cases r6_row1
    (Fin.cases r6_row2
    (Fin.cases r6_row3
    (Fin.cases r6_row4
    (Fin.cases r6_row5
    (Fin.cases r6_row6
    (Fin.cases r6_row7
    (Fin.cases r6_row8
    (Fin.cases r6_row9
    (Fin.cases r6_row10
    (Fin.cases r6_row11
    (Fin.cases r6_row12
    (Fin.cases r6_row13
    (Fin.cases r6_row14
    (Fin.cases r6_row15
    (Fin.cases r6_row16
    (Fin.cases r6_row17
    (Fin.cases r6_row18
    (Fin.cases r6_row19
    (Fin.cases r6_row20
    (Fin.cases r6_row21
    (Fin.cases r6_row22
    (Fin.cases r6_row23
    (Fin.cases r6_row24
    (Fin.cases r6_row25
    (Fin.cases r6_row26
    (Fin.cases r6_row27
    (Fin.cases r6_row28
    (Fin.cases r6_row29
    (Fin.cases r6_row30
    (Fin.cases r6_row31
    (Fin.cases r6_row32
    (Fin.cases r6_row33
    (Fin.cases r6_row34
    (Fin.cases r6_row35
    (Fin.cases r6_row36
    (Fin.cases r6_row37
    (Fin.cases r6_row38
    (Fin.cases r6_row39
    (Fin.cases r6_row40
    (Fin.cases r6_row41
    (Fin.cases r6_row42
    (Fin.cases r6_row43
    (Fin.cases r6_row44
    (Fin.cases r6_row45
    (Fin.cases r6_row46
    (Fin.cases r6_row47
    (Fin.cases r6_row48
    (Fin.cases r6_row49
    (Fin.cases r6_row50
    (Fin.cases r6_row51
    (Fin.cases r6_row52
    (Fin.cases r6_row53
    (Fin.cases r6_row54
    (Fin.cases r6_row55
    (Fin.cases r6_row56
    (Fin.cases r6_row57
    (Fin.cases r6_row58
    (Fin.cases r6_row59
    (Fin.cases r6_row60
    (Fin.cases r6_row61
    (Fin.cases r6_row62
    (Fin.cases r6_row63
    (Fin.cases r6_row64
    (Fin.cases r6_row65
    (Fin.cases r6_row66
    (Fin.cases r6_row67
    (Fin.cases r6_row68
    (Fin.cases r6_row69
    (Fin.cases r6_row70
    (Fin.cases r6_row71
    (Fin.cases r6_row72
    (Fin.cases r6_row73
    (Fin.cases r6_row74
    (Fin.cases r6_row75
    (Fin.cases r6_row76
    (Fin.cases r6_row77
    (Fin.cases r6_row78
    (Fin.cases r6_row79
    (Fin.cases r6_row80
    (Fin.cases r6_row81
    (Fin.cases r6_row82
    (Fin.cases r6_row83
    (Fin.cases r6_row84
    (Fin.cases r6_row85
    (Fin.cases r6_row86
    (Fin.cases r6_row87
    (Fin.cases r6_row88
    (Fin.cases r6_row89
    (Fin.cases r6_row90
    (Fin.cases r6_row91
    (Fin.cases r6_row92
    (Fin.cases r6_row93
    (Fin.cases r6_row94
    (Fin.cases r6_row95
    (Fin.cases r6_row96
    (Fin.cases r6_row97
    (Fin.cases r6_row98
    (Fin.cases r6_row99
    (Fin.cases r6_row100
    (Fin.cases r6_row101
    (Fin.cases r6_row102
    (Fin.cases r6_row103
    (Fin.cases r6_row104
    (Fin.cases r6_row105
    (Fin.cases r6_row106
    (Fin.cases r6_row107
    (Fin.cases r6_row108
    (Fin.cases r6_row109
    (Fin.cases r6_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_r6 : abMatrix * r5Matrix = r6Matrix :=
  decode_mul _ _ _ ab_small r5_small r6_rows

end Lyons.Atlas111InvolutionWords
