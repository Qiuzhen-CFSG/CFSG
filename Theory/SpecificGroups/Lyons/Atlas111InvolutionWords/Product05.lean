module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: r9 times r4

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
private theorem r10_row0 :
    digitsEq 111 (rowProduct (r9Rows 0) r4Rows 111) (r10Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row1 :
    digitsEq 111 (rowProduct (r9Rows 1) r4Rows 111) (r10Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row2 :
    digitsEq 111 (rowProduct (r9Rows 2) r4Rows 111) (r10Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row3 :
    digitsEq 111 (rowProduct (r9Rows 3) r4Rows 111) (r10Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row4 :
    digitsEq 111 (rowProduct (r9Rows 4) r4Rows 111) (r10Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row5 :
    digitsEq 111 (rowProduct (r9Rows 5) r4Rows 111) (r10Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row6 :
    digitsEq 111 (rowProduct (r9Rows 6) r4Rows 111) (r10Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row7 :
    digitsEq 111 (rowProduct (r9Rows 7) r4Rows 111) (r10Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row8 :
    digitsEq 111 (rowProduct (r9Rows 8) r4Rows 111) (r10Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row9 :
    digitsEq 111 (rowProduct (r9Rows 9) r4Rows 111) (r10Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row10 :
    digitsEq 111 (rowProduct (r9Rows 10) r4Rows 111) (r10Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row11 :
    digitsEq 111 (rowProduct (r9Rows 11) r4Rows 111) (r10Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row12 :
    digitsEq 111 (rowProduct (r9Rows 12) r4Rows 111) (r10Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row13 :
    digitsEq 111 (rowProduct (r9Rows 13) r4Rows 111) (r10Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row14 :
    digitsEq 111 (rowProduct (r9Rows 14) r4Rows 111) (r10Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row15 :
    digitsEq 111 (rowProduct (r9Rows 15) r4Rows 111) (r10Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row16 :
    digitsEq 111 (rowProduct (r9Rows 16) r4Rows 111) (r10Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row17 :
    digitsEq 111 (rowProduct (r9Rows 17) r4Rows 111) (r10Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row18 :
    digitsEq 111 (rowProduct (r9Rows 18) r4Rows 111) (r10Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row19 :
    digitsEq 111 (rowProduct (r9Rows 19) r4Rows 111) (r10Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row20 :
    digitsEq 111 (rowProduct (r9Rows 20) r4Rows 111) (r10Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row21 :
    digitsEq 111 (rowProduct (r9Rows 21) r4Rows 111) (r10Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row22 :
    digitsEq 111 (rowProduct (r9Rows 22) r4Rows 111) (r10Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row23 :
    digitsEq 111 (rowProduct (r9Rows 23) r4Rows 111) (r10Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row24 :
    digitsEq 111 (rowProduct (r9Rows 24) r4Rows 111) (r10Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row25 :
    digitsEq 111 (rowProduct (r9Rows 25) r4Rows 111) (r10Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row26 :
    digitsEq 111 (rowProduct (r9Rows 26) r4Rows 111) (r10Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row27 :
    digitsEq 111 (rowProduct (r9Rows 27) r4Rows 111) (r10Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row28 :
    digitsEq 111 (rowProduct (r9Rows 28) r4Rows 111) (r10Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row29 :
    digitsEq 111 (rowProduct (r9Rows 29) r4Rows 111) (r10Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row30 :
    digitsEq 111 (rowProduct (r9Rows 30) r4Rows 111) (r10Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row31 :
    digitsEq 111 (rowProduct (r9Rows 31) r4Rows 111) (r10Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row32 :
    digitsEq 111 (rowProduct (r9Rows 32) r4Rows 111) (r10Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row33 :
    digitsEq 111 (rowProduct (r9Rows 33) r4Rows 111) (r10Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row34 :
    digitsEq 111 (rowProduct (r9Rows 34) r4Rows 111) (r10Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row35 :
    digitsEq 111 (rowProduct (r9Rows 35) r4Rows 111) (r10Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row36 :
    digitsEq 111 (rowProduct (r9Rows 36) r4Rows 111) (r10Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row37 :
    digitsEq 111 (rowProduct (r9Rows 37) r4Rows 111) (r10Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row38 :
    digitsEq 111 (rowProduct (r9Rows 38) r4Rows 111) (r10Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row39 :
    digitsEq 111 (rowProduct (r9Rows 39) r4Rows 111) (r10Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row40 :
    digitsEq 111 (rowProduct (r9Rows 40) r4Rows 111) (r10Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row41 :
    digitsEq 111 (rowProduct (r9Rows 41) r4Rows 111) (r10Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row42 :
    digitsEq 111 (rowProduct (r9Rows 42) r4Rows 111) (r10Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row43 :
    digitsEq 111 (rowProduct (r9Rows 43) r4Rows 111) (r10Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row44 :
    digitsEq 111 (rowProduct (r9Rows 44) r4Rows 111) (r10Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row45 :
    digitsEq 111 (rowProduct (r9Rows 45) r4Rows 111) (r10Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row46 :
    digitsEq 111 (rowProduct (r9Rows 46) r4Rows 111) (r10Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row47 :
    digitsEq 111 (rowProduct (r9Rows 47) r4Rows 111) (r10Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row48 :
    digitsEq 111 (rowProduct (r9Rows 48) r4Rows 111) (r10Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row49 :
    digitsEq 111 (rowProduct (r9Rows 49) r4Rows 111) (r10Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row50 :
    digitsEq 111 (rowProduct (r9Rows 50) r4Rows 111) (r10Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row51 :
    digitsEq 111 (rowProduct (r9Rows 51) r4Rows 111) (r10Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row52 :
    digitsEq 111 (rowProduct (r9Rows 52) r4Rows 111) (r10Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row53 :
    digitsEq 111 (rowProduct (r9Rows 53) r4Rows 111) (r10Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row54 :
    digitsEq 111 (rowProduct (r9Rows 54) r4Rows 111) (r10Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row55 :
    digitsEq 111 (rowProduct (r9Rows 55) r4Rows 111) (r10Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row56 :
    digitsEq 111 (rowProduct (r9Rows 56) r4Rows 111) (r10Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row57 :
    digitsEq 111 (rowProduct (r9Rows 57) r4Rows 111) (r10Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row58 :
    digitsEq 111 (rowProduct (r9Rows 58) r4Rows 111) (r10Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row59 :
    digitsEq 111 (rowProduct (r9Rows 59) r4Rows 111) (r10Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row60 :
    digitsEq 111 (rowProduct (r9Rows 60) r4Rows 111) (r10Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row61 :
    digitsEq 111 (rowProduct (r9Rows 61) r4Rows 111) (r10Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row62 :
    digitsEq 111 (rowProduct (r9Rows 62) r4Rows 111) (r10Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row63 :
    digitsEq 111 (rowProduct (r9Rows 63) r4Rows 111) (r10Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row64 :
    digitsEq 111 (rowProduct (r9Rows 64) r4Rows 111) (r10Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row65 :
    digitsEq 111 (rowProduct (r9Rows 65) r4Rows 111) (r10Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row66 :
    digitsEq 111 (rowProduct (r9Rows 66) r4Rows 111) (r10Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row67 :
    digitsEq 111 (rowProduct (r9Rows 67) r4Rows 111) (r10Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row68 :
    digitsEq 111 (rowProduct (r9Rows 68) r4Rows 111) (r10Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row69 :
    digitsEq 111 (rowProduct (r9Rows 69) r4Rows 111) (r10Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row70 :
    digitsEq 111 (rowProduct (r9Rows 70) r4Rows 111) (r10Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row71 :
    digitsEq 111 (rowProduct (r9Rows 71) r4Rows 111) (r10Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row72 :
    digitsEq 111 (rowProduct (r9Rows 72) r4Rows 111) (r10Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row73 :
    digitsEq 111 (rowProduct (r9Rows 73) r4Rows 111) (r10Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row74 :
    digitsEq 111 (rowProduct (r9Rows 74) r4Rows 111) (r10Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row75 :
    digitsEq 111 (rowProduct (r9Rows 75) r4Rows 111) (r10Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row76 :
    digitsEq 111 (rowProduct (r9Rows 76) r4Rows 111) (r10Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row77 :
    digitsEq 111 (rowProduct (r9Rows 77) r4Rows 111) (r10Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row78 :
    digitsEq 111 (rowProduct (r9Rows 78) r4Rows 111) (r10Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row79 :
    digitsEq 111 (rowProduct (r9Rows 79) r4Rows 111) (r10Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row80 :
    digitsEq 111 (rowProduct (r9Rows 80) r4Rows 111) (r10Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row81 :
    digitsEq 111 (rowProduct (r9Rows 81) r4Rows 111) (r10Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row82 :
    digitsEq 111 (rowProduct (r9Rows 82) r4Rows 111) (r10Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row83 :
    digitsEq 111 (rowProduct (r9Rows 83) r4Rows 111) (r10Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row84 :
    digitsEq 111 (rowProduct (r9Rows 84) r4Rows 111) (r10Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row85 :
    digitsEq 111 (rowProduct (r9Rows 85) r4Rows 111) (r10Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row86 :
    digitsEq 111 (rowProduct (r9Rows 86) r4Rows 111) (r10Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row87 :
    digitsEq 111 (rowProduct (r9Rows 87) r4Rows 111) (r10Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row88 :
    digitsEq 111 (rowProduct (r9Rows 88) r4Rows 111) (r10Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row89 :
    digitsEq 111 (rowProduct (r9Rows 89) r4Rows 111) (r10Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row90 :
    digitsEq 111 (rowProduct (r9Rows 90) r4Rows 111) (r10Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row91 :
    digitsEq 111 (rowProduct (r9Rows 91) r4Rows 111) (r10Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row92 :
    digitsEq 111 (rowProduct (r9Rows 92) r4Rows 111) (r10Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row93 :
    digitsEq 111 (rowProduct (r9Rows 93) r4Rows 111) (r10Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row94 :
    digitsEq 111 (rowProduct (r9Rows 94) r4Rows 111) (r10Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row95 :
    digitsEq 111 (rowProduct (r9Rows 95) r4Rows 111) (r10Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row96 :
    digitsEq 111 (rowProduct (r9Rows 96) r4Rows 111) (r10Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row97 :
    digitsEq 111 (rowProduct (r9Rows 97) r4Rows 111) (r10Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row98 :
    digitsEq 111 (rowProduct (r9Rows 98) r4Rows 111) (r10Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row99 :
    digitsEq 111 (rowProduct (r9Rows 99) r4Rows 111) (r10Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row100 :
    digitsEq 111 (rowProduct (r9Rows 100) r4Rows 111) (r10Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row101 :
    digitsEq 111 (rowProduct (r9Rows 101) r4Rows 111) (r10Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row102 :
    digitsEq 111 (rowProduct (r9Rows 102) r4Rows 111) (r10Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row103 :
    digitsEq 111 (rowProduct (r9Rows 103) r4Rows 111) (r10Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row104 :
    digitsEq 111 (rowProduct (r9Rows 104) r4Rows 111) (r10Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row105 :
    digitsEq 111 (rowProduct (r9Rows 105) r4Rows 111) (r10Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row106 :
    digitsEq 111 (rowProduct (r9Rows 106) r4Rows 111) (r10Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row107 :
    digitsEq 111 (rowProduct (r9Rows 107) r4Rows 111) (r10Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row108 :
    digitsEq 111 (rowProduct (r9Rows 108) r4Rows 111) (r10Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row109 :
    digitsEq 111 (rowProduct (r9Rows 109) r4Rows 111) (r10Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r10_row110 :
    digitsEq 111 (rowProduct (r9Rows 110) r4Rows 111) (r10Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem r10_rows : ∀ i,
    digitsEq 111 (rowProduct (r9Rows i) r4Rows 111) (r10Rows i) = true :=
  (Fin.cases r10_row0
    (Fin.cases r10_row1
    (Fin.cases r10_row2
    (Fin.cases r10_row3
    (Fin.cases r10_row4
    (Fin.cases r10_row5
    (Fin.cases r10_row6
    (Fin.cases r10_row7
    (Fin.cases r10_row8
    (Fin.cases r10_row9
    (Fin.cases r10_row10
    (Fin.cases r10_row11
    (Fin.cases r10_row12
    (Fin.cases r10_row13
    (Fin.cases r10_row14
    (Fin.cases r10_row15
    (Fin.cases r10_row16
    (Fin.cases r10_row17
    (Fin.cases r10_row18
    (Fin.cases r10_row19
    (Fin.cases r10_row20
    (Fin.cases r10_row21
    (Fin.cases r10_row22
    (Fin.cases r10_row23
    (Fin.cases r10_row24
    (Fin.cases r10_row25
    (Fin.cases r10_row26
    (Fin.cases r10_row27
    (Fin.cases r10_row28
    (Fin.cases r10_row29
    (Fin.cases r10_row30
    (Fin.cases r10_row31
    (Fin.cases r10_row32
    (Fin.cases r10_row33
    (Fin.cases r10_row34
    (Fin.cases r10_row35
    (Fin.cases r10_row36
    (Fin.cases r10_row37
    (Fin.cases r10_row38
    (Fin.cases r10_row39
    (Fin.cases r10_row40
    (Fin.cases r10_row41
    (Fin.cases r10_row42
    (Fin.cases r10_row43
    (Fin.cases r10_row44
    (Fin.cases r10_row45
    (Fin.cases r10_row46
    (Fin.cases r10_row47
    (Fin.cases r10_row48
    (Fin.cases r10_row49
    (Fin.cases r10_row50
    (Fin.cases r10_row51
    (Fin.cases r10_row52
    (Fin.cases r10_row53
    (Fin.cases r10_row54
    (Fin.cases r10_row55
    (Fin.cases r10_row56
    (Fin.cases r10_row57
    (Fin.cases r10_row58
    (Fin.cases r10_row59
    (Fin.cases r10_row60
    (Fin.cases r10_row61
    (Fin.cases r10_row62
    (Fin.cases r10_row63
    (Fin.cases r10_row64
    (Fin.cases r10_row65
    (Fin.cases r10_row66
    (Fin.cases r10_row67
    (Fin.cases r10_row68
    (Fin.cases r10_row69
    (Fin.cases r10_row70
    (Fin.cases r10_row71
    (Fin.cases r10_row72
    (Fin.cases r10_row73
    (Fin.cases r10_row74
    (Fin.cases r10_row75
    (Fin.cases r10_row76
    (Fin.cases r10_row77
    (Fin.cases r10_row78
    (Fin.cases r10_row79
    (Fin.cases r10_row80
    (Fin.cases r10_row81
    (Fin.cases r10_row82
    (Fin.cases r10_row83
    (Fin.cases r10_row84
    (Fin.cases r10_row85
    (Fin.cases r10_row86
    (Fin.cases r10_row87
    (Fin.cases r10_row88
    (Fin.cases r10_row89
    (Fin.cases r10_row90
    (Fin.cases r10_row91
    (Fin.cases r10_row92
    (Fin.cases r10_row93
    (Fin.cases r10_row94
    (Fin.cases r10_row95
    (Fin.cases r10_row96
    (Fin.cases r10_row97
    (Fin.cases r10_row98
    (Fin.cases r10_row99
    (Fin.cases r10_row100
    (Fin.cases r10_row101
    (Fin.cases r10_row102
    (Fin.cases r10_row103
    (Fin.cases r10_row104
    (Fin.cases r10_row105
    (Fin.cases r10_row106
    (Fin.cases r10_row107
    (Fin.cases r10_row108
    (Fin.cases r10_row109
    (Fin.cases r10_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_r10 : r9Matrix * r4Matrix = r10Matrix :=
  decode_mul _ _ _ r9_small r4_small r10_rows

end Lyons.Atlas111InvolutionWords
