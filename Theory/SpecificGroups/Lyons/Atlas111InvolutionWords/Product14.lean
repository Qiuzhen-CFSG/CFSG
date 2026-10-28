module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: r10 times c10

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
private theorem localB_row0 :
    digitsEq 111 (rowProduct (r10Rows 0) c10Rows 111) (localBRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row1 :
    digitsEq 111 (rowProduct (r10Rows 1) c10Rows 111) (localBRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row2 :
    digitsEq 111 (rowProduct (r10Rows 2) c10Rows 111) (localBRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row3 :
    digitsEq 111 (rowProduct (r10Rows 3) c10Rows 111) (localBRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row4 :
    digitsEq 111 (rowProduct (r10Rows 4) c10Rows 111) (localBRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row5 :
    digitsEq 111 (rowProduct (r10Rows 5) c10Rows 111) (localBRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row6 :
    digitsEq 111 (rowProduct (r10Rows 6) c10Rows 111) (localBRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row7 :
    digitsEq 111 (rowProduct (r10Rows 7) c10Rows 111) (localBRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row8 :
    digitsEq 111 (rowProduct (r10Rows 8) c10Rows 111) (localBRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row9 :
    digitsEq 111 (rowProduct (r10Rows 9) c10Rows 111) (localBRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row10 :
    digitsEq 111 (rowProduct (r10Rows 10) c10Rows 111) (localBRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row11 :
    digitsEq 111 (rowProduct (r10Rows 11) c10Rows 111) (localBRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row12 :
    digitsEq 111 (rowProduct (r10Rows 12) c10Rows 111) (localBRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row13 :
    digitsEq 111 (rowProduct (r10Rows 13) c10Rows 111) (localBRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row14 :
    digitsEq 111 (rowProduct (r10Rows 14) c10Rows 111) (localBRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row15 :
    digitsEq 111 (rowProduct (r10Rows 15) c10Rows 111) (localBRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row16 :
    digitsEq 111 (rowProduct (r10Rows 16) c10Rows 111) (localBRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row17 :
    digitsEq 111 (rowProduct (r10Rows 17) c10Rows 111) (localBRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row18 :
    digitsEq 111 (rowProduct (r10Rows 18) c10Rows 111) (localBRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row19 :
    digitsEq 111 (rowProduct (r10Rows 19) c10Rows 111) (localBRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row20 :
    digitsEq 111 (rowProduct (r10Rows 20) c10Rows 111) (localBRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row21 :
    digitsEq 111 (rowProduct (r10Rows 21) c10Rows 111) (localBRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row22 :
    digitsEq 111 (rowProduct (r10Rows 22) c10Rows 111) (localBRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row23 :
    digitsEq 111 (rowProduct (r10Rows 23) c10Rows 111) (localBRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row24 :
    digitsEq 111 (rowProduct (r10Rows 24) c10Rows 111) (localBRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row25 :
    digitsEq 111 (rowProduct (r10Rows 25) c10Rows 111) (localBRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row26 :
    digitsEq 111 (rowProduct (r10Rows 26) c10Rows 111) (localBRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row27 :
    digitsEq 111 (rowProduct (r10Rows 27) c10Rows 111) (localBRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row28 :
    digitsEq 111 (rowProduct (r10Rows 28) c10Rows 111) (localBRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row29 :
    digitsEq 111 (rowProduct (r10Rows 29) c10Rows 111) (localBRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row30 :
    digitsEq 111 (rowProduct (r10Rows 30) c10Rows 111) (localBRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row31 :
    digitsEq 111 (rowProduct (r10Rows 31) c10Rows 111) (localBRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row32 :
    digitsEq 111 (rowProduct (r10Rows 32) c10Rows 111) (localBRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row33 :
    digitsEq 111 (rowProduct (r10Rows 33) c10Rows 111) (localBRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row34 :
    digitsEq 111 (rowProduct (r10Rows 34) c10Rows 111) (localBRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row35 :
    digitsEq 111 (rowProduct (r10Rows 35) c10Rows 111) (localBRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row36 :
    digitsEq 111 (rowProduct (r10Rows 36) c10Rows 111) (localBRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row37 :
    digitsEq 111 (rowProduct (r10Rows 37) c10Rows 111) (localBRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row38 :
    digitsEq 111 (rowProduct (r10Rows 38) c10Rows 111) (localBRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row39 :
    digitsEq 111 (rowProduct (r10Rows 39) c10Rows 111) (localBRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row40 :
    digitsEq 111 (rowProduct (r10Rows 40) c10Rows 111) (localBRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row41 :
    digitsEq 111 (rowProduct (r10Rows 41) c10Rows 111) (localBRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row42 :
    digitsEq 111 (rowProduct (r10Rows 42) c10Rows 111) (localBRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row43 :
    digitsEq 111 (rowProduct (r10Rows 43) c10Rows 111) (localBRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row44 :
    digitsEq 111 (rowProduct (r10Rows 44) c10Rows 111) (localBRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row45 :
    digitsEq 111 (rowProduct (r10Rows 45) c10Rows 111) (localBRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row46 :
    digitsEq 111 (rowProduct (r10Rows 46) c10Rows 111) (localBRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row47 :
    digitsEq 111 (rowProduct (r10Rows 47) c10Rows 111) (localBRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row48 :
    digitsEq 111 (rowProduct (r10Rows 48) c10Rows 111) (localBRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row49 :
    digitsEq 111 (rowProduct (r10Rows 49) c10Rows 111) (localBRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row50 :
    digitsEq 111 (rowProduct (r10Rows 50) c10Rows 111) (localBRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row51 :
    digitsEq 111 (rowProduct (r10Rows 51) c10Rows 111) (localBRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row52 :
    digitsEq 111 (rowProduct (r10Rows 52) c10Rows 111) (localBRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row53 :
    digitsEq 111 (rowProduct (r10Rows 53) c10Rows 111) (localBRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row54 :
    digitsEq 111 (rowProduct (r10Rows 54) c10Rows 111) (localBRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row55 :
    digitsEq 111 (rowProduct (r10Rows 55) c10Rows 111) (localBRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row56 :
    digitsEq 111 (rowProduct (r10Rows 56) c10Rows 111) (localBRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row57 :
    digitsEq 111 (rowProduct (r10Rows 57) c10Rows 111) (localBRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row58 :
    digitsEq 111 (rowProduct (r10Rows 58) c10Rows 111) (localBRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row59 :
    digitsEq 111 (rowProduct (r10Rows 59) c10Rows 111) (localBRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row60 :
    digitsEq 111 (rowProduct (r10Rows 60) c10Rows 111) (localBRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row61 :
    digitsEq 111 (rowProduct (r10Rows 61) c10Rows 111) (localBRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row62 :
    digitsEq 111 (rowProduct (r10Rows 62) c10Rows 111) (localBRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row63 :
    digitsEq 111 (rowProduct (r10Rows 63) c10Rows 111) (localBRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row64 :
    digitsEq 111 (rowProduct (r10Rows 64) c10Rows 111) (localBRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row65 :
    digitsEq 111 (rowProduct (r10Rows 65) c10Rows 111) (localBRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row66 :
    digitsEq 111 (rowProduct (r10Rows 66) c10Rows 111) (localBRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row67 :
    digitsEq 111 (rowProduct (r10Rows 67) c10Rows 111) (localBRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row68 :
    digitsEq 111 (rowProduct (r10Rows 68) c10Rows 111) (localBRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row69 :
    digitsEq 111 (rowProduct (r10Rows 69) c10Rows 111) (localBRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row70 :
    digitsEq 111 (rowProduct (r10Rows 70) c10Rows 111) (localBRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row71 :
    digitsEq 111 (rowProduct (r10Rows 71) c10Rows 111) (localBRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row72 :
    digitsEq 111 (rowProduct (r10Rows 72) c10Rows 111) (localBRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row73 :
    digitsEq 111 (rowProduct (r10Rows 73) c10Rows 111) (localBRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row74 :
    digitsEq 111 (rowProduct (r10Rows 74) c10Rows 111) (localBRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row75 :
    digitsEq 111 (rowProduct (r10Rows 75) c10Rows 111) (localBRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row76 :
    digitsEq 111 (rowProduct (r10Rows 76) c10Rows 111) (localBRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row77 :
    digitsEq 111 (rowProduct (r10Rows 77) c10Rows 111) (localBRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row78 :
    digitsEq 111 (rowProduct (r10Rows 78) c10Rows 111) (localBRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row79 :
    digitsEq 111 (rowProduct (r10Rows 79) c10Rows 111) (localBRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row80 :
    digitsEq 111 (rowProduct (r10Rows 80) c10Rows 111) (localBRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row81 :
    digitsEq 111 (rowProduct (r10Rows 81) c10Rows 111) (localBRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row82 :
    digitsEq 111 (rowProduct (r10Rows 82) c10Rows 111) (localBRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row83 :
    digitsEq 111 (rowProduct (r10Rows 83) c10Rows 111) (localBRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row84 :
    digitsEq 111 (rowProduct (r10Rows 84) c10Rows 111) (localBRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row85 :
    digitsEq 111 (rowProduct (r10Rows 85) c10Rows 111) (localBRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row86 :
    digitsEq 111 (rowProduct (r10Rows 86) c10Rows 111) (localBRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row87 :
    digitsEq 111 (rowProduct (r10Rows 87) c10Rows 111) (localBRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row88 :
    digitsEq 111 (rowProduct (r10Rows 88) c10Rows 111) (localBRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row89 :
    digitsEq 111 (rowProduct (r10Rows 89) c10Rows 111) (localBRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row90 :
    digitsEq 111 (rowProduct (r10Rows 90) c10Rows 111) (localBRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row91 :
    digitsEq 111 (rowProduct (r10Rows 91) c10Rows 111) (localBRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row92 :
    digitsEq 111 (rowProduct (r10Rows 92) c10Rows 111) (localBRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row93 :
    digitsEq 111 (rowProduct (r10Rows 93) c10Rows 111) (localBRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row94 :
    digitsEq 111 (rowProduct (r10Rows 94) c10Rows 111) (localBRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row95 :
    digitsEq 111 (rowProduct (r10Rows 95) c10Rows 111) (localBRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row96 :
    digitsEq 111 (rowProduct (r10Rows 96) c10Rows 111) (localBRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row97 :
    digitsEq 111 (rowProduct (r10Rows 97) c10Rows 111) (localBRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row98 :
    digitsEq 111 (rowProduct (r10Rows 98) c10Rows 111) (localBRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row99 :
    digitsEq 111 (rowProduct (r10Rows 99) c10Rows 111) (localBRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row100 :
    digitsEq 111 (rowProduct (r10Rows 100) c10Rows 111) (localBRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row101 :
    digitsEq 111 (rowProduct (r10Rows 101) c10Rows 111) (localBRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row102 :
    digitsEq 111 (rowProduct (r10Rows 102) c10Rows 111) (localBRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row103 :
    digitsEq 111 (rowProduct (r10Rows 103) c10Rows 111) (localBRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row104 :
    digitsEq 111 (rowProduct (r10Rows 104) c10Rows 111) (localBRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row105 :
    digitsEq 111 (rowProduct (r10Rows 105) c10Rows 111) (localBRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row106 :
    digitsEq 111 (rowProduct (r10Rows 106) c10Rows 111) (localBRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row107 :
    digitsEq 111 (rowProduct (r10Rows 107) c10Rows 111) (localBRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row108 :
    digitsEq 111 (rowProduct (r10Rows 108) c10Rows 111) (localBRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row109 :
    digitsEq 111 (rowProduct (r10Rows 109) c10Rows 111) (localBRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem localB_row110 :
    digitsEq 111 (rowProduct (r10Rows 110) c10Rows 111) (localBRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem localB_rows : ∀ i,
    digitsEq 111 (rowProduct (r10Rows i) c10Rows 111) (localBRows i) = true :=
  (Fin.cases localB_row0
    (Fin.cases localB_row1
    (Fin.cases localB_row2
    (Fin.cases localB_row3
    (Fin.cases localB_row4
    (Fin.cases localB_row5
    (Fin.cases localB_row6
    (Fin.cases localB_row7
    (Fin.cases localB_row8
    (Fin.cases localB_row9
    (Fin.cases localB_row10
    (Fin.cases localB_row11
    (Fin.cases localB_row12
    (Fin.cases localB_row13
    (Fin.cases localB_row14
    (Fin.cases localB_row15
    (Fin.cases localB_row16
    (Fin.cases localB_row17
    (Fin.cases localB_row18
    (Fin.cases localB_row19
    (Fin.cases localB_row20
    (Fin.cases localB_row21
    (Fin.cases localB_row22
    (Fin.cases localB_row23
    (Fin.cases localB_row24
    (Fin.cases localB_row25
    (Fin.cases localB_row26
    (Fin.cases localB_row27
    (Fin.cases localB_row28
    (Fin.cases localB_row29
    (Fin.cases localB_row30
    (Fin.cases localB_row31
    (Fin.cases localB_row32
    (Fin.cases localB_row33
    (Fin.cases localB_row34
    (Fin.cases localB_row35
    (Fin.cases localB_row36
    (Fin.cases localB_row37
    (Fin.cases localB_row38
    (Fin.cases localB_row39
    (Fin.cases localB_row40
    (Fin.cases localB_row41
    (Fin.cases localB_row42
    (Fin.cases localB_row43
    (Fin.cases localB_row44
    (Fin.cases localB_row45
    (Fin.cases localB_row46
    (Fin.cases localB_row47
    (Fin.cases localB_row48
    (Fin.cases localB_row49
    (Fin.cases localB_row50
    (Fin.cases localB_row51
    (Fin.cases localB_row52
    (Fin.cases localB_row53
    (Fin.cases localB_row54
    (Fin.cases localB_row55
    (Fin.cases localB_row56
    (Fin.cases localB_row57
    (Fin.cases localB_row58
    (Fin.cases localB_row59
    (Fin.cases localB_row60
    (Fin.cases localB_row61
    (Fin.cases localB_row62
    (Fin.cases localB_row63
    (Fin.cases localB_row64
    (Fin.cases localB_row65
    (Fin.cases localB_row66
    (Fin.cases localB_row67
    (Fin.cases localB_row68
    (Fin.cases localB_row69
    (Fin.cases localB_row70
    (Fin.cases localB_row71
    (Fin.cases localB_row72
    (Fin.cases localB_row73
    (Fin.cases localB_row74
    (Fin.cases localB_row75
    (Fin.cases localB_row76
    (Fin.cases localB_row77
    (Fin.cases localB_row78
    (Fin.cases localB_row79
    (Fin.cases localB_row80
    (Fin.cases localB_row81
    (Fin.cases localB_row82
    (Fin.cases localB_row83
    (Fin.cases localB_row84
    (Fin.cases localB_row85
    (Fin.cases localB_row86
    (Fin.cases localB_row87
    (Fin.cases localB_row88
    (Fin.cases localB_row89
    (Fin.cases localB_row90
    (Fin.cases localB_row91
    (Fin.cases localB_row92
    (Fin.cases localB_row93
    (Fin.cases localB_row94
    (Fin.cases localB_row95
    (Fin.cases localB_row96
    (Fin.cases localB_row97
    (Fin.cases localB_row98
    (Fin.cases localB_row99
    (Fin.cases localB_row100
    (Fin.cases localB_row101
    (Fin.cases localB_row102
    (Fin.cases localB_row103
    (Fin.cases localB_row104
    (Fin.cases localB_row105
    (Fin.cases localB_row106
    (Fin.cases localB_row107
    (Fin.cases localB_row108
    (Fin.cases localB_row109
    (Fin.cases localB_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_localB : r10Matrix * c10Matrix = localBMatrix :=
  decode_mul _ _ _ r10_small c10_small localB_rows

end Lyons.Atlas111InvolutionWords
