module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: ab7 times r10

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
private theorem tr_row0 :
    digitsEq 111 (rowProduct (ab7Rows 0) r10Rows 111) (trRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row1 :
    digitsEq 111 (rowProduct (ab7Rows 1) r10Rows 111) (trRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row2 :
    digitsEq 111 (rowProduct (ab7Rows 2) r10Rows 111) (trRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row3 :
    digitsEq 111 (rowProduct (ab7Rows 3) r10Rows 111) (trRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row4 :
    digitsEq 111 (rowProduct (ab7Rows 4) r10Rows 111) (trRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row5 :
    digitsEq 111 (rowProduct (ab7Rows 5) r10Rows 111) (trRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row6 :
    digitsEq 111 (rowProduct (ab7Rows 6) r10Rows 111) (trRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row7 :
    digitsEq 111 (rowProduct (ab7Rows 7) r10Rows 111) (trRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row8 :
    digitsEq 111 (rowProduct (ab7Rows 8) r10Rows 111) (trRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row9 :
    digitsEq 111 (rowProduct (ab7Rows 9) r10Rows 111) (trRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row10 :
    digitsEq 111 (rowProduct (ab7Rows 10) r10Rows 111) (trRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row11 :
    digitsEq 111 (rowProduct (ab7Rows 11) r10Rows 111) (trRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row12 :
    digitsEq 111 (rowProduct (ab7Rows 12) r10Rows 111) (trRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row13 :
    digitsEq 111 (rowProduct (ab7Rows 13) r10Rows 111) (trRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row14 :
    digitsEq 111 (rowProduct (ab7Rows 14) r10Rows 111) (trRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row15 :
    digitsEq 111 (rowProduct (ab7Rows 15) r10Rows 111) (trRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row16 :
    digitsEq 111 (rowProduct (ab7Rows 16) r10Rows 111) (trRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row17 :
    digitsEq 111 (rowProduct (ab7Rows 17) r10Rows 111) (trRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row18 :
    digitsEq 111 (rowProduct (ab7Rows 18) r10Rows 111) (trRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row19 :
    digitsEq 111 (rowProduct (ab7Rows 19) r10Rows 111) (trRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row20 :
    digitsEq 111 (rowProduct (ab7Rows 20) r10Rows 111) (trRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row21 :
    digitsEq 111 (rowProduct (ab7Rows 21) r10Rows 111) (trRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row22 :
    digitsEq 111 (rowProduct (ab7Rows 22) r10Rows 111) (trRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row23 :
    digitsEq 111 (rowProduct (ab7Rows 23) r10Rows 111) (trRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row24 :
    digitsEq 111 (rowProduct (ab7Rows 24) r10Rows 111) (trRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row25 :
    digitsEq 111 (rowProduct (ab7Rows 25) r10Rows 111) (trRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row26 :
    digitsEq 111 (rowProduct (ab7Rows 26) r10Rows 111) (trRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row27 :
    digitsEq 111 (rowProduct (ab7Rows 27) r10Rows 111) (trRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row28 :
    digitsEq 111 (rowProduct (ab7Rows 28) r10Rows 111) (trRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row29 :
    digitsEq 111 (rowProduct (ab7Rows 29) r10Rows 111) (trRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row30 :
    digitsEq 111 (rowProduct (ab7Rows 30) r10Rows 111) (trRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row31 :
    digitsEq 111 (rowProduct (ab7Rows 31) r10Rows 111) (trRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row32 :
    digitsEq 111 (rowProduct (ab7Rows 32) r10Rows 111) (trRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row33 :
    digitsEq 111 (rowProduct (ab7Rows 33) r10Rows 111) (trRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row34 :
    digitsEq 111 (rowProduct (ab7Rows 34) r10Rows 111) (trRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row35 :
    digitsEq 111 (rowProduct (ab7Rows 35) r10Rows 111) (trRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row36 :
    digitsEq 111 (rowProduct (ab7Rows 36) r10Rows 111) (trRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row37 :
    digitsEq 111 (rowProduct (ab7Rows 37) r10Rows 111) (trRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row38 :
    digitsEq 111 (rowProduct (ab7Rows 38) r10Rows 111) (trRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row39 :
    digitsEq 111 (rowProduct (ab7Rows 39) r10Rows 111) (trRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row40 :
    digitsEq 111 (rowProduct (ab7Rows 40) r10Rows 111) (trRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row41 :
    digitsEq 111 (rowProduct (ab7Rows 41) r10Rows 111) (trRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row42 :
    digitsEq 111 (rowProduct (ab7Rows 42) r10Rows 111) (trRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row43 :
    digitsEq 111 (rowProduct (ab7Rows 43) r10Rows 111) (trRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row44 :
    digitsEq 111 (rowProduct (ab7Rows 44) r10Rows 111) (trRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row45 :
    digitsEq 111 (rowProduct (ab7Rows 45) r10Rows 111) (trRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row46 :
    digitsEq 111 (rowProduct (ab7Rows 46) r10Rows 111) (trRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row47 :
    digitsEq 111 (rowProduct (ab7Rows 47) r10Rows 111) (trRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row48 :
    digitsEq 111 (rowProduct (ab7Rows 48) r10Rows 111) (trRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row49 :
    digitsEq 111 (rowProduct (ab7Rows 49) r10Rows 111) (trRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row50 :
    digitsEq 111 (rowProduct (ab7Rows 50) r10Rows 111) (trRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row51 :
    digitsEq 111 (rowProduct (ab7Rows 51) r10Rows 111) (trRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row52 :
    digitsEq 111 (rowProduct (ab7Rows 52) r10Rows 111) (trRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row53 :
    digitsEq 111 (rowProduct (ab7Rows 53) r10Rows 111) (trRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row54 :
    digitsEq 111 (rowProduct (ab7Rows 54) r10Rows 111) (trRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row55 :
    digitsEq 111 (rowProduct (ab7Rows 55) r10Rows 111) (trRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row56 :
    digitsEq 111 (rowProduct (ab7Rows 56) r10Rows 111) (trRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row57 :
    digitsEq 111 (rowProduct (ab7Rows 57) r10Rows 111) (trRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row58 :
    digitsEq 111 (rowProduct (ab7Rows 58) r10Rows 111) (trRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row59 :
    digitsEq 111 (rowProduct (ab7Rows 59) r10Rows 111) (trRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row60 :
    digitsEq 111 (rowProduct (ab7Rows 60) r10Rows 111) (trRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row61 :
    digitsEq 111 (rowProduct (ab7Rows 61) r10Rows 111) (trRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row62 :
    digitsEq 111 (rowProduct (ab7Rows 62) r10Rows 111) (trRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row63 :
    digitsEq 111 (rowProduct (ab7Rows 63) r10Rows 111) (trRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row64 :
    digitsEq 111 (rowProduct (ab7Rows 64) r10Rows 111) (trRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row65 :
    digitsEq 111 (rowProduct (ab7Rows 65) r10Rows 111) (trRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row66 :
    digitsEq 111 (rowProduct (ab7Rows 66) r10Rows 111) (trRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row67 :
    digitsEq 111 (rowProduct (ab7Rows 67) r10Rows 111) (trRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row68 :
    digitsEq 111 (rowProduct (ab7Rows 68) r10Rows 111) (trRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row69 :
    digitsEq 111 (rowProduct (ab7Rows 69) r10Rows 111) (trRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row70 :
    digitsEq 111 (rowProduct (ab7Rows 70) r10Rows 111) (trRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row71 :
    digitsEq 111 (rowProduct (ab7Rows 71) r10Rows 111) (trRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row72 :
    digitsEq 111 (rowProduct (ab7Rows 72) r10Rows 111) (trRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row73 :
    digitsEq 111 (rowProduct (ab7Rows 73) r10Rows 111) (trRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row74 :
    digitsEq 111 (rowProduct (ab7Rows 74) r10Rows 111) (trRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row75 :
    digitsEq 111 (rowProduct (ab7Rows 75) r10Rows 111) (trRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row76 :
    digitsEq 111 (rowProduct (ab7Rows 76) r10Rows 111) (trRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row77 :
    digitsEq 111 (rowProduct (ab7Rows 77) r10Rows 111) (trRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row78 :
    digitsEq 111 (rowProduct (ab7Rows 78) r10Rows 111) (trRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row79 :
    digitsEq 111 (rowProduct (ab7Rows 79) r10Rows 111) (trRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row80 :
    digitsEq 111 (rowProduct (ab7Rows 80) r10Rows 111) (trRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row81 :
    digitsEq 111 (rowProduct (ab7Rows 81) r10Rows 111) (trRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row82 :
    digitsEq 111 (rowProduct (ab7Rows 82) r10Rows 111) (trRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row83 :
    digitsEq 111 (rowProduct (ab7Rows 83) r10Rows 111) (trRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row84 :
    digitsEq 111 (rowProduct (ab7Rows 84) r10Rows 111) (trRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row85 :
    digitsEq 111 (rowProduct (ab7Rows 85) r10Rows 111) (trRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row86 :
    digitsEq 111 (rowProduct (ab7Rows 86) r10Rows 111) (trRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row87 :
    digitsEq 111 (rowProduct (ab7Rows 87) r10Rows 111) (trRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row88 :
    digitsEq 111 (rowProduct (ab7Rows 88) r10Rows 111) (trRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row89 :
    digitsEq 111 (rowProduct (ab7Rows 89) r10Rows 111) (trRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row90 :
    digitsEq 111 (rowProduct (ab7Rows 90) r10Rows 111) (trRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row91 :
    digitsEq 111 (rowProduct (ab7Rows 91) r10Rows 111) (trRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row92 :
    digitsEq 111 (rowProduct (ab7Rows 92) r10Rows 111) (trRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row93 :
    digitsEq 111 (rowProduct (ab7Rows 93) r10Rows 111) (trRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row94 :
    digitsEq 111 (rowProduct (ab7Rows 94) r10Rows 111) (trRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row95 :
    digitsEq 111 (rowProduct (ab7Rows 95) r10Rows 111) (trRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row96 :
    digitsEq 111 (rowProduct (ab7Rows 96) r10Rows 111) (trRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row97 :
    digitsEq 111 (rowProduct (ab7Rows 97) r10Rows 111) (trRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row98 :
    digitsEq 111 (rowProduct (ab7Rows 98) r10Rows 111) (trRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row99 :
    digitsEq 111 (rowProduct (ab7Rows 99) r10Rows 111) (trRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row100 :
    digitsEq 111 (rowProduct (ab7Rows 100) r10Rows 111) (trRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row101 :
    digitsEq 111 (rowProduct (ab7Rows 101) r10Rows 111) (trRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row102 :
    digitsEq 111 (rowProduct (ab7Rows 102) r10Rows 111) (trRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row103 :
    digitsEq 111 (rowProduct (ab7Rows 103) r10Rows 111) (trRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row104 :
    digitsEq 111 (rowProduct (ab7Rows 104) r10Rows 111) (trRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row105 :
    digitsEq 111 (rowProduct (ab7Rows 105) r10Rows 111) (trRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row106 :
    digitsEq 111 (rowProduct (ab7Rows 106) r10Rows 111) (trRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row107 :
    digitsEq 111 (rowProduct (ab7Rows 107) r10Rows 111) (trRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row108 :
    digitsEq 111 (rowProduct (ab7Rows 108) r10Rows 111) (trRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row109 :
    digitsEq 111 (rowProduct (ab7Rows 109) r10Rows 111) (trRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tr_row110 :
    digitsEq 111 (rowProduct (ab7Rows 110) r10Rows 111) (trRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem tr_rows : ∀ i,
    digitsEq 111 (rowProduct (ab7Rows i) r10Rows 111) (trRows i) = true :=
  (Fin.cases tr_row0
    (Fin.cases tr_row1
    (Fin.cases tr_row2
    (Fin.cases tr_row3
    (Fin.cases tr_row4
    (Fin.cases tr_row5
    (Fin.cases tr_row6
    (Fin.cases tr_row7
    (Fin.cases tr_row8
    (Fin.cases tr_row9
    (Fin.cases tr_row10
    (Fin.cases tr_row11
    (Fin.cases tr_row12
    (Fin.cases tr_row13
    (Fin.cases tr_row14
    (Fin.cases tr_row15
    (Fin.cases tr_row16
    (Fin.cases tr_row17
    (Fin.cases tr_row18
    (Fin.cases tr_row19
    (Fin.cases tr_row20
    (Fin.cases tr_row21
    (Fin.cases tr_row22
    (Fin.cases tr_row23
    (Fin.cases tr_row24
    (Fin.cases tr_row25
    (Fin.cases tr_row26
    (Fin.cases tr_row27
    (Fin.cases tr_row28
    (Fin.cases tr_row29
    (Fin.cases tr_row30
    (Fin.cases tr_row31
    (Fin.cases tr_row32
    (Fin.cases tr_row33
    (Fin.cases tr_row34
    (Fin.cases tr_row35
    (Fin.cases tr_row36
    (Fin.cases tr_row37
    (Fin.cases tr_row38
    (Fin.cases tr_row39
    (Fin.cases tr_row40
    (Fin.cases tr_row41
    (Fin.cases tr_row42
    (Fin.cases tr_row43
    (Fin.cases tr_row44
    (Fin.cases tr_row45
    (Fin.cases tr_row46
    (Fin.cases tr_row47
    (Fin.cases tr_row48
    (Fin.cases tr_row49
    (Fin.cases tr_row50
    (Fin.cases tr_row51
    (Fin.cases tr_row52
    (Fin.cases tr_row53
    (Fin.cases tr_row54
    (Fin.cases tr_row55
    (Fin.cases tr_row56
    (Fin.cases tr_row57
    (Fin.cases tr_row58
    (Fin.cases tr_row59
    (Fin.cases tr_row60
    (Fin.cases tr_row61
    (Fin.cases tr_row62
    (Fin.cases tr_row63
    (Fin.cases tr_row64
    (Fin.cases tr_row65
    (Fin.cases tr_row66
    (Fin.cases tr_row67
    (Fin.cases tr_row68
    (Fin.cases tr_row69
    (Fin.cases tr_row70
    (Fin.cases tr_row71
    (Fin.cases tr_row72
    (Fin.cases tr_row73
    (Fin.cases tr_row74
    (Fin.cases tr_row75
    (Fin.cases tr_row76
    (Fin.cases tr_row77
    (Fin.cases tr_row78
    (Fin.cases tr_row79
    (Fin.cases tr_row80
    (Fin.cases tr_row81
    (Fin.cases tr_row82
    (Fin.cases tr_row83
    (Fin.cases tr_row84
    (Fin.cases tr_row85
    (Fin.cases tr_row86
    (Fin.cases tr_row87
    (Fin.cases tr_row88
    (Fin.cases tr_row89
    (Fin.cases tr_row90
    (Fin.cases tr_row91
    (Fin.cases tr_row92
    (Fin.cases tr_row93
    (Fin.cases tr_row94
    (Fin.cases tr_row95
    (Fin.cases tr_row96
    (Fin.cases tr_row97
    (Fin.cases tr_row98
    (Fin.cases tr_row99
    (Fin.cases tr_row100
    (Fin.cases tr_row101
    (Fin.cases tr_row102
    (Fin.cases tr_row103
    (Fin.cases tr_row104
    (Fin.cases tr_row105
    (Fin.cases tr_row106
    (Fin.cases tr_row107
    (Fin.cases tr_row108
    (Fin.cases tr_row109
    (Fin.cases tr_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_tr : ab7Matrix * r10Matrix = trMatrix :=
  decode_mul _ _ _ ab7_small r10_small tr_rows

end Lyons.Atlas111InvolutionWords
