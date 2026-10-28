module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: ab7 times transporter

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
private theorem tw_row0 :
    digitsEq 111 (rowProduct (ab7Rows 0) transporterRows 111) (twRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row1 :
    digitsEq 111 (rowProduct (ab7Rows 1) transporterRows 111) (twRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row2 :
    digitsEq 111 (rowProduct (ab7Rows 2) transporterRows 111) (twRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row3 :
    digitsEq 111 (rowProduct (ab7Rows 3) transporterRows 111) (twRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row4 :
    digitsEq 111 (rowProduct (ab7Rows 4) transporterRows 111) (twRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row5 :
    digitsEq 111 (rowProduct (ab7Rows 5) transporterRows 111) (twRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row6 :
    digitsEq 111 (rowProduct (ab7Rows 6) transporterRows 111) (twRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row7 :
    digitsEq 111 (rowProduct (ab7Rows 7) transporterRows 111) (twRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row8 :
    digitsEq 111 (rowProduct (ab7Rows 8) transporterRows 111) (twRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row9 :
    digitsEq 111 (rowProduct (ab7Rows 9) transporterRows 111) (twRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row10 :
    digitsEq 111 (rowProduct (ab7Rows 10) transporterRows 111) (twRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row11 :
    digitsEq 111 (rowProduct (ab7Rows 11) transporterRows 111) (twRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row12 :
    digitsEq 111 (rowProduct (ab7Rows 12) transporterRows 111) (twRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row13 :
    digitsEq 111 (rowProduct (ab7Rows 13) transporterRows 111) (twRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row14 :
    digitsEq 111 (rowProduct (ab7Rows 14) transporterRows 111) (twRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row15 :
    digitsEq 111 (rowProduct (ab7Rows 15) transporterRows 111) (twRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row16 :
    digitsEq 111 (rowProduct (ab7Rows 16) transporterRows 111) (twRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row17 :
    digitsEq 111 (rowProduct (ab7Rows 17) transporterRows 111) (twRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row18 :
    digitsEq 111 (rowProduct (ab7Rows 18) transporterRows 111) (twRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row19 :
    digitsEq 111 (rowProduct (ab7Rows 19) transporterRows 111) (twRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row20 :
    digitsEq 111 (rowProduct (ab7Rows 20) transporterRows 111) (twRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row21 :
    digitsEq 111 (rowProduct (ab7Rows 21) transporterRows 111) (twRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row22 :
    digitsEq 111 (rowProduct (ab7Rows 22) transporterRows 111) (twRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row23 :
    digitsEq 111 (rowProduct (ab7Rows 23) transporterRows 111) (twRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row24 :
    digitsEq 111 (rowProduct (ab7Rows 24) transporterRows 111) (twRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row25 :
    digitsEq 111 (rowProduct (ab7Rows 25) transporterRows 111) (twRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row26 :
    digitsEq 111 (rowProduct (ab7Rows 26) transporterRows 111) (twRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row27 :
    digitsEq 111 (rowProduct (ab7Rows 27) transporterRows 111) (twRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row28 :
    digitsEq 111 (rowProduct (ab7Rows 28) transporterRows 111) (twRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row29 :
    digitsEq 111 (rowProduct (ab7Rows 29) transporterRows 111) (twRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row30 :
    digitsEq 111 (rowProduct (ab7Rows 30) transporterRows 111) (twRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row31 :
    digitsEq 111 (rowProduct (ab7Rows 31) transporterRows 111) (twRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row32 :
    digitsEq 111 (rowProduct (ab7Rows 32) transporterRows 111) (twRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row33 :
    digitsEq 111 (rowProduct (ab7Rows 33) transporterRows 111) (twRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row34 :
    digitsEq 111 (rowProduct (ab7Rows 34) transporterRows 111) (twRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row35 :
    digitsEq 111 (rowProduct (ab7Rows 35) transporterRows 111) (twRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row36 :
    digitsEq 111 (rowProduct (ab7Rows 36) transporterRows 111) (twRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row37 :
    digitsEq 111 (rowProduct (ab7Rows 37) transporterRows 111) (twRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row38 :
    digitsEq 111 (rowProduct (ab7Rows 38) transporterRows 111) (twRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row39 :
    digitsEq 111 (rowProduct (ab7Rows 39) transporterRows 111) (twRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row40 :
    digitsEq 111 (rowProduct (ab7Rows 40) transporterRows 111) (twRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row41 :
    digitsEq 111 (rowProduct (ab7Rows 41) transporterRows 111) (twRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row42 :
    digitsEq 111 (rowProduct (ab7Rows 42) transporterRows 111) (twRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row43 :
    digitsEq 111 (rowProduct (ab7Rows 43) transporterRows 111) (twRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row44 :
    digitsEq 111 (rowProduct (ab7Rows 44) transporterRows 111) (twRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row45 :
    digitsEq 111 (rowProduct (ab7Rows 45) transporterRows 111) (twRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row46 :
    digitsEq 111 (rowProduct (ab7Rows 46) transporterRows 111) (twRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row47 :
    digitsEq 111 (rowProduct (ab7Rows 47) transporterRows 111) (twRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row48 :
    digitsEq 111 (rowProduct (ab7Rows 48) transporterRows 111) (twRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row49 :
    digitsEq 111 (rowProduct (ab7Rows 49) transporterRows 111) (twRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row50 :
    digitsEq 111 (rowProduct (ab7Rows 50) transporterRows 111) (twRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row51 :
    digitsEq 111 (rowProduct (ab7Rows 51) transporterRows 111) (twRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row52 :
    digitsEq 111 (rowProduct (ab7Rows 52) transporterRows 111) (twRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row53 :
    digitsEq 111 (rowProduct (ab7Rows 53) transporterRows 111) (twRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row54 :
    digitsEq 111 (rowProduct (ab7Rows 54) transporterRows 111) (twRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row55 :
    digitsEq 111 (rowProduct (ab7Rows 55) transporterRows 111) (twRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row56 :
    digitsEq 111 (rowProduct (ab7Rows 56) transporterRows 111) (twRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row57 :
    digitsEq 111 (rowProduct (ab7Rows 57) transporterRows 111) (twRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row58 :
    digitsEq 111 (rowProduct (ab7Rows 58) transporterRows 111) (twRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row59 :
    digitsEq 111 (rowProduct (ab7Rows 59) transporterRows 111) (twRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row60 :
    digitsEq 111 (rowProduct (ab7Rows 60) transporterRows 111) (twRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row61 :
    digitsEq 111 (rowProduct (ab7Rows 61) transporterRows 111) (twRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row62 :
    digitsEq 111 (rowProduct (ab7Rows 62) transporterRows 111) (twRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row63 :
    digitsEq 111 (rowProduct (ab7Rows 63) transporterRows 111) (twRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row64 :
    digitsEq 111 (rowProduct (ab7Rows 64) transporterRows 111) (twRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row65 :
    digitsEq 111 (rowProduct (ab7Rows 65) transporterRows 111) (twRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row66 :
    digitsEq 111 (rowProduct (ab7Rows 66) transporterRows 111) (twRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row67 :
    digitsEq 111 (rowProduct (ab7Rows 67) transporterRows 111) (twRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row68 :
    digitsEq 111 (rowProduct (ab7Rows 68) transporterRows 111) (twRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row69 :
    digitsEq 111 (rowProduct (ab7Rows 69) transporterRows 111) (twRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row70 :
    digitsEq 111 (rowProduct (ab7Rows 70) transporterRows 111) (twRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row71 :
    digitsEq 111 (rowProduct (ab7Rows 71) transporterRows 111) (twRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row72 :
    digitsEq 111 (rowProduct (ab7Rows 72) transporterRows 111) (twRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row73 :
    digitsEq 111 (rowProduct (ab7Rows 73) transporterRows 111) (twRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row74 :
    digitsEq 111 (rowProduct (ab7Rows 74) transporterRows 111) (twRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row75 :
    digitsEq 111 (rowProduct (ab7Rows 75) transporterRows 111) (twRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row76 :
    digitsEq 111 (rowProduct (ab7Rows 76) transporterRows 111) (twRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row77 :
    digitsEq 111 (rowProduct (ab7Rows 77) transporterRows 111) (twRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row78 :
    digitsEq 111 (rowProduct (ab7Rows 78) transporterRows 111) (twRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row79 :
    digitsEq 111 (rowProduct (ab7Rows 79) transporterRows 111) (twRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row80 :
    digitsEq 111 (rowProduct (ab7Rows 80) transporterRows 111) (twRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row81 :
    digitsEq 111 (rowProduct (ab7Rows 81) transporterRows 111) (twRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row82 :
    digitsEq 111 (rowProduct (ab7Rows 82) transporterRows 111) (twRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row83 :
    digitsEq 111 (rowProduct (ab7Rows 83) transporterRows 111) (twRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row84 :
    digitsEq 111 (rowProduct (ab7Rows 84) transporterRows 111) (twRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row85 :
    digitsEq 111 (rowProduct (ab7Rows 85) transporterRows 111) (twRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row86 :
    digitsEq 111 (rowProduct (ab7Rows 86) transporterRows 111) (twRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row87 :
    digitsEq 111 (rowProduct (ab7Rows 87) transporterRows 111) (twRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row88 :
    digitsEq 111 (rowProduct (ab7Rows 88) transporterRows 111) (twRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row89 :
    digitsEq 111 (rowProduct (ab7Rows 89) transporterRows 111) (twRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row90 :
    digitsEq 111 (rowProduct (ab7Rows 90) transporterRows 111) (twRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row91 :
    digitsEq 111 (rowProduct (ab7Rows 91) transporterRows 111) (twRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row92 :
    digitsEq 111 (rowProduct (ab7Rows 92) transporterRows 111) (twRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row93 :
    digitsEq 111 (rowProduct (ab7Rows 93) transporterRows 111) (twRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row94 :
    digitsEq 111 (rowProduct (ab7Rows 94) transporterRows 111) (twRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row95 :
    digitsEq 111 (rowProduct (ab7Rows 95) transporterRows 111) (twRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row96 :
    digitsEq 111 (rowProduct (ab7Rows 96) transporterRows 111) (twRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row97 :
    digitsEq 111 (rowProduct (ab7Rows 97) transporterRows 111) (twRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row98 :
    digitsEq 111 (rowProduct (ab7Rows 98) transporterRows 111) (twRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row99 :
    digitsEq 111 (rowProduct (ab7Rows 99) transporterRows 111) (twRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row100 :
    digitsEq 111 (rowProduct (ab7Rows 100) transporterRows 111) (twRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row101 :
    digitsEq 111 (rowProduct (ab7Rows 101) transporterRows 111) (twRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row102 :
    digitsEq 111 (rowProduct (ab7Rows 102) transporterRows 111) (twRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row103 :
    digitsEq 111 (rowProduct (ab7Rows 103) transporterRows 111) (twRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row104 :
    digitsEq 111 (rowProduct (ab7Rows 104) transporterRows 111) (twRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row105 :
    digitsEq 111 (rowProduct (ab7Rows 105) transporterRows 111) (twRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row106 :
    digitsEq 111 (rowProduct (ab7Rows 106) transporterRows 111) (twRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row107 :
    digitsEq 111 (rowProduct (ab7Rows 107) transporterRows 111) (twRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row108 :
    digitsEq 111 (rowProduct (ab7Rows 108) transporterRows 111) (twRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row109 :
    digitsEq 111 (rowProduct (ab7Rows 109) transporterRows 111) (twRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tw_row110 :
    digitsEq 111 (rowProduct (ab7Rows 110) transporterRows 111) (twRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem tw_rows : ∀ i,
    digitsEq 111 (rowProduct (ab7Rows i) transporterRows 111) (twRows i) = true :=
  (Fin.cases tw_row0
    (Fin.cases tw_row1
    (Fin.cases tw_row2
    (Fin.cases tw_row3
    (Fin.cases tw_row4
    (Fin.cases tw_row5
    (Fin.cases tw_row6
    (Fin.cases tw_row7
    (Fin.cases tw_row8
    (Fin.cases tw_row9
    (Fin.cases tw_row10
    (Fin.cases tw_row11
    (Fin.cases tw_row12
    (Fin.cases tw_row13
    (Fin.cases tw_row14
    (Fin.cases tw_row15
    (Fin.cases tw_row16
    (Fin.cases tw_row17
    (Fin.cases tw_row18
    (Fin.cases tw_row19
    (Fin.cases tw_row20
    (Fin.cases tw_row21
    (Fin.cases tw_row22
    (Fin.cases tw_row23
    (Fin.cases tw_row24
    (Fin.cases tw_row25
    (Fin.cases tw_row26
    (Fin.cases tw_row27
    (Fin.cases tw_row28
    (Fin.cases tw_row29
    (Fin.cases tw_row30
    (Fin.cases tw_row31
    (Fin.cases tw_row32
    (Fin.cases tw_row33
    (Fin.cases tw_row34
    (Fin.cases tw_row35
    (Fin.cases tw_row36
    (Fin.cases tw_row37
    (Fin.cases tw_row38
    (Fin.cases tw_row39
    (Fin.cases tw_row40
    (Fin.cases tw_row41
    (Fin.cases tw_row42
    (Fin.cases tw_row43
    (Fin.cases tw_row44
    (Fin.cases tw_row45
    (Fin.cases tw_row46
    (Fin.cases tw_row47
    (Fin.cases tw_row48
    (Fin.cases tw_row49
    (Fin.cases tw_row50
    (Fin.cases tw_row51
    (Fin.cases tw_row52
    (Fin.cases tw_row53
    (Fin.cases tw_row54
    (Fin.cases tw_row55
    (Fin.cases tw_row56
    (Fin.cases tw_row57
    (Fin.cases tw_row58
    (Fin.cases tw_row59
    (Fin.cases tw_row60
    (Fin.cases tw_row61
    (Fin.cases tw_row62
    (Fin.cases tw_row63
    (Fin.cases tw_row64
    (Fin.cases tw_row65
    (Fin.cases tw_row66
    (Fin.cases tw_row67
    (Fin.cases tw_row68
    (Fin.cases tw_row69
    (Fin.cases tw_row70
    (Fin.cases tw_row71
    (Fin.cases tw_row72
    (Fin.cases tw_row73
    (Fin.cases tw_row74
    (Fin.cases tw_row75
    (Fin.cases tw_row76
    (Fin.cases tw_row77
    (Fin.cases tw_row78
    (Fin.cases tw_row79
    (Fin.cases tw_row80
    (Fin.cases tw_row81
    (Fin.cases tw_row82
    (Fin.cases tw_row83
    (Fin.cases tw_row84
    (Fin.cases tw_row85
    (Fin.cases tw_row86
    (Fin.cases tw_row87
    (Fin.cases tw_row88
    (Fin.cases tw_row89
    (Fin.cases tw_row90
    (Fin.cases tw_row91
    (Fin.cases tw_row92
    (Fin.cases tw_row93
    (Fin.cases tw_row94
    (Fin.cases tw_row95
    (Fin.cases tw_row96
    (Fin.cases tw_row97
    (Fin.cases tw_row98
    (Fin.cases tw_row99
    (Fin.cases tw_row100
    (Fin.cases tw_row101
    (Fin.cases tw_row102
    (Fin.cases tw_row103
    (Fin.cases tw_row104
    (Fin.cases tw_row105
    (Fin.cases tw_row106
    (Fin.cases tw_row107
    (Fin.cases tw_row108
    (Fin.cases tw_row109
    (Fin.cases tw_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_tw : ab7Matrix * transporterMatrix = twMatrix :=
  decode_mul _ _ _ ab7_small transporter_small tw_rows

end Lyons.Atlas111InvolutionWords
