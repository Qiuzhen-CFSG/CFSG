module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Data

/-!
# Involution word multiplication: localB times ab7

The carry-free arithmetic soundness theorem converts the 111
closed row checks into the displayed matrix identity.

Source and reproducible candidate generation:
`Atlas111InvolutionLocalCommutant/Words/source/GenerateWords.py` and the attributed
original matrices in `Atlas111Source/`. All checks run in Lean's kernel.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Words

open Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row0 :
    digitsEq 111 (rowProduct (localBRows 0) ab7Rows 111) (btRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row1 :
    digitsEq 111 (rowProduct (localBRows 1) ab7Rows 111) (btRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row2 :
    digitsEq 111 (rowProduct (localBRows 2) ab7Rows 111) (btRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row3 :
    digitsEq 111 (rowProduct (localBRows 3) ab7Rows 111) (btRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row4 :
    digitsEq 111 (rowProduct (localBRows 4) ab7Rows 111) (btRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row5 :
    digitsEq 111 (rowProduct (localBRows 5) ab7Rows 111) (btRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row6 :
    digitsEq 111 (rowProduct (localBRows 6) ab7Rows 111) (btRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row7 :
    digitsEq 111 (rowProduct (localBRows 7) ab7Rows 111) (btRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row8 :
    digitsEq 111 (rowProduct (localBRows 8) ab7Rows 111) (btRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row9 :
    digitsEq 111 (rowProduct (localBRows 9) ab7Rows 111) (btRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row10 :
    digitsEq 111 (rowProduct (localBRows 10) ab7Rows 111) (btRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row11 :
    digitsEq 111 (rowProduct (localBRows 11) ab7Rows 111) (btRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row12 :
    digitsEq 111 (rowProduct (localBRows 12) ab7Rows 111) (btRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row13 :
    digitsEq 111 (rowProduct (localBRows 13) ab7Rows 111) (btRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row14 :
    digitsEq 111 (rowProduct (localBRows 14) ab7Rows 111) (btRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row15 :
    digitsEq 111 (rowProduct (localBRows 15) ab7Rows 111) (btRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row16 :
    digitsEq 111 (rowProduct (localBRows 16) ab7Rows 111) (btRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row17 :
    digitsEq 111 (rowProduct (localBRows 17) ab7Rows 111) (btRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row18 :
    digitsEq 111 (rowProduct (localBRows 18) ab7Rows 111) (btRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row19 :
    digitsEq 111 (rowProduct (localBRows 19) ab7Rows 111) (btRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row20 :
    digitsEq 111 (rowProduct (localBRows 20) ab7Rows 111) (btRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row21 :
    digitsEq 111 (rowProduct (localBRows 21) ab7Rows 111) (btRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row22 :
    digitsEq 111 (rowProduct (localBRows 22) ab7Rows 111) (btRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row23 :
    digitsEq 111 (rowProduct (localBRows 23) ab7Rows 111) (btRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row24 :
    digitsEq 111 (rowProduct (localBRows 24) ab7Rows 111) (btRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row25 :
    digitsEq 111 (rowProduct (localBRows 25) ab7Rows 111) (btRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row26 :
    digitsEq 111 (rowProduct (localBRows 26) ab7Rows 111) (btRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row27 :
    digitsEq 111 (rowProduct (localBRows 27) ab7Rows 111) (btRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row28 :
    digitsEq 111 (rowProduct (localBRows 28) ab7Rows 111) (btRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row29 :
    digitsEq 111 (rowProduct (localBRows 29) ab7Rows 111) (btRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row30 :
    digitsEq 111 (rowProduct (localBRows 30) ab7Rows 111) (btRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row31 :
    digitsEq 111 (rowProduct (localBRows 31) ab7Rows 111) (btRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row32 :
    digitsEq 111 (rowProduct (localBRows 32) ab7Rows 111) (btRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row33 :
    digitsEq 111 (rowProduct (localBRows 33) ab7Rows 111) (btRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row34 :
    digitsEq 111 (rowProduct (localBRows 34) ab7Rows 111) (btRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row35 :
    digitsEq 111 (rowProduct (localBRows 35) ab7Rows 111) (btRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row36 :
    digitsEq 111 (rowProduct (localBRows 36) ab7Rows 111) (btRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row37 :
    digitsEq 111 (rowProduct (localBRows 37) ab7Rows 111) (btRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row38 :
    digitsEq 111 (rowProduct (localBRows 38) ab7Rows 111) (btRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row39 :
    digitsEq 111 (rowProduct (localBRows 39) ab7Rows 111) (btRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row40 :
    digitsEq 111 (rowProduct (localBRows 40) ab7Rows 111) (btRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row41 :
    digitsEq 111 (rowProduct (localBRows 41) ab7Rows 111) (btRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row42 :
    digitsEq 111 (rowProduct (localBRows 42) ab7Rows 111) (btRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row43 :
    digitsEq 111 (rowProduct (localBRows 43) ab7Rows 111) (btRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row44 :
    digitsEq 111 (rowProduct (localBRows 44) ab7Rows 111) (btRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row45 :
    digitsEq 111 (rowProduct (localBRows 45) ab7Rows 111) (btRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row46 :
    digitsEq 111 (rowProduct (localBRows 46) ab7Rows 111) (btRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row47 :
    digitsEq 111 (rowProduct (localBRows 47) ab7Rows 111) (btRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row48 :
    digitsEq 111 (rowProduct (localBRows 48) ab7Rows 111) (btRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row49 :
    digitsEq 111 (rowProduct (localBRows 49) ab7Rows 111) (btRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row50 :
    digitsEq 111 (rowProduct (localBRows 50) ab7Rows 111) (btRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row51 :
    digitsEq 111 (rowProduct (localBRows 51) ab7Rows 111) (btRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row52 :
    digitsEq 111 (rowProduct (localBRows 52) ab7Rows 111) (btRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row53 :
    digitsEq 111 (rowProduct (localBRows 53) ab7Rows 111) (btRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row54 :
    digitsEq 111 (rowProduct (localBRows 54) ab7Rows 111) (btRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row55 :
    digitsEq 111 (rowProduct (localBRows 55) ab7Rows 111) (btRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row56 :
    digitsEq 111 (rowProduct (localBRows 56) ab7Rows 111) (btRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row57 :
    digitsEq 111 (rowProduct (localBRows 57) ab7Rows 111) (btRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row58 :
    digitsEq 111 (rowProduct (localBRows 58) ab7Rows 111) (btRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row59 :
    digitsEq 111 (rowProduct (localBRows 59) ab7Rows 111) (btRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row60 :
    digitsEq 111 (rowProduct (localBRows 60) ab7Rows 111) (btRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row61 :
    digitsEq 111 (rowProduct (localBRows 61) ab7Rows 111) (btRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row62 :
    digitsEq 111 (rowProduct (localBRows 62) ab7Rows 111) (btRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row63 :
    digitsEq 111 (rowProduct (localBRows 63) ab7Rows 111) (btRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row64 :
    digitsEq 111 (rowProduct (localBRows 64) ab7Rows 111) (btRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row65 :
    digitsEq 111 (rowProduct (localBRows 65) ab7Rows 111) (btRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row66 :
    digitsEq 111 (rowProduct (localBRows 66) ab7Rows 111) (btRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row67 :
    digitsEq 111 (rowProduct (localBRows 67) ab7Rows 111) (btRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row68 :
    digitsEq 111 (rowProduct (localBRows 68) ab7Rows 111) (btRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row69 :
    digitsEq 111 (rowProduct (localBRows 69) ab7Rows 111) (btRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row70 :
    digitsEq 111 (rowProduct (localBRows 70) ab7Rows 111) (btRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row71 :
    digitsEq 111 (rowProduct (localBRows 71) ab7Rows 111) (btRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row72 :
    digitsEq 111 (rowProduct (localBRows 72) ab7Rows 111) (btRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row73 :
    digitsEq 111 (rowProduct (localBRows 73) ab7Rows 111) (btRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row74 :
    digitsEq 111 (rowProduct (localBRows 74) ab7Rows 111) (btRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row75 :
    digitsEq 111 (rowProduct (localBRows 75) ab7Rows 111) (btRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row76 :
    digitsEq 111 (rowProduct (localBRows 76) ab7Rows 111) (btRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row77 :
    digitsEq 111 (rowProduct (localBRows 77) ab7Rows 111) (btRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row78 :
    digitsEq 111 (rowProduct (localBRows 78) ab7Rows 111) (btRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row79 :
    digitsEq 111 (rowProduct (localBRows 79) ab7Rows 111) (btRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row80 :
    digitsEq 111 (rowProduct (localBRows 80) ab7Rows 111) (btRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row81 :
    digitsEq 111 (rowProduct (localBRows 81) ab7Rows 111) (btRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row82 :
    digitsEq 111 (rowProduct (localBRows 82) ab7Rows 111) (btRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row83 :
    digitsEq 111 (rowProduct (localBRows 83) ab7Rows 111) (btRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row84 :
    digitsEq 111 (rowProduct (localBRows 84) ab7Rows 111) (btRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row85 :
    digitsEq 111 (rowProduct (localBRows 85) ab7Rows 111) (btRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row86 :
    digitsEq 111 (rowProduct (localBRows 86) ab7Rows 111) (btRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row87 :
    digitsEq 111 (rowProduct (localBRows 87) ab7Rows 111) (btRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row88 :
    digitsEq 111 (rowProduct (localBRows 88) ab7Rows 111) (btRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row89 :
    digitsEq 111 (rowProduct (localBRows 89) ab7Rows 111) (btRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row90 :
    digitsEq 111 (rowProduct (localBRows 90) ab7Rows 111) (btRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row91 :
    digitsEq 111 (rowProduct (localBRows 91) ab7Rows 111) (btRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row92 :
    digitsEq 111 (rowProduct (localBRows 92) ab7Rows 111) (btRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row93 :
    digitsEq 111 (rowProduct (localBRows 93) ab7Rows 111) (btRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row94 :
    digitsEq 111 (rowProduct (localBRows 94) ab7Rows 111) (btRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row95 :
    digitsEq 111 (rowProduct (localBRows 95) ab7Rows 111) (btRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row96 :
    digitsEq 111 (rowProduct (localBRows 96) ab7Rows 111) (btRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row97 :
    digitsEq 111 (rowProduct (localBRows 97) ab7Rows 111) (btRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row98 :
    digitsEq 111 (rowProduct (localBRows 98) ab7Rows 111) (btRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row99 :
    digitsEq 111 (rowProduct (localBRows 99) ab7Rows 111) (btRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row100 :
    digitsEq 111 (rowProduct (localBRows 100) ab7Rows 111) (btRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row101 :
    digitsEq 111 (rowProduct (localBRows 101) ab7Rows 111) (btRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row102 :
    digitsEq 111 (rowProduct (localBRows 102) ab7Rows 111) (btRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row103 :
    digitsEq 111 (rowProduct (localBRows 103) ab7Rows 111) (btRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row104 :
    digitsEq 111 (rowProduct (localBRows 104) ab7Rows 111) (btRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row105 :
    digitsEq 111 (rowProduct (localBRows 105) ab7Rows 111) (btRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row106 :
    digitsEq 111 (rowProduct (localBRows 106) ab7Rows 111) (btRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row107 :
    digitsEq 111 (rowProduct (localBRows 107) ab7Rows 111) (btRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row108 :
    digitsEq 111 (rowProduct (localBRows 108) ab7Rows 111) (btRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row109 :
    digitsEq 111 (rowProduct (localBRows 109) ab7Rows 111) (btRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem bt_row110 :
    digitsEq 111 (rowProduct (localBRows 110) ab7Rows 111) (btRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bt_rows : ∀ i,
    digitsEq 111 (rowProduct (localBRows i) ab7Rows 111) (btRows i) = true :=
  (Fin.cases bt_row0
    (Fin.cases bt_row1
    (Fin.cases bt_row2
    (Fin.cases bt_row3
    (Fin.cases bt_row4
    (Fin.cases bt_row5
    (Fin.cases bt_row6
    (Fin.cases bt_row7
    (Fin.cases bt_row8
    (Fin.cases bt_row9
    (Fin.cases bt_row10
    (Fin.cases bt_row11
    (Fin.cases bt_row12
    (Fin.cases bt_row13
    (Fin.cases bt_row14
    (Fin.cases bt_row15
    (Fin.cases bt_row16
    (Fin.cases bt_row17
    (Fin.cases bt_row18
    (Fin.cases bt_row19
    (Fin.cases bt_row20
    (Fin.cases bt_row21
    (Fin.cases bt_row22
    (Fin.cases bt_row23
    (Fin.cases bt_row24
    (Fin.cases bt_row25
    (Fin.cases bt_row26
    (Fin.cases bt_row27
    (Fin.cases bt_row28
    (Fin.cases bt_row29
    (Fin.cases bt_row30
    (Fin.cases bt_row31
    (Fin.cases bt_row32
    (Fin.cases bt_row33
    (Fin.cases bt_row34
    (Fin.cases bt_row35
    (Fin.cases bt_row36
    (Fin.cases bt_row37
    (Fin.cases bt_row38
    (Fin.cases bt_row39
    (Fin.cases bt_row40
    (Fin.cases bt_row41
    (Fin.cases bt_row42
    (Fin.cases bt_row43
    (Fin.cases bt_row44
    (Fin.cases bt_row45
    (Fin.cases bt_row46
    (Fin.cases bt_row47
    (Fin.cases bt_row48
    (Fin.cases bt_row49
    (Fin.cases bt_row50
    (Fin.cases bt_row51
    (Fin.cases bt_row52
    (Fin.cases bt_row53
    (Fin.cases bt_row54
    (Fin.cases bt_row55
    (Fin.cases bt_row56
    (Fin.cases bt_row57
    (Fin.cases bt_row58
    (Fin.cases bt_row59
    (Fin.cases bt_row60
    (Fin.cases bt_row61
    (Fin.cases bt_row62
    (Fin.cases bt_row63
    (Fin.cases bt_row64
    (Fin.cases bt_row65
    (Fin.cases bt_row66
    (Fin.cases bt_row67
    (Fin.cases bt_row68
    (Fin.cases bt_row69
    (Fin.cases bt_row70
    (Fin.cases bt_row71
    (Fin.cases bt_row72
    (Fin.cases bt_row73
    (Fin.cases bt_row74
    (Fin.cases bt_row75
    (Fin.cases bt_row76
    (Fin.cases bt_row77
    (Fin.cases bt_row78
    (Fin.cases bt_row79
    (Fin.cases bt_row80
    (Fin.cases bt_row81
    (Fin.cases bt_row82
    (Fin.cases bt_row83
    (Fin.cases bt_row84
    (Fin.cases bt_row85
    (Fin.cases bt_row86
    (Fin.cases bt_row87
    (Fin.cases bt_row88
    (Fin.cases bt_row89
    (Fin.cases bt_row90
    (Fin.cases bt_row91
    (Fin.cases bt_row92
    (Fin.cases bt_row93
    (Fin.cases bt_row94
    (Fin.cases bt_row95
    (Fin.cases bt_row96
    (Fin.cases bt_row97
    (Fin.cases bt_row98
    (Fin.cases bt_row99
    (Fin.cases bt_row100
    (Fin.cases bt_row101
    (Fin.cases bt_row102
    (Fin.cases bt_row103
    (Fin.cases bt_row104
    (Fin.cases bt_row105
    (Fin.cases bt_row106
    (Fin.cases bt_row107
    (Fin.cases bt_row108
    (Fin.cases bt_row109
    (Fin.cases bt_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_bt : localBMatrix * ab7Matrix = btMatrix :=
  decode_mul _ _ _ localB_small ab7_small bt_rows

end Lyons.SimplicityCertificate.LocalCommutant.Words
