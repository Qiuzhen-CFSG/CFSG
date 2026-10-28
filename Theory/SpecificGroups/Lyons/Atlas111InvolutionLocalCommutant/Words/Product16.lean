module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Data

/-!
# Involution word multiplication: ab7 times localB

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
private theorem tb_row0 :
    digitsEq 111 (rowProduct (ab7Rows 0) localBRows 111) (btRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row1 :
    digitsEq 111 (rowProduct (ab7Rows 1) localBRows 111) (btRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row2 :
    digitsEq 111 (rowProduct (ab7Rows 2) localBRows 111) (btRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row3 :
    digitsEq 111 (rowProduct (ab7Rows 3) localBRows 111) (btRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row4 :
    digitsEq 111 (rowProduct (ab7Rows 4) localBRows 111) (btRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row5 :
    digitsEq 111 (rowProduct (ab7Rows 5) localBRows 111) (btRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row6 :
    digitsEq 111 (rowProduct (ab7Rows 6) localBRows 111) (btRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row7 :
    digitsEq 111 (rowProduct (ab7Rows 7) localBRows 111) (btRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row8 :
    digitsEq 111 (rowProduct (ab7Rows 8) localBRows 111) (btRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row9 :
    digitsEq 111 (rowProduct (ab7Rows 9) localBRows 111) (btRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row10 :
    digitsEq 111 (rowProduct (ab7Rows 10) localBRows 111) (btRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row11 :
    digitsEq 111 (rowProduct (ab7Rows 11) localBRows 111) (btRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row12 :
    digitsEq 111 (rowProduct (ab7Rows 12) localBRows 111) (btRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row13 :
    digitsEq 111 (rowProduct (ab7Rows 13) localBRows 111) (btRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row14 :
    digitsEq 111 (rowProduct (ab7Rows 14) localBRows 111) (btRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row15 :
    digitsEq 111 (rowProduct (ab7Rows 15) localBRows 111) (btRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row16 :
    digitsEq 111 (rowProduct (ab7Rows 16) localBRows 111) (btRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row17 :
    digitsEq 111 (rowProduct (ab7Rows 17) localBRows 111) (btRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row18 :
    digitsEq 111 (rowProduct (ab7Rows 18) localBRows 111) (btRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row19 :
    digitsEq 111 (rowProduct (ab7Rows 19) localBRows 111) (btRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row20 :
    digitsEq 111 (rowProduct (ab7Rows 20) localBRows 111) (btRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row21 :
    digitsEq 111 (rowProduct (ab7Rows 21) localBRows 111) (btRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row22 :
    digitsEq 111 (rowProduct (ab7Rows 22) localBRows 111) (btRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row23 :
    digitsEq 111 (rowProduct (ab7Rows 23) localBRows 111) (btRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row24 :
    digitsEq 111 (rowProduct (ab7Rows 24) localBRows 111) (btRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row25 :
    digitsEq 111 (rowProduct (ab7Rows 25) localBRows 111) (btRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row26 :
    digitsEq 111 (rowProduct (ab7Rows 26) localBRows 111) (btRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row27 :
    digitsEq 111 (rowProduct (ab7Rows 27) localBRows 111) (btRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row28 :
    digitsEq 111 (rowProduct (ab7Rows 28) localBRows 111) (btRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row29 :
    digitsEq 111 (rowProduct (ab7Rows 29) localBRows 111) (btRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row30 :
    digitsEq 111 (rowProduct (ab7Rows 30) localBRows 111) (btRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row31 :
    digitsEq 111 (rowProduct (ab7Rows 31) localBRows 111) (btRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row32 :
    digitsEq 111 (rowProduct (ab7Rows 32) localBRows 111) (btRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row33 :
    digitsEq 111 (rowProduct (ab7Rows 33) localBRows 111) (btRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row34 :
    digitsEq 111 (rowProduct (ab7Rows 34) localBRows 111) (btRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row35 :
    digitsEq 111 (rowProduct (ab7Rows 35) localBRows 111) (btRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row36 :
    digitsEq 111 (rowProduct (ab7Rows 36) localBRows 111) (btRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row37 :
    digitsEq 111 (rowProduct (ab7Rows 37) localBRows 111) (btRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row38 :
    digitsEq 111 (rowProduct (ab7Rows 38) localBRows 111) (btRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row39 :
    digitsEq 111 (rowProduct (ab7Rows 39) localBRows 111) (btRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row40 :
    digitsEq 111 (rowProduct (ab7Rows 40) localBRows 111) (btRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row41 :
    digitsEq 111 (rowProduct (ab7Rows 41) localBRows 111) (btRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row42 :
    digitsEq 111 (rowProduct (ab7Rows 42) localBRows 111) (btRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row43 :
    digitsEq 111 (rowProduct (ab7Rows 43) localBRows 111) (btRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row44 :
    digitsEq 111 (rowProduct (ab7Rows 44) localBRows 111) (btRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row45 :
    digitsEq 111 (rowProduct (ab7Rows 45) localBRows 111) (btRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row46 :
    digitsEq 111 (rowProduct (ab7Rows 46) localBRows 111) (btRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row47 :
    digitsEq 111 (rowProduct (ab7Rows 47) localBRows 111) (btRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row48 :
    digitsEq 111 (rowProduct (ab7Rows 48) localBRows 111) (btRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row49 :
    digitsEq 111 (rowProduct (ab7Rows 49) localBRows 111) (btRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row50 :
    digitsEq 111 (rowProduct (ab7Rows 50) localBRows 111) (btRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row51 :
    digitsEq 111 (rowProduct (ab7Rows 51) localBRows 111) (btRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row52 :
    digitsEq 111 (rowProduct (ab7Rows 52) localBRows 111) (btRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row53 :
    digitsEq 111 (rowProduct (ab7Rows 53) localBRows 111) (btRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row54 :
    digitsEq 111 (rowProduct (ab7Rows 54) localBRows 111) (btRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row55 :
    digitsEq 111 (rowProduct (ab7Rows 55) localBRows 111) (btRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row56 :
    digitsEq 111 (rowProduct (ab7Rows 56) localBRows 111) (btRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row57 :
    digitsEq 111 (rowProduct (ab7Rows 57) localBRows 111) (btRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row58 :
    digitsEq 111 (rowProduct (ab7Rows 58) localBRows 111) (btRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row59 :
    digitsEq 111 (rowProduct (ab7Rows 59) localBRows 111) (btRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row60 :
    digitsEq 111 (rowProduct (ab7Rows 60) localBRows 111) (btRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row61 :
    digitsEq 111 (rowProduct (ab7Rows 61) localBRows 111) (btRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row62 :
    digitsEq 111 (rowProduct (ab7Rows 62) localBRows 111) (btRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row63 :
    digitsEq 111 (rowProduct (ab7Rows 63) localBRows 111) (btRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row64 :
    digitsEq 111 (rowProduct (ab7Rows 64) localBRows 111) (btRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row65 :
    digitsEq 111 (rowProduct (ab7Rows 65) localBRows 111) (btRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row66 :
    digitsEq 111 (rowProduct (ab7Rows 66) localBRows 111) (btRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row67 :
    digitsEq 111 (rowProduct (ab7Rows 67) localBRows 111) (btRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row68 :
    digitsEq 111 (rowProduct (ab7Rows 68) localBRows 111) (btRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row69 :
    digitsEq 111 (rowProduct (ab7Rows 69) localBRows 111) (btRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row70 :
    digitsEq 111 (rowProduct (ab7Rows 70) localBRows 111) (btRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row71 :
    digitsEq 111 (rowProduct (ab7Rows 71) localBRows 111) (btRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row72 :
    digitsEq 111 (rowProduct (ab7Rows 72) localBRows 111) (btRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row73 :
    digitsEq 111 (rowProduct (ab7Rows 73) localBRows 111) (btRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row74 :
    digitsEq 111 (rowProduct (ab7Rows 74) localBRows 111) (btRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row75 :
    digitsEq 111 (rowProduct (ab7Rows 75) localBRows 111) (btRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row76 :
    digitsEq 111 (rowProduct (ab7Rows 76) localBRows 111) (btRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row77 :
    digitsEq 111 (rowProduct (ab7Rows 77) localBRows 111) (btRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row78 :
    digitsEq 111 (rowProduct (ab7Rows 78) localBRows 111) (btRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row79 :
    digitsEq 111 (rowProduct (ab7Rows 79) localBRows 111) (btRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row80 :
    digitsEq 111 (rowProduct (ab7Rows 80) localBRows 111) (btRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row81 :
    digitsEq 111 (rowProduct (ab7Rows 81) localBRows 111) (btRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row82 :
    digitsEq 111 (rowProduct (ab7Rows 82) localBRows 111) (btRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row83 :
    digitsEq 111 (rowProduct (ab7Rows 83) localBRows 111) (btRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row84 :
    digitsEq 111 (rowProduct (ab7Rows 84) localBRows 111) (btRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row85 :
    digitsEq 111 (rowProduct (ab7Rows 85) localBRows 111) (btRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row86 :
    digitsEq 111 (rowProduct (ab7Rows 86) localBRows 111) (btRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row87 :
    digitsEq 111 (rowProduct (ab7Rows 87) localBRows 111) (btRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row88 :
    digitsEq 111 (rowProduct (ab7Rows 88) localBRows 111) (btRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row89 :
    digitsEq 111 (rowProduct (ab7Rows 89) localBRows 111) (btRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row90 :
    digitsEq 111 (rowProduct (ab7Rows 90) localBRows 111) (btRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row91 :
    digitsEq 111 (rowProduct (ab7Rows 91) localBRows 111) (btRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row92 :
    digitsEq 111 (rowProduct (ab7Rows 92) localBRows 111) (btRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row93 :
    digitsEq 111 (rowProduct (ab7Rows 93) localBRows 111) (btRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row94 :
    digitsEq 111 (rowProduct (ab7Rows 94) localBRows 111) (btRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row95 :
    digitsEq 111 (rowProduct (ab7Rows 95) localBRows 111) (btRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row96 :
    digitsEq 111 (rowProduct (ab7Rows 96) localBRows 111) (btRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row97 :
    digitsEq 111 (rowProduct (ab7Rows 97) localBRows 111) (btRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row98 :
    digitsEq 111 (rowProduct (ab7Rows 98) localBRows 111) (btRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row99 :
    digitsEq 111 (rowProduct (ab7Rows 99) localBRows 111) (btRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row100 :
    digitsEq 111 (rowProduct (ab7Rows 100) localBRows 111) (btRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row101 :
    digitsEq 111 (rowProduct (ab7Rows 101) localBRows 111) (btRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row102 :
    digitsEq 111 (rowProduct (ab7Rows 102) localBRows 111) (btRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row103 :
    digitsEq 111 (rowProduct (ab7Rows 103) localBRows 111) (btRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row104 :
    digitsEq 111 (rowProduct (ab7Rows 104) localBRows 111) (btRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row105 :
    digitsEq 111 (rowProduct (ab7Rows 105) localBRows 111) (btRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row106 :
    digitsEq 111 (rowProduct (ab7Rows 106) localBRows 111) (btRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row107 :
    digitsEq 111 (rowProduct (ab7Rows 107) localBRows 111) (btRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row108 :
    digitsEq 111 (rowProduct (ab7Rows 108) localBRows 111) (btRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row109 :
    digitsEq 111 (rowProduct (ab7Rows 109) localBRows 111) (btRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tb_row110 :
    digitsEq 111 (rowProduct (ab7Rows 110) localBRows 111) (btRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem tb_rows : ∀ i,
    digitsEq 111 (rowProduct (ab7Rows i) localBRows 111) (btRows i) = true :=
  (Fin.cases tb_row0
    (Fin.cases tb_row1
    (Fin.cases tb_row2
    (Fin.cases tb_row3
    (Fin.cases tb_row4
    (Fin.cases tb_row5
    (Fin.cases tb_row6
    (Fin.cases tb_row7
    (Fin.cases tb_row8
    (Fin.cases tb_row9
    (Fin.cases tb_row10
    (Fin.cases tb_row11
    (Fin.cases tb_row12
    (Fin.cases tb_row13
    (Fin.cases tb_row14
    (Fin.cases tb_row15
    (Fin.cases tb_row16
    (Fin.cases tb_row17
    (Fin.cases tb_row18
    (Fin.cases tb_row19
    (Fin.cases tb_row20
    (Fin.cases tb_row21
    (Fin.cases tb_row22
    (Fin.cases tb_row23
    (Fin.cases tb_row24
    (Fin.cases tb_row25
    (Fin.cases tb_row26
    (Fin.cases tb_row27
    (Fin.cases tb_row28
    (Fin.cases tb_row29
    (Fin.cases tb_row30
    (Fin.cases tb_row31
    (Fin.cases tb_row32
    (Fin.cases tb_row33
    (Fin.cases tb_row34
    (Fin.cases tb_row35
    (Fin.cases tb_row36
    (Fin.cases tb_row37
    (Fin.cases tb_row38
    (Fin.cases tb_row39
    (Fin.cases tb_row40
    (Fin.cases tb_row41
    (Fin.cases tb_row42
    (Fin.cases tb_row43
    (Fin.cases tb_row44
    (Fin.cases tb_row45
    (Fin.cases tb_row46
    (Fin.cases tb_row47
    (Fin.cases tb_row48
    (Fin.cases tb_row49
    (Fin.cases tb_row50
    (Fin.cases tb_row51
    (Fin.cases tb_row52
    (Fin.cases tb_row53
    (Fin.cases tb_row54
    (Fin.cases tb_row55
    (Fin.cases tb_row56
    (Fin.cases tb_row57
    (Fin.cases tb_row58
    (Fin.cases tb_row59
    (Fin.cases tb_row60
    (Fin.cases tb_row61
    (Fin.cases tb_row62
    (Fin.cases tb_row63
    (Fin.cases tb_row64
    (Fin.cases tb_row65
    (Fin.cases tb_row66
    (Fin.cases tb_row67
    (Fin.cases tb_row68
    (Fin.cases tb_row69
    (Fin.cases tb_row70
    (Fin.cases tb_row71
    (Fin.cases tb_row72
    (Fin.cases tb_row73
    (Fin.cases tb_row74
    (Fin.cases tb_row75
    (Fin.cases tb_row76
    (Fin.cases tb_row77
    (Fin.cases tb_row78
    (Fin.cases tb_row79
    (Fin.cases tb_row80
    (Fin.cases tb_row81
    (Fin.cases tb_row82
    (Fin.cases tb_row83
    (Fin.cases tb_row84
    (Fin.cases tb_row85
    (Fin.cases tb_row86
    (Fin.cases tb_row87
    (Fin.cases tb_row88
    (Fin.cases tb_row89
    (Fin.cases tb_row90
    (Fin.cases tb_row91
    (Fin.cases tb_row92
    (Fin.cases tb_row93
    (Fin.cases tb_row94
    (Fin.cases tb_row95
    (Fin.cases tb_row96
    (Fin.cases tb_row97
    (Fin.cases tb_row98
    (Fin.cases tb_row99
    (Fin.cases tb_row100
    (Fin.cases tb_row101
    (Fin.cases tb_row102
    (Fin.cases tb_row103
    (Fin.cases tb_row104
    (Fin.cases tb_row105
    (Fin.cases tb_row106
    (Fin.cases tb_row107
    (Fin.cases tb_row108
    (Fin.cases tb_row109
    (Fin.cases tb_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_tb : ab7Matrix * localBMatrix = btMatrix :=
  decode_mul _ _ _ ab7_small localB_small tb_rows

end Lyons.SimplicityCertificate.LocalCommutant.Words
