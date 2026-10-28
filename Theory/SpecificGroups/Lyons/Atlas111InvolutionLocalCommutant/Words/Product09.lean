module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Data

/-!
# Involution word multiplication: rtInv times tr

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
private theorem c_row0 :
    digitsEq 111 (rowProduct (rtInvRows 0) trRows 111) (cRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row1 :
    digitsEq 111 (rowProduct (rtInvRows 1) trRows 111) (cRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row2 :
    digitsEq 111 (rowProduct (rtInvRows 2) trRows 111) (cRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row3 :
    digitsEq 111 (rowProduct (rtInvRows 3) trRows 111) (cRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row4 :
    digitsEq 111 (rowProduct (rtInvRows 4) trRows 111) (cRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row5 :
    digitsEq 111 (rowProduct (rtInvRows 5) trRows 111) (cRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row6 :
    digitsEq 111 (rowProduct (rtInvRows 6) trRows 111) (cRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row7 :
    digitsEq 111 (rowProduct (rtInvRows 7) trRows 111) (cRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row8 :
    digitsEq 111 (rowProduct (rtInvRows 8) trRows 111) (cRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row9 :
    digitsEq 111 (rowProduct (rtInvRows 9) trRows 111) (cRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row10 :
    digitsEq 111 (rowProduct (rtInvRows 10) trRows 111) (cRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row11 :
    digitsEq 111 (rowProduct (rtInvRows 11) trRows 111) (cRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row12 :
    digitsEq 111 (rowProduct (rtInvRows 12) trRows 111) (cRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row13 :
    digitsEq 111 (rowProduct (rtInvRows 13) trRows 111) (cRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row14 :
    digitsEq 111 (rowProduct (rtInvRows 14) trRows 111) (cRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row15 :
    digitsEq 111 (rowProduct (rtInvRows 15) trRows 111) (cRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row16 :
    digitsEq 111 (rowProduct (rtInvRows 16) trRows 111) (cRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row17 :
    digitsEq 111 (rowProduct (rtInvRows 17) trRows 111) (cRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row18 :
    digitsEq 111 (rowProduct (rtInvRows 18) trRows 111) (cRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row19 :
    digitsEq 111 (rowProduct (rtInvRows 19) trRows 111) (cRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row20 :
    digitsEq 111 (rowProduct (rtInvRows 20) trRows 111) (cRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row21 :
    digitsEq 111 (rowProduct (rtInvRows 21) trRows 111) (cRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row22 :
    digitsEq 111 (rowProduct (rtInvRows 22) trRows 111) (cRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row23 :
    digitsEq 111 (rowProduct (rtInvRows 23) trRows 111) (cRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row24 :
    digitsEq 111 (rowProduct (rtInvRows 24) trRows 111) (cRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row25 :
    digitsEq 111 (rowProduct (rtInvRows 25) trRows 111) (cRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row26 :
    digitsEq 111 (rowProduct (rtInvRows 26) trRows 111) (cRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row27 :
    digitsEq 111 (rowProduct (rtInvRows 27) trRows 111) (cRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row28 :
    digitsEq 111 (rowProduct (rtInvRows 28) trRows 111) (cRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row29 :
    digitsEq 111 (rowProduct (rtInvRows 29) trRows 111) (cRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row30 :
    digitsEq 111 (rowProduct (rtInvRows 30) trRows 111) (cRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row31 :
    digitsEq 111 (rowProduct (rtInvRows 31) trRows 111) (cRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row32 :
    digitsEq 111 (rowProduct (rtInvRows 32) trRows 111) (cRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row33 :
    digitsEq 111 (rowProduct (rtInvRows 33) trRows 111) (cRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row34 :
    digitsEq 111 (rowProduct (rtInvRows 34) trRows 111) (cRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row35 :
    digitsEq 111 (rowProduct (rtInvRows 35) trRows 111) (cRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row36 :
    digitsEq 111 (rowProduct (rtInvRows 36) trRows 111) (cRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row37 :
    digitsEq 111 (rowProduct (rtInvRows 37) trRows 111) (cRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row38 :
    digitsEq 111 (rowProduct (rtInvRows 38) trRows 111) (cRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row39 :
    digitsEq 111 (rowProduct (rtInvRows 39) trRows 111) (cRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row40 :
    digitsEq 111 (rowProduct (rtInvRows 40) trRows 111) (cRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row41 :
    digitsEq 111 (rowProduct (rtInvRows 41) trRows 111) (cRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row42 :
    digitsEq 111 (rowProduct (rtInvRows 42) trRows 111) (cRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row43 :
    digitsEq 111 (rowProduct (rtInvRows 43) trRows 111) (cRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row44 :
    digitsEq 111 (rowProduct (rtInvRows 44) trRows 111) (cRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row45 :
    digitsEq 111 (rowProduct (rtInvRows 45) trRows 111) (cRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row46 :
    digitsEq 111 (rowProduct (rtInvRows 46) trRows 111) (cRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row47 :
    digitsEq 111 (rowProduct (rtInvRows 47) trRows 111) (cRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row48 :
    digitsEq 111 (rowProduct (rtInvRows 48) trRows 111) (cRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row49 :
    digitsEq 111 (rowProduct (rtInvRows 49) trRows 111) (cRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row50 :
    digitsEq 111 (rowProduct (rtInvRows 50) trRows 111) (cRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row51 :
    digitsEq 111 (rowProduct (rtInvRows 51) trRows 111) (cRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row52 :
    digitsEq 111 (rowProduct (rtInvRows 52) trRows 111) (cRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row53 :
    digitsEq 111 (rowProduct (rtInvRows 53) trRows 111) (cRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row54 :
    digitsEq 111 (rowProduct (rtInvRows 54) trRows 111) (cRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row55 :
    digitsEq 111 (rowProduct (rtInvRows 55) trRows 111) (cRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row56 :
    digitsEq 111 (rowProduct (rtInvRows 56) trRows 111) (cRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row57 :
    digitsEq 111 (rowProduct (rtInvRows 57) trRows 111) (cRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row58 :
    digitsEq 111 (rowProduct (rtInvRows 58) trRows 111) (cRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row59 :
    digitsEq 111 (rowProduct (rtInvRows 59) trRows 111) (cRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row60 :
    digitsEq 111 (rowProduct (rtInvRows 60) trRows 111) (cRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row61 :
    digitsEq 111 (rowProduct (rtInvRows 61) trRows 111) (cRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row62 :
    digitsEq 111 (rowProduct (rtInvRows 62) trRows 111) (cRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row63 :
    digitsEq 111 (rowProduct (rtInvRows 63) trRows 111) (cRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row64 :
    digitsEq 111 (rowProduct (rtInvRows 64) trRows 111) (cRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row65 :
    digitsEq 111 (rowProduct (rtInvRows 65) trRows 111) (cRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row66 :
    digitsEq 111 (rowProduct (rtInvRows 66) trRows 111) (cRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row67 :
    digitsEq 111 (rowProduct (rtInvRows 67) trRows 111) (cRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row68 :
    digitsEq 111 (rowProduct (rtInvRows 68) trRows 111) (cRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row69 :
    digitsEq 111 (rowProduct (rtInvRows 69) trRows 111) (cRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row70 :
    digitsEq 111 (rowProduct (rtInvRows 70) trRows 111) (cRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row71 :
    digitsEq 111 (rowProduct (rtInvRows 71) trRows 111) (cRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row72 :
    digitsEq 111 (rowProduct (rtInvRows 72) trRows 111) (cRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row73 :
    digitsEq 111 (rowProduct (rtInvRows 73) trRows 111) (cRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row74 :
    digitsEq 111 (rowProduct (rtInvRows 74) trRows 111) (cRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row75 :
    digitsEq 111 (rowProduct (rtInvRows 75) trRows 111) (cRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row76 :
    digitsEq 111 (rowProduct (rtInvRows 76) trRows 111) (cRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row77 :
    digitsEq 111 (rowProduct (rtInvRows 77) trRows 111) (cRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row78 :
    digitsEq 111 (rowProduct (rtInvRows 78) trRows 111) (cRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row79 :
    digitsEq 111 (rowProduct (rtInvRows 79) trRows 111) (cRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row80 :
    digitsEq 111 (rowProduct (rtInvRows 80) trRows 111) (cRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row81 :
    digitsEq 111 (rowProduct (rtInvRows 81) trRows 111) (cRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row82 :
    digitsEq 111 (rowProduct (rtInvRows 82) trRows 111) (cRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row83 :
    digitsEq 111 (rowProduct (rtInvRows 83) trRows 111) (cRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row84 :
    digitsEq 111 (rowProduct (rtInvRows 84) trRows 111) (cRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row85 :
    digitsEq 111 (rowProduct (rtInvRows 85) trRows 111) (cRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row86 :
    digitsEq 111 (rowProduct (rtInvRows 86) trRows 111) (cRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row87 :
    digitsEq 111 (rowProduct (rtInvRows 87) trRows 111) (cRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row88 :
    digitsEq 111 (rowProduct (rtInvRows 88) trRows 111) (cRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row89 :
    digitsEq 111 (rowProduct (rtInvRows 89) trRows 111) (cRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row90 :
    digitsEq 111 (rowProduct (rtInvRows 90) trRows 111) (cRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row91 :
    digitsEq 111 (rowProduct (rtInvRows 91) trRows 111) (cRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row92 :
    digitsEq 111 (rowProduct (rtInvRows 92) trRows 111) (cRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row93 :
    digitsEq 111 (rowProduct (rtInvRows 93) trRows 111) (cRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row94 :
    digitsEq 111 (rowProduct (rtInvRows 94) trRows 111) (cRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row95 :
    digitsEq 111 (rowProduct (rtInvRows 95) trRows 111) (cRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row96 :
    digitsEq 111 (rowProduct (rtInvRows 96) trRows 111) (cRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row97 :
    digitsEq 111 (rowProduct (rtInvRows 97) trRows 111) (cRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row98 :
    digitsEq 111 (rowProduct (rtInvRows 98) trRows 111) (cRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row99 :
    digitsEq 111 (rowProduct (rtInvRows 99) trRows 111) (cRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row100 :
    digitsEq 111 (rowProduct (rtInvRows 100) trRows 111) (cRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row101 :
    digitsEq 111 (rowProduct (rtInvRows 101) trRows 111) (cRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row102 :
    digitsEq 111 (rowProduct (rtInvRows 102) trRows 111) (cRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row103 :
    digitsEq 111 (rowProduct (rtInvRows 103) trRows 111) (cRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row104 :
    digitsEq 111 (rowProduct (rtInvRows 104) trRows 111) (cRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row105 :
    digitsEq 111 (rowProduct (rtInvRows 105) trRows 111) (cRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row106 :
    digitsEq 111 (rowProduct (rtInvRows 106) trRows 111) (cRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row107 :
    digitsEq 111 (rowProduct (rtInvRows 107) trRows 111) (cRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row108 :
    digitsEq 111 (rowProduct (rtInvRows 108) trRows 111) (cRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row109 :
    digitsEq 111 (rowProduct (rtInvRows 109) trRows 111) (cRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem c_row110 :
    digitsEq 111 (rowProduct (rtInvRows 110) trRows 111) (cRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem c_rows : ∀ i,
    digitsEq 111 (rowProduct (rtInvRows i) trRows 111) (cRows i) = true :=
  (Fin.cases c_row0
    (Fin.cases c_row1
    (Fin.cases c_row2
    (Fin.cases c_row3
    (Fin.cases c_row4
    (Fin.cases c_row5
    (Fin.cases c_row6
    (Fin.cases c_row7
    (Fin.cases c_row8
    (Fin.cases c_row9
    (Fin.cases c_row10
    (Fin.cases c_row11
    (Fin.cases c_row12
    (Fin.cases c_row13
    (Fin.cases c_row14
    (Fin.cases c_row15
    (Fin.cases c_row16
    (Fin.cases c_row17
    (Fin.cases c_row18
    (Fin.cases c_row19
    (Fin.cases c_row20
    (Fin.cases c_row21
    (Fin.cases c_row22
    (Fin.cases c_row23
    (Fin.cases c_row24
    (Fin.cases c_row25
    (Fin.cases c_row26
    (Fin.cases c_row27
    (Fin.cases c_row28
    (Fin.cases c_row29
    (Fin.cases c_row30
    (Fin.cases c_row31
    (Fin.cases c_row32
    (Fin.cases c_row33
    (Fin.cases c_row34
    (Fin.cases c_row35
    (Fin.cases c_row36
    (Fin.cases c_row37
    (Fin.cases c_row38
    (Fin.cases c_row39
    (Fin.cases c_row40
    (Fin.cases c_row41
    (Fin.cases c_row42
    (Fin.cases c_row43
    (Fin.cases c_row44
    (Fin.cases c_row45
    (Fin.cases c_row46
    (Fin.cases c_row47
    (Fin.cases c_row48
    (Fin.cases c_row49
    (Fin.cases c_row50
    (Fin.cases c_row51
    (Fin.cases c_row52
    (Fin.cases c_row53
    (Fin.cases c_row54
    (Fin.cases c_row55
    (Fin.cases c_row56
    (Fin.cases c_row57
    (Fin.cases c_row58
    (Fin.cases c_row59
    (Fin.cases c_row60
    (Fin.cases c_row61
    (Fin.cases c_row62
    (Fin.cases c_row63
    (Fin.cases c_row64
    (Fin.cases c_row65
    (Fin.cases c_row66
    (Fin.cases c_row67
    (Fin.cases c_row68
    (Fin.cases c_row69
    (Fin.cases c_row70
    (Fin.cases c_row71
    (Fin.cases c_row72
    (Fin.cases c_row73
    (Fin.cases c_row74
    (Fin.cases c_row75
    (Fin.cases c_row76
    (Fin.cases c_row77
    (Fin.cases c_row78
    (Fin.cases c_row79
    (Fin.cases c_row80
    (Fin.cases c_row81
    (Fin.cases c_row82
    (Fin.cases c_row83
    (Fin.cases c_row84
    (Fin.cases c_row85
    (Fin.cases c_row86
    (Fin.cases c_row87
    (Fin.cases c_row88
    (Fin.cases c_row89
    (Fin.cases c_row90
    (Fin.cases c_row91
    (Fin.cases c_row92
    (Fin.cases c_row93
    (Fin.cases c_row94
    (Fin.cases c_row95
    (Fin.cases c_row96
    (Fin.cases c_row97
    (Fin.cases c_row98
    (Fin.cases c_row99
    (Fin.cases c_row100
    (Fin.cases c_row101
    (Fin.cases c_row102
    (Fin.cases c_row103
    (Fin.cases c_row104
    (Fin.cases c_row105
    (Fin.cases c_row106
    (Fin.cases c_row107
    (Fin.cases c_row108
    (Fin.cases c_row109
    (Fin.cases c_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_c : rtInvMatrix * trMatrix = cMatrix :=
  decode_mul _ _ _ rtInv_small tr_small c_rows

end Lyons.SimplicityCertificate.LocalCommutant.Words
