module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: seed times v18

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
private theorem transporter_row0 :
    digitsEq 111 (rowProduct (seedRows 0) v18Rows 111) (transporterRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row1 :
    digitsEq 111 (rowProduct (seedRows 1) v18Rows 111) (transporterRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row2 :
    digitsEq 111 (rowProduct (seedRows 2) v18Rows 111) (transporterRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row3 :
    digitsEq 111 (rowProduct (seedRows 3) v18Rows 111) (transporterRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row4 :
    digitsEq 111 (rowProduct (seedRows 4) v18Rows 111) (transporterRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row5 :
    digitsEq 111 (rowProduct (seedRows 5) v18Rows 111) (transporterRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row6 :
    digitsEq 111 (rowProduct (seedRows 6) v18Rows 111) (transporterRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row7 :
    digitsEq 111 (rowProduct (seedRows 7) v18Rows 111) (transporterRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row8 :
    digitsEq 111 (rowProduct (seedRows 8) v18Rows 111) (transporterRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row9 :
    digitsEq 111 (rowProduct (seedRows 9) v18Rows 111) (transporterRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row10 :
    digitsEq 111 (rowProduct (seedRows 10) v18Rows 111) (transporterRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row11 :
    digitsEq 111 (rowProduct (seedRows 11) v18Rows 111) (transporterRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row12 :
    digitsEq 111 (rowProduct (seedRows 12) v18Rows 111) (transporterRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row13 :
    digitsEq 111 (rowProduct (seedRows 13) v18Rows 111) (transporterRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row14 :
    digitsEq 111 (rowProduct (seedRows 14) v18Rows 111) (transporterRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row15 :
    digitsEq 111 (rowProduct (seedRows 15) v18Rows 111) (transporterRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row16 :
    digitsEq 111 (rowProduct (seedRows 16) v18Rows 111) (transporterRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row17 :
    digitsEq 111 (rowProduct (seedRows 17) v18Rows 111) (transporterRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row18 :
    digitsEq 111 (rowProduct (seedRows 18) v18Rows 111) (transporterRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row19 :
    digitsEq 111 (rowProduct (seedRows 19) v18Rows 111) (transporterRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row20 :
    digitsEq 111 (rowProduct (seedRows 20) v18Rows 111) (transporterRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row21 :
    digitsEq 111 (rowProduct (seedRows 21) v18Rows 111) (transporterRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row22 :
    digitsEq 111 (rowProduct (seedRows 22) v18Rows 111) (transporterRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row23 :
    digitsEq 111 (rowProduct (seedRows 23) v18Rows 111) (transporterRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row24 :
    digitsEq 111 (rowProduct (seedRows 24) v18Rows 111) (transporterRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row25 :
    digitsEq 111 (rowProduct (seedRows 25) v18Rows 111) (transporterRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row26 :
    digitsEq 111 (rowProduct (seedRows 26) v18Rows 111) (transporterRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row27 :
    digitsEq 111 (rowProduct (seedRows 27) v18Rows 111) (transporterRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row28 :
    digitsEq 111 (rowProduct (seedRows 28) v18Rows 111) (transporterRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row29 :
    digitsEq 111 (rowProduct (seedRows 29) v18Rows 111) (transporterRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row30 :
    digitsEq 111 (rowProduct (seedRows 30) v18Rows 111) (transporterRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row31 :
    digitsEq 111 (rowProduct (seedRows 31) v18Rows 111) (transporterRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row32 :
    digitsEq 111 (rowProduct (seedRows 32) v18Rows 111) (transporterRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row33 :
    digitsEq 111 (rowProduct (seedRows 33) v18Rows 111) (transporterRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row34 :
    digitsEq 111 (rowProduct (seedRows 34) v18Rows 111) (transporterRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row35 :
    digitsEq 111 (rowProduct (seedRows 35) v18Rows 111) (transporterRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row36 :
    digitsEq 111 (rowProduct (seedRows 36) v18Rows 111) (transporterRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row37 :
    digitsEq 111 (rowProduct (seedRows 37) v18Rows 111) (transporterRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row38 :
    digitsEq 111 (rowProduct (seedRows 38) v18Rows 111) (transporterRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row39 :
    digitsEq 111 (rowProduct (seedRows 39) v18Rows 111) (transporterRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row40 :
    digitsEq 111 (rowProduct (seedRows 40) v18Rows 111) (transporterRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row41 :
    digitsEq 111 (rowProduct (seedRows 41) v18Rows 111) (transporterRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row42 :
    digitsEq 111 (rowProduct (seedRows 42) v18Rows 111) (transporterRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row43 :
    digitsEq 111 (rowProduct (seedRows 43) v18Rows 111) (transporterRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row44 :
    digitsEq 111 (rowProduct (seedRows 44) v18Rows 111) (transporterRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row45 :
    digitsEq 111 (rowProduct (seedRows 45) v18Rows 111) (transporterRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row46 :
    digitsEq 111 (rowProduct (seedRows 46) v18Rows 111) (transporterRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row47 :
    digitsEq 111 (rowProduct (seedRows 47) v18Rows 111) (transporterRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row48 :
    digitsEq 111 (rowProduct (seedRows 48) v18Rows 111) (transporterRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row49 :
    digitsEq 111 (rowProduct (seedRows 49) v18Rows 111) (transporterRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row50 :
    digitsEq 111 (rowProduct (seedRows 50) v18Rows 111) (transporterRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row51 :
    digitsEq 111 (rowProduct (seedRows 51) v18Rows 111) (transporterRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row52 :
    digitsEq 111 (rowProduct (seedRows 52) v18Rows 111) (transporterRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row53 :
    digitsEq 111 (rowProduct (seedRows 53) v18Rows 111) (transporterRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row54 :
    digitsEq 111 (rowProduct (seedRows 54) v18Rows 111) (transporterRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row55 :
    digitsEq 111 (rowProduct (seedRows 55) v18Rows 111) (transporterRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row56 :
    digitsEq 111 (rowProduct (seedRows 56) v18Rows 111) (transporterRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row57 :
    digitsEq 111 (rowProduct (seedRows 57) v18Rows 111) (transporterRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row58 :
    digitsEq 111 (rowProduct (seedRows 58) v18Rows 111) (transporterRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row59 :
    digitsEq 111 (rowProduct (seedRows 59) v18Rows 111) (transporterRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row60 :
    digitsEq 111 (rowProduct (seedRows 60) v18Rows 111) (transporterRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row61 :
    digitsEq 111 (rowProduct (seedRows 61) v18Rows 111) (transporterRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row62 :
    digitsEq 111 (rowProduct (seedRows 62) v18Rows 111) (transporterRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row63 :
    digitsEq 111 (rowProduct (seedRows 63) v18Rows 111) (transporterRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row64 :
    digitsEq 111 (rowProduct (seedRows 64) v18Rows 111) (transporterRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row65 :
    digitsEq 111 (rowProduct (seedRows 65) v18Rows 111) (transporterRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row66 :
    digitsEq 111 (rowProduct (seedRows 66) v18Rows 111) (transporterRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row67 :
    digitsEq 111 (rowProduct (seedRows 67) v18Rows 111) (transporterRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row68 :
    digitsEq 111 (rowProduct (seedRows 68) v18Rows 111) (transporterRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row69 :
    digitsEq 111 (rowProduct (seedRows 69) v18Rows 111) (transporterRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row70 :
    digitsEq 111 (rowProduct (seedRows 70) v18Rows 111) (transporterRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row71 :
    digitsEq 111 (rowProduct (seedRows 71) v18Rows 111) (transporterRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row72 :
    digitsEq 111 (rowProduct (seedRows 72) v18Rows 111) (transporterRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row73 :
    digitsEq 111 (rowProduct (seedRows 73) v18Rows 111) (transporterRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row74 :
    digitsEq 111 (rowProduct (seedRows 74) v18Rows 111) (transporterRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row75 :
    digitsEq 111 (rowProduct (seedRows 75) v18Rows 111) (transporterRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row76 :
    digitsEq 111 (rowProduct (seedRows 76) v18Rows 111) (transporterRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row77 :
    digitsEq 111 (rowProduct (seedRows 77) v18Rows 111) (transporterRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row78 :
    digitsEq 111 (rowProduct (seedRows 78) v18Rows 111) (transporterRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row79 :
    digitsEq 111 (rowProduct (seedRows 79) v18Rows 111) (transporterRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row80 :
    digitsEq 111 (rowProduct (seedRows 80) v18Rows 111) (transporterRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row81 :
    digitsEq 111 (rowProduct (seedRows 81) v18Rows 111) (transporterRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row82 :
    digitsEq 111 (rowProduct (seedRows 82) v18Rows 111) (transporterRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row83 :
    digitsEq 111 (rowProduct (seedRows 83) v18Rows 111) (transporterRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row84 :
    digitsEq 111 (rowProduct (seedRows 84) v18Rows 111) (transporterRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row85 :
    digitsEq 111 (rowProduct (seedRows 85) v18Rows 111) (transporterRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row86 :
    digitsEq 111 (rowProduct (seedRows 86) v18Rows 111) (transporterRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row87 :
    digitsEq 111 (rowProduct (seedRows 87) v18Rows 111) (transporterRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row88 :
    digitsEq 111 (rowProduct (seedRows 88) v18Rows 111) (transporterRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row89 :
    digitsEq 111 (rowProduct (seedRows 89) v18Rows 111) (transporterRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row90 :
    digitsEq 111 (rowProduct (seedRows 90) v18Rows 111) (transporterRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row91 :
    digitsEq 111 (rowProduct (seedRows 91) v18Rows 111) (transporterRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row92 :
    digitsEq 111 (rowProduct (seedRows 92) v18Rows 111) (transporterRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row93 :
    digitsEq 111 (rowProduct (seedRows 93) v18Rows 111) (transporterRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row94 :
    digitsEq 111 (rowProduct (seedRows 94) v18Rows 111) (transporterRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row95 :
    digitsEq 111 (rowProduct (seedRows 95) v18Rows 111) (transporterRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row96 :
    digitsEq 111 (rowProduct (seedRows 96) v18Rows 111) (transporterRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row97 :
    digitsEq 111 (rowProduct (seedRows 97) v18Rows 111) (transporterRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row98 :
    digitsEq 111 (rowProduct (seedRows 98) v18Rows 111) (transporterRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row99 :
    digitsEq 111 (rowProduct (seedRows 99) v18Rows 111) (transporterRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row100 :
    digitsEq 111 (rowProduct (seedRows 100) v18Rows 111) (transporterRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row101 :
    digitsEq 111 (rowProduct (seedRows 101) v18Rows 111) (transporterRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row102 :
    digitsEq 111 (rowProduct (seedRows 102) v18Rows 111) (transporterRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row103 :
    digitsEq 111 (rowProduct (seedRows 103) v18Rows 111) (transporterRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row104 :
    digitsEq 111 (rowProduct (seedRows 104) v18Rows 111) (transporterRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row105 :
    digitsEq 111 (rowProduct (seedRows 105) v18Rows 111) (transporterRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row106 :
    digitsEq 111 (rowProduct (seedRows 106) v18Rows 111) (transporterRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row107 :
    digitsEq 111 (rowProduct (seedRows 107) v18Rows 111) (transporterRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row108 :
    digitsEq 111 (rowProduct (seedRows 108) v18Rows 111) (transporterRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row109 :
    digitsEq 111 (rowProduct (seedRows 109) v18Rows 111) (transporterRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem transporter_row110 :
    digitsEq 111 (rowProduct (seedRows 110) v18Rows 111) (transporterRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem transporter_rows : ∀ i,
    digitsEq 111 (rowProduct (seedRows i) v18Rows 111) (transporterRows i) = true :=
  (Fin.cases transporter_row0
    (Fin.cases transporter_row1
    (Fin.cases transporter_row2
    (Fin.cases transporter_row3
    (Fin.cases transporter_row4
    (Fin.cases transporter_row5
    (Fin.cases transporter_row6
    (Fin.cases transporter_row7
    (Fin.cases transporter_row8
    (Fin.cases transporter_row9
    (Fin.cases transporter_row10
    (Fin.cases transporter_row11
    (Fin.cases transporter_row12
    (Fin.cases transporter_row13
    (Fin.cases transporter_row14
    (Fin.cases transporter_row15
    (Fin.cases transporter_row16
    (Fin.cases transporter_row17
    (Fin.cases transporter_row18
    (Fin.cases transporter_row19
    (Fin.cases transporter_row20
    (Fin.cases transporter_row21
    (Fin.cases transporter_row22
    (Fin.cases transporter_row23
    (Fin.cases transporter_row24
    (Fin.cases transporter_row25
    (Fin.cases transporter_row26
    (Fin.cases transporter_row27
    (Fin.cases transporter_row28
    (Fin.cases transporter_row29
    (Fin.cases transporter_row30
    (Fin.cases transporter_row31
    (Fin.cases transporter_row32
    (Fin.cases transporter_row33
    (Fin.cases transporter_row34
    (Fin.cases transporter_row35
    (Fin.cases transporter_row36
    (Fin.cases transporter_row37
    (Fin.cases transporter_row38
    (Fin.cases transporter_row39
    (Fin.cases transporter_row40
    (Fin.cases transporter_row41
    (Fin.cases transporter_row42
    (Fin.cases transporter_row43
    (Fin.cases transporter_row44
    (Fin.cases transporter_row45
    (Fin.cases transporter_row46
    (Fin.cases transporter_row47
    (Fin.cases transporter_row48
    (Fin.cases transporter_row49
    (Fin.cases transporter_row50
    (Fin.cases transporter_row51
    (Fin.cases transporter_row52
    (Fin.cases transporter_row53
    (Fin.cases transporter_row54
    (Fin.cases transporter_row55
    (Fin.cases transporter_row56
    (Fin.cases transporter_row57
    (Fin.cases transporter_row58
    (Fin.cases transporter_row59
    (Fin.cases transporter_row60
    (Fin.cases transporter_row61
    (Fin.cases transporter_row62
    (Fin.cases transporter_row63
    (Fin.cases transporter_row64
    (Fin.cases transporter_row65
    (Fin.cases transporter_row66
    (Fin.cases transporter_row67
    (Fin.cases transporter_row68
    (Fin.cases transporter_row69
    (Fin.cases transporter_row70
    (Fin.cases transporter_row71
    (Fin.cases transporter_row72
    (Fin.cases transporter_row73
    (Fin.cases transporter_row74
    (Fin.cases transporter_row75
    (Fin.cases transporter_row76
    (Fin.cases transporter_row77
    (Fin.cases transporter_row78
    (Fin.cases transporter_row79
    (Fin.cases transporter_row80
    (Fin.cases transporter_row81
    (Fin.cases transporter_row82
    (Fin.cases transporter_row83
    (Fin.cases transporter_row84
    (Fin.cases transporter_row85
    (Fin.cases transporter_row86
    (Fin.cases transporter_row87
    (Fin.cases transporter_row88
    (Fin.cases transporter_row89
    (Fin.cases transporter_row90
    (Fin.cases transporter_row91
    (Fin.cases transporter_row92
    (Fin.cases transporter_row93
    (Fin.cases transporter_row94
    (Fin.cases transporter_row95
    (Fin.cases transporter_row96
    (Fin.cases transporter_row97
    (Fin.cases transporter_row98
    (Fin.cases transporter_row99
    (Fin.cases transporter_row100
    (Fin.cases transporter_row101
    (Fin.cases transporter_row102
    (Fin.cases transporter_row103
    (Fin.cases transporter_row104
    (Fin.cases transporter_row105
    (Fin.cases transporter_row106
    (Fin.cases transporter_row107
    (Fin.cases transporter_row108
    (Fin.cases transporter_row109
    (Fin.cases transporter_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_transporter : seedMatrix * v18Matrix = transporterMatrix :=
  decode_mul _ _ _ seed_small v18_small transporter_rows

end Lyons.Atlas111InvolutionWords
