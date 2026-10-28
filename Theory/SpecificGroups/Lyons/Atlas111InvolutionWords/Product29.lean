module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords.Data

/-!
# Involution word multiplication: transporter times a

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
private theorem wa_row0 :
    digitsEq 111 (rowProduct (transporterRows 0) aRows 111) (twRows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row1 :
    digitsEq 111 (rowProduct (transporterRows 1) aRows 111) (twRows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row2 :
    digitsEq 111 (rowProduct (transporterRows 2) aRows 111) (twRows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row3 :
    digitsEq 111 (rowProduct (transporterRows 3) aRows 111) (twRows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row4 :
    digitsEq 111 (rowProduct (transporterRows 4) aRows 111) (twRows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row5 :
    digitsEq 111 (rowProduct (transporterRows 5) aRows 111) (twRows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row6 :
    digitsEq 111 (rowProduct (transporterRows 6) aRows 111) (twRows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row7 :
    digitsEq 111 (rowProduct (transporterRows 7) aRows 111) (twRows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row8 :
    digitsEq 111 (rowProduct (transporterRows 8) aRows 111) (twRows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row9 :
    digitsEq 111 (rowProduct (transporterRows 9) aRows 111) (twRows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row10 :
    digitsEq 111 (rowProduct (transporterRows 10) aRows 111) (twRows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row11 :
    digitsEq 111 (rowProduct (transporterRows 11) aRows 111) (twRows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row12 :
    digitsEq 111 (rowProduct (transporterRows 12) aRows 111) (twRows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row13 :
    digitsEq 111 (rowProduct (transporterRows 13) aRows 111) (twRows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row14 :
    digitsEq 111 (rowProduct (transporterRows 14) aRows 111) (twRows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row15 :
    digitsEq 111 (rowProduct (transporterRows 15) aRows 111) (twRows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row16 :
    digitsEq 111 (rowProduct (transporterRows 16) aRows 111) (twRows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row17 :
    digitsEq 111 (rowProduct (transporterRows 17) aRows 111) (twRows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row18 :
    digitsEq 111 (rowProduct (transporterRows 18) aRows 111) (twRows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row19 :
    digitsEq 111 (rowProduct (transporterRows 19) aRows 111) (twRows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row20 :
    digitsEq 111 (rowProduct (transporterRows 20) aRows 111) (twRows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row21 :
    digitsEq 111 (rowProduct (transporterRows 21) aRows 111) (twRows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row22 :
    digitsEq 111 (rowProduct (transporterRows 22) aRows 111) (twRows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row23 :
    digitsEq 111 (rowProduct (transporterRows 23) aRows 111) (twRows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row24 :
    digitsEq 111 (rowProduct (transporterRows 24) aRows 111) (twRows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row25 :
    digitsEq 111 (rowProduct (transporterRows 25) aRows 111) (twRows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row26 :
    digitsEq 111 (rowProduct (transporterRows 26) aRows 111) (twRows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row27 :
    digitsEq 111 (rowProduct (transporterRows 27) aRows 111) (twRows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row28 :
    digitsEq 111 (rowProduct (transporterRows 28) aRows 111) (twRows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row29 :
    digitsEq 111 (rowProduct (transporterRows 29) aRows 111) (twRows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row30 :
    digitsEq 111 (rowProduct (transporterRows 30) aRows 111) (twRows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row31 :
    digitsEq 111 (rowProduct (transporterRows 31) aRows 111) (twRows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row32 :
    digitsEq 111 (rowProduct (transporterRows 32) aRows 111) (twRows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row33 :
    digitsEq 111 (rowProduct (transporterRows 33) aRows 111) (twRows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row34 :
    digitsEq 111 (rowProduct (transporterRows 34) aRows 111) (twRows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row35 :
    digitsEq 111 (rowProduct (transporterRows 35) aRows 111) (twRows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row36 :
    digitsEq 111 (rowProduct (transporterRows 36) aRows 111) (twRows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row37 :
    digitsEq 111 (rowProduct (transporterRows 37) aRows 111) (twRows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row38 :
    digitsEq 111 (rowProduct (transporterRows 38) aRows 111) (twRows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row39 :
    digitsEq 111 (rowProduct (transporterRows 39) aRows 111) (twRows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row40 :
    digitsEq 111 (rowProduct (transporterRows 40) aRows 111) (twRows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row41 :
    digitsEq 111 (rowProduct (transporterRows 41) aRows 111) (twRows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row42 :
    digitsEq 111 (rowProduct (transporterRows 42) aRows 111) (twRows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row43 :
    digitsEq 111 (rowProduct (transporterRows 43) aRows 111) (twRows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row44 :
    digitsEq 111 (rowProduct (transporterRows 44) aRows 111) (twRows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row45 :
    digitsEq 111 (rowProduct (transporterRows 45) aRows 111) (twRows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row46 :
    digitsEq 111 (rowProduct (transporterRows 46) aRows 111) (twRows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row47 :
    digitsEq 111 (rowProduct (transporterRows 47) aRows 111) (twRows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row48 :
    digitsEq 111 (rowProduct (transporterRows 48) aRows 111) (twRows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row49 :
    digitsEq 111 (rowProduct (transporterRows 49) aRows 111) (twRows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row50 :
    digitsEq 111 (rowProduct (transporterRows 50) aRows 111) (twRows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row51 :
    digitsEq 111 (rowProduct (transporterRows 51) aRows 111) (twRows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row52 :
    digitsEq 111 (rowProduct (transporterRows 52) aRows 111) (twRows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row53 :
    digitsEq 111 (rowProduct (transporterRows 53) aRows 111) (twRows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row54 :
    digitsEq 111 (rowProduct (transporterRows 54) aRows 111) (twRows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row55 :
    digitsEq 111 (rowProduct (transporterRows 55) aRows 111) (twRows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row56 :
    digitsEq 111 (rowProduct (transporterRows 56) aRows 111) (twRows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row57 :
    digitsEq 111 (rowProduct (transporterRows 57) aRows 111) (twRows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row58 :
    digitsEq 111 (rowProduct (transporterRows 58) aRows 111) (twRows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row59 :
    digitsEq 111 (rowProduct (transporterRows 59) aRows 111) (twRows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row60 :
    digitsEq 111 (rowProduct (transporterRows 60) aRows 111) (twRows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row61 :
    digitsEq 111 (rowProduct (transporterRows 61) aRows 111) (twRows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row62 :
    digitsEq 111 (rowProduct (transporterRows 62) aRows 111) (twRows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row63 :
    digitsEq 111 (rowProduct (transporterRows 63) aRows 111) (twRows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row64 :
    digitsEq 111 (rowProduct (transporterRows 64) aRows 111) (twRows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row65 :
    digitsEq 111 (rowProduct (transporterRows 65) aRows 111) (twRows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row66 :
    digitsEq 111 (rowProduct (transporterRows 66) aRows 111) (twRows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row67 :
    digitsEq 111 (rowProduct (transporterRows 67) aRows 111) (twRows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row68 :
    digitsEq 111 (rowProduct (transporterRows 68) aRows 111) (twRows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row69 :
    digitsEq 111 (rowProduct (transporterRows 69) aRows 111) (twRows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row70 :
    digitsEq 111 (rowProduct (transporterRows 70) aRows 111) (twRows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row71 :
    digitsEq 111 (rowProduct (transporterRows 71) aRows 111) (twRows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row72 :
    digitsEq 111 (rowProduct (transporterRows 72) aRows 111) (twRows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row73 :
    digitsEq 111 (rowProduct (transporterRows 73) aRows 111) (twRows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row74 :
    digitsEq 111 (rowProduct (transporterRows 74) aRows 111) (twRows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row75 :
    digitsEq 111 (rowProduct (transporterRows 75) aRows 111) (twRows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row76 :
    digitsEq 111 (rowProduct (transporterRows 76) aRows 111) (twRows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row77 :
    digitsEq 111 (rowProduct (transporterRows 77) aRows 111) (twRows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row78 :
    digitsEq 111 (rowProduct (transporterRows 78) aRows 111) (twRows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row79 :
    digitsEq 111 (rowProduct (transporterRows 79) aRows 111) (twRows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row80 :
    digitsEq 111 (rowProduct (transporterRows 80) aRows 111) (twRows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row81 :
    digitsEq 111 (rowProduct (transporterRows 81) aRows 111) (twRows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row82 :
    digitsEq 111 (rowProduct (transporterRows 82) aRows 111) (twRows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row83 :
    digitsEq 111 (rowProduct (transporterRows 83) aRows 111) (twRows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row84 :
    digitsEq 111 (rowProduct (transporterRows 84) aRows 111) (twRows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row85 :
    digitsEq 111 (rowProduct (transporterRows 85) aRows 111) (twRows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row86 :
    digitsEq 111 (rowProduct (transporterRows 86) aRows 111) (twRows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row87 :
    digitsEq 111 (rowProduct (transporterRows 87) aRows 111) (twRows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row88 :
    digitsEq 111 (rowProduct (transporterRows 88) aRows 111) (twRows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row89 :
    digitsEq 111 (rowProduct (transporterRows 89) aRows 111) (twRows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row90 :
    digitsEq 111 (rowProduct (transporterRows 90) aRows 111) (twRows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row91 :
    digitsEq 111 (rowProduct (transporterRows 91) aRows 111) (twRows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row92 :
    digitsEq 111 (rowProduct (transporterRows 92) aRows 111) (twRows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row93 :
    digitsEq 111 (rowProduct (transporterRows 93) aRows 111) (twRows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row94 :
    digitsEq 111 (rowProduct (transporterRows 94) aRows 111) (twRows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row95 :
    digitsEq 111 (rowProduct (transporterRows 95) aRows 111) (twRows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row96 :
    digitsEq 111 (rowProduct (transporterRows 96) aRows 111) (twRows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row97 :
    digitsEq 111 (rowProduct (transporterRows 97) aRows 111) (twRows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row98 :
    digitsEq 111 (rowProduct (transporterRows 98) aRows 111) (twRows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row99 :
    digitsEq 111 (rowProduct (transporterRows 99) aRows 111) (twRows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row100 :
    digitsEq 111 (rowProduct (transporterRows 100) aRows 111) (twRows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row101 :
    digitsEq 111 (rowProduct (transporterRows 101) aRows 111) (twRows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row102 :
    digitsEq 111 (rowProduct (transporterRows 102) aRows 111) (twRows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row103 :
    digitsEq 111 (rowProduct (transporterRows 103) aRows 111) (twRows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row104 :
    digitsEq 111 (rowProduct (transporterRows 104) aRows 111) (twRows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row105 :
    digitsEq 111 (rowProduct (transporterRows 105) aRows 111) (twRows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row106 :
    digitsEq 111 (rowProduct (transporterRows 106) aRows 111) (twRows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row107 :
    digitsEq 111 (rowProduct (transporterRows 107) aRows 111) (twRows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row108 :
    digitsEq 111 (rowProduct (transporterRows 108) aRows 111) (twRows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row109 :
    digitsEq 111 (rowProduct (transporterRows 109) aRows 111) (twRows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem wa_row110 :
    digitsEq 111 (rowProduct (transporterRows 110) aRows 111) (twRows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem wa_rows : ∀ i,
    digitsEq 111 (rowProduct (transporterRows i) aRows 111) (twRows i) = true :=
  (Fin.cases wa_row0
    (Fin.cases wa_row1
    (Fin.cases wa_row2
    (Fin.cases wa_row3
    (Fin.cases wa_row4
    (Fin.cases wa_row5
    (Fin.cases wa_row6
    (Fin.cases wa_row7
    (Fin.cases wa_row8
    (Fin.cases wa_row9
    (Fin.cases wa_row10
    (Fin.cases wa_row11
    (Fin.cases wa_row12
    (Fin.cases wa_row13
    (Fin.cases wa_row14
    (Fin.cases wa_row15
    (Fin.cases wa_row16
    (Fin.cases wa_row17
    (Fin.cases wa_row18
    (Fin.cases wa_row19
    (Fin.cases wa_row20
    (Fin.cases wa_row21
    (Fin.cases wa_row22
    (Fin.cases wa_row23
    (Fin.cases wa_row24
    (Fin.cases wa_row25
    (Fin.cases wa_row26
    (Fin.cases wa_row27
    (Fin.cases wa_row28
    (Fin.cases wa_row29
    (Fin.cases wa_row30
    (Fin.cases wa_row31
    (Fin.cases wa_row32
    (Fin.cases wa_row33
    (Fin.cases wa_row34
    (Fin.cases wa_row35
    (Fin.cases wa_row36
    (Fin.cases wa_row37
    (Fin.cases wa_row38
    (Fin.cases wa_row39
    (Fin.cases wa_row40
    (Fin.cases wa_row41
    (Fin.cases wa_row42
    (Fin.cases wa_row43
    (Fin.cases wa_row44
    (Fin.cases wa_row45
    (Fin.cases wa_row46
    (Fin.cases wa_row47
    (Fin.cases wa_row48
    (Fin.cases wa_row49
    (Fin.cases wa_row50
    (Fin.cases wa_row51
    (Fin.cases wa_row52
    (Fin.cases wa_row53
    (Fin.cases wa_row54
    (Fin.cases wa_row55
    (Fin.cases wa_row56
    (Fin.cases wa_row57
    (Fin.cases wa_row58
    (Fin.cases wa_row59
    (Fin.cases wa_row60
    (Fin.cases wa_row61
    (Fin.cases wa_row62
    (Fin.cases wa_row63
    (Fin.cases wa_row64
    (Fin.cases wa_row65
    (Fin.cases wa_row66
    (Fin.cases wa_row67
    (Fin.cases wa_row68
    (Fin.cases wa_row69
    (Fin.cases wa_row70
    (Fin.cases wa_row71
    (Fin.cases wa_row72
    (Fin.cases wa_row73
    (Fin.cases wa_row74
    (Fin.cases wa_row75
    (Fin.cases wa_row76
    (Fin.cases wa_row77
    (Fin.cases wa_row78
    (Fin.cases wa_row79
    (Fin.cases wa_row80
    (Fin.cases wa_row81
    (Fin.cases wa_row82
    (Fin.cases wa_row83
    (Fin.cases wa_row84
    (Fin.cases wa_row85
    (Fin.cases wa_row86
    (Fin.cases wa_row87
    (Fin.cases wa_row88
    (Fin.cases wa_row89
    (Fin.cases wa_row90
    (Fin.cases wa_row91
    (Fin.cases wa_row92
    (Fin.cases wa_row93
    (Fin.cases wa_row94
    (Fin.cases wa_row95
    (Fin.cases wa_row96
    (Fin.cases wa_row97
    (Fin.cases wa_row98
    (Fin.cases wa_row99
    (Fin.cases wa_row100
    (Fin.cases wa_row101
    (Fin.cases wa_row102
    (Fin.cases wa_row103
    (Fin.cases wa_row104
    (Fin.cases wa_row105
    (Fin.cases wa_row106
    (Fin.cases wa_row107
    (Fin.cases wa_row108
    (Fin.cases wa_row109
    (Fin.cases wa_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_wa : transporterMatrix * aMatrix = twMatrix :=
  decode_mul _ _ _ transporter_small a_small wa_rows

end Lyons.Atlas111InvolutionWords
