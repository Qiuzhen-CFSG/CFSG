module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Words.Data

/-!
# Involution word multiplication: ab times b

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
private theorem r4_row0 :
    digitsEq 111 (rowProduct (abRows 0) bRows 111) (r4Rows 0)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row1 :
    digitsEq 111 (rowProduct (abRows 1) bRows 111) (r4Rows 1)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row2 :
    digitsEq 111 (rowProduct (abRows 2) bRows 111) (r4Rows 2)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row3 :
    digitsEq 111 (rowProduct (abRows 3) bRows 111) (r4Rows 3)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row4 :
    digitsEq 111 (rowProduct (abRows 4) bRows 111) (r4Rows 4)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row5 :
    digitsEq 111 (rowProduct (abRows 5) bRows 111) (r4Rows 5)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row6 :
    digitsEq 111 (rowProduct (abRows 6) bRows 111) (r4Rows 6)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row7 :
    digitsEq 111 (rowProduct (abRows 7) bRows 111) (r4Rows 7)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row8 :
    digitsEq 111 (rowProduct (abRows 8) bRows 111) (r4Rows 8)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row9 :
    digitsEq 111 (rowProduct (abRows 9) bRows 111) (r4Rows 9)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row10 :
    digitsEq 111 (rowProduct (abRows 10) bRows 111) (r4Rows 10)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row11 :
    digitsEq 111 (rowProduct (abRows 11) bRows 111) (r4Rows 11)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row12 :
    digitsEq 111 (rowProduct (abRows 12) bRows 111) (r4Rows 12)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row13 :
    digitsEq 111 (rowProduct (abRows 13) bRows 111) (r4Rows 13)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row14 :
    digitsEq 111 (rowProduct (abRows 14) bRows 111) (r4Rows 14)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row15 :
    digitsEq 111 (rowProduct (abRows 15) bRows 111) (r4Rows 15)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row16 :
    digitsEq 111 (rowProduct (abRows 16) bRows 111) (r4Rows 16)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row17 :
    digitsEq 111 (rowProduct (abRows 17) bRows 111) (r4Rows 17)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row18 :
    digitsEq 111 (rowProduct (abRows 18) bRows 111) (r4Rows 18)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row19 :
    digitsEq 111 (rowProduct (abRows 19) bRows 111) (r4Rows 19)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row20 :
    digitsEq 111 (rowProduct (abRows 20) bRows 111) (r4Rows 20)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row21 :
    digitsEq 111 (rowProduct (abRows 21) bRows 111) (r4Rows 21)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row22 :
    digitsEq 111 (rowProduct (abRows 22) bRows 111) (r4Rows 22)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row23 :
    digitsEq 111 (rowProduct (abRows 23) bRows 111) (r4Rows 23)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row24 :
    digitsEq 111 (rowProduct (abRows 24) bRows 111) (r4Rows 24)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row25 :
    digitsEq 111 (rowProduct (abRows 25) bRows 111) (r4Rows 25)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row26 :
    digitsEq 111 (rowProduct (abRows 26) bRows 111) (r4Rows 26)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row27 :
    digitsEq 111 (rowProduct (abRows 27) bRows 111) (r4Rows 27)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row28 :
    digitsEq 111 (rowProduct (abRows 28) bRows 111) (r4Rows 28)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row29 :
    digitsEq 111 (rowProduct (abRows 29) bRows 111) (r4Rows 29)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row30 :
    digitsEq 111 (rowProduct (abRows 30) bRows 111) (r4Rows 30)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row31 :
    digitsEq 111 (rowProduct (abRows 31) bRows 111) (r4Rows 31)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row32 :
    digitsEq 111 (rowProduct (abRows 32) bRows 111) (r4Rows 32)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row33 :
    digitsEq 111 (rowProduct (abRows 33) bRows 111) (r4Rows 33)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row34 :
    digitsEq 111 (rowProduct (abRows 34) bRows 111) (r4Rows 34)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row35 :
    digitsEq 111 (rowProduct (abRows 35) bRows 111) (r4Rows 35)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row36 :
    digitsEq 111 (rowProduct (abRows 36) bRows 111) (r4Rows 36)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row37 :
    digitsEq 111 (rowProduct (abRows 37) bRows 111) (r4Rows 37)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row38 :
    digitsEq 111 (rowProduct (abRows 38) bRows 111) (r4Rows 38)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row39 :
    digitsEq 111 (rowProduct (abRows 39) bRows 111) (r4Rows 39)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row40 :
    digitsEq 111 (rowProduct (abRows 40) bRows 111) (r4Rows 40)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row41 :
    digitsEq 111 (rowProduct (abRows 41) bRows 111) (r4Rows 41)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row42 :
    digitsEq 111 (rowProduct (abRows 42) bRows 111) (r4Rows 42)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row43 :
    digitsEq 111 (rowProduct (abRows 43) bRows 111) (r4Rows 43)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row44 :
    digitsEq 111 (rowProduct (abRows 44) bRows 111) (r4Rows 44)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row45 :
    digitsEq 111 (rowProduct (abRows 45) bRows 111) (r4Rows 45)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row46 :
    digitsEq 111 (rowProduct (abRows 46) bRows 111) (r4Rows 46)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row47 :
    digitsEq 111 (rowProduct (abRows 47) bRows 111) (r4Rows 47)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row48 :
    digitsEq 111 (rowProduct (abRows 48) bRows 111) (r4Rows 48)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row49 :
    digitsEq 111 (rowProduct (abRows 49) bRows 111) (r4Rows 49)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row50 :
    digitsEq 111 (rowProduct (abRows 50) bRows 111) (r4Rows 50)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row51 :
    digitsEq 111 (rowProduct (abRows 51) bRows 111) (r4Rows 51)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row52 :
    digitsEq 111 (rowProduct (abRows 52) bRows 111) (r4Rows 52)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row53 :
    digitsEq 111 (rowProduct (abRows 53) bRows 111) (r4Rows 53)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row54 :
    digitsEq 111 (rowProduct (abRows 54) bRows 111) (r4Rows 54)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row55 :
    digitsEq 111 (rowProduct (abRows 55) bRows 111) (r4Rows 55)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row56 :
    digitsEq 111 (rowProduct (abRows 56) bRows 111) (r4Rows 56)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row57 :
    digitsEq 111 (rowProduct (abRows 57) bRows 111) (r4Rows 57)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row58 :
    digitsEq 111 (rowProduct (abRows 58) bRows 111) (r4Rows 58)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row59 :
    digitsEq 111 (rowProduct (abRows 59) bRows 111) (r4Rows 59)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row60 :
    digitsEq 111 (rowProduct (abRows 60) bRows 111) (r4Rows 60)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row61 :
    digitsEq 111 (rowProduct (abRows 61) bRows 111) (r4Rows 61)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row62 :
    digitsEq 111 (rowProduct (abRows 62) bRows 111) (r4Rows 62)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row63 :
    digitsEq 111 (rowProduct (abRows 63) bRows 111) (r4Rows 63)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row64 :
    digitsEq 111 (rowProduct (abRows 64) bRows 111) (r4Rows 64)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row65 :
    digitsEq 111 (rowProduct (abRows 65) bRows 111) (r4Rows 65)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row66 :
    digitsEq 111 (rowProduct (abRows 66) bRows 111) (r4Rows 66)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row67 :
    digitsEq 111 (rowProduct (abRows 67) bRows 111) (r4Rows 67)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row68 :
    digitsEq 111 (rowProduct (abRows 68) bRows 111) (r4Rows 68)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row69 :
    digitsEq 111 (rowProduct (abRows 69) bRows 111) (r4Rows 69)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row70 :
    digitsEq 111 (rowProduct (abRows 70) bRows 111) (r4Rows 70)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row71 :
    digitsEq 111 (rowProduct (abRows 71) bRows 111) (r4Rows 71)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row72 :
    digitsEq 111 (rowProduct (abRows 72) bRows 111) (r4Rows 72)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row73 :
    digitsEq 111 (rowProduct (abRows 73) bRows 111) (r4Rows 73)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row74 :
    digitsEq 111 (rowProduct (abRows 74) bRows 111) (r4Rows 74)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row75 :
    digitsEq 111 (rowProduct (abRows 75) bRows 111) (r4Rows 75)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row76 :
    digitsEq 111 (rowProduct (abRows 76) bRows 111) (r4Rows 76)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row77 :
    digitsEq 111 (rowProduct (abRows 77) bRows 111) (r4Rows 77)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row78 :
    digitsEq 111 (rowProduct (abRows 78) bRows 111) (r4Rows 78)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row79 :
    digitsEq 111 (rowProduct (abRows 79) bRows 111) (r4Rows 79)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row80 :
    digitsEq 111 (rowProduct (abRows 80) bRows 111) (r4Rows 80)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row81 :
    digitsEq 111 (rowProduct (abRows 81) bRows 111) (r4Rows 81)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row82 :
    digitsEq 111 (rowProduct (abRows 82) bRows 111) (r4Rows 82)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row83 :
    digitsEq 111 (rowProduct (abRows 83) bRows 111) (r4Rows 83)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row84 :
    digitsEq 111 (rowProduct (abRows 84) bRows 111) (r4Rows 84)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row85 :
    digitsEq 111 (rowProduct (abRows 85) bRows 111) (r4Rows 85)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row86 :
    digitsEq 111 (rowProduct (abRows 86) bRows 111) (r4Rows 86)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row87 :
    digitsEq 111 (rowProduct (abRows 87) bRows 111) (r4Rows 87)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row88 :
    digitsEq 111 (rowProduct (abRows 88) bRows 111) (r4Rows 88)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row89 :
    digitsEq 111 (rowProduct (abRows 89) bRows 111) (r4Rows 89)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row90 :
    digitsEq 111 (rowProduct (abRows 90) bRows 111) (r4Rows 90)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row91 :
    digitsEq 111 (rowProduct (abRows 91) bRows 111) (r4Rows 91)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row92 :
    digitsEq 111 (rowProduct (abRows 92) bRows 111) (r4Rows 92)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row93 :
    digitsEq 111 (rowProduct (abRows 93) bRows 111) (r4Rows 93)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row94 :
    digitsEq 111 (rowProduct (abRows 94) bRows 111) (r4Rows 94)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row95 :
    digitsEq 111 (rowProduct (abRows 95) bRows 111) (r4Rows 95)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row96 :
    digitsEq 111 (rowProduct (abRows 96) bRows 111) (r4Rows 96)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row97 :
    digitsEq 111 (rowProduct (abRows 97) bRows 111) (r4Rows 97)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row98 :
    digitsEq 111 (rowProduct (abRows 98) bRows 111) (r4Rows 98)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row99 :
    digitsEq 111 (rowProduct (abRows 99) bRows 111) (r4Rows 99)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row100 :
    digitsEq 111 (rowProduct (abRows 100) bRows 111) (r4Rows 100)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row101 :
    digitsEq 111 (rowProduct (abRows 101) bRows 111) (r4Rows 101)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row102 :
    digitsEq 111 (rowProduct (abRows 102) bRows 111) (r4Rows 102)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row103 :
    digitsEq 111 (rowProduct (abRows 103) bRows 111) (r4Rows 103)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row104 :
    digitsEq 111 (rowProduct (abRows 104) bRows 111) (r4Rows 104)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row105 :
    digitsEq 111 (rowProduct (abRows 105) bRows 111) (r4Rows 105)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row106 :
    digitsEq 111 (rowProduct (abRows 106) bRows 111) (r4Rows 106)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row107 :
    digitsEq 111 (rowProduct (abRows 107) bRows 111) (r4Rows 107)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row108 :
    digitsEq 111 (rowProduct (abRows 108) bRows 111) (r4Rows 108)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row109 :
    digitsEq 111 (rowProduct (abRows 109) bRows 111) (r4Rows 109)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem r4_row110 :
    digitsEq 111 (rowProduct (abRows 110) bRows 111) (r4Rows 110)
      = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem r4_rows : ∀ i,
    digitsEq 111 (rowProduct (abRows i) bRows 111) (r4Rows i) = true :=
  (Fin.cases r4_row0
    (Fin.cases r4_row1
    (Fin.cases r4_row2
    (Fin.cases r4_row3
    (Fin.cases r4_row4
    (Fin.cases r4_row5
    (Fin.cases r4_row6
    (Fin.cases r4_row7
    (Fin.cases r4_row8
    (Fin.cases r4_row9
    (Fin.cases r4_row10
    (Fin.cases r4_row11
    (Fin.cases r4_row12
    (Fin.cases r4_row13
    (Fin.cases r4_row14
    (Fin.cases r4_row15
    (Fin.cases r4_row16
    (Fin.cases r4_row17
    (Fin.cases r4_row18
    (Fin.cases r4_row19
    (Fin.cases r4_row20
    (Fin.cases r4_row21
    (Fin.cases r4_row22
    (Fin.cases r4_row23
    (Fin.cases r4_row24
    (Fin.cases r4_row25
    (Fin.cases r4_row26
    (Fin.cases r4_row27
    (Fin.cases r4_row28
    (Fin.cases r4_row29
    (Fin.cases r4_row30
    (Fin.cases r4_row31
    (Fin.cases r4_row32
    (Fin.cases r4_row33
    (Fin.cases r4_row34
    (Fin.cases r4_row35
    (Fin.cases r4_row36
    (Fin.cases r4_row37
    (Fin.cases r4_row38
    (Fin.cases r4_row39
    (Fin.cases r4_row40
    (Fin.cases r4_row41
    (Fin.cases r4_row42
    (Fin.cases r4_row43
    (Fin.cases r4_row44
    (Fin.cases r4_row45
    (Fin.cases r4_row46
    (Fin.cases r4_row47
    (Fin.cases r4_row48
    (Fin.cases r4_row49
    (Fin.cases r4_row50
    (Fin.cases r4_row51
    (Fin.cases r4_row52
    (Fin.cases r4_row53
    (Fin.cases r4_row54
    (Fin.cases r4_row55
    (Fin.cases r4_row56
    (Fin.cases r4_row57
    (Fin.cases r4_row58
    (Fin.cases r4_row59
    (Fin.cases r4_row60
    (Fin.cases r4_row61
    (Fin.cases r4_row62
    (Fin.cases r4_row63
    (Fin.cases r4_row64
    (Fin.cases r4_row65
    (Fin.cases r4_row66
    (Fin.cases r4_row67
    (Fin.cases r4_row68
    (Fin.cases r4_row69
    (Fin.cases r4_row70
    (Fin.cases r4_row71
    (Fin.cases r4_row72
    (Fin.cases r4_row73
    (Fin.cases r4_row74
    (Fin.cases r4_row75
    (Fin.cases r4_row76
    (Fin.cases r4_row77
    (Fin.cases r4_row78
    (Fin.cases r4_row79
    (Fin.cases r4_row80
    (Fin.cases r4_row81
    (Fin.cases r4_row82
    (Fin.cases r4_row83
    (Fin.cases r4_row84
    (Fin.cases r4_row85
    (Fin.cases r4_row86
    (Fin.cases r4_row87
    (Fin.cases r4_row88
    (Fin.cases r4_row89
    (Fin.cases r4_row90
    (Fin.cases r4_row91
    (Fin.cases r4_row92
    (Fin.cases r4_row93
    (Fin.cases r4_row94
    (Fin.cases r4_row95
    (Fin.cases r4_row96
    (Fin.cases r4_row97
    (Fin.cases r4_row98
    (Fin.cases r4_row99
    (Fin.cases r4_row100
    (Fin.cases r4_row101
    (Fin.cases r4_row102
    (Fin.cases r4_row103
    (Fin.cases r4_row104
    (Fin.cases r4_row105
    (Fin.cases r4_row106
    (Fin.cases r4_row107
    (Fin.cases r4_row108
    (Fin.cases r4_row109
    (Fin.cases r4_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Kernel-checked multiplication in the actual matrix algebra. -/
public theorem mul_r4 : abMatrix * bMatrix = r4Matrix :=
  decode_mul _ _ _ ab_small b_small r4_rows

end Lyons.SimplicityCertificate.LocalCommutant.Words
