module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Polynomial.Family

/-!
# Subtraction for the annihilator polynomial

Entrywise finite-field subtraction identifies W₁₁₁ minus the weighted sum
with the packed annihilator. In characteristic five, subtraction adds four times.

Candidate generation and source attribution: `Kernel/source/GenerateKernel.py`
and `Kernel/source/README.md`. Every numerical assertion is checked in Lean.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Kernel

open Atlas111WordCertificate

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row0 :
    allRows (fun j => (digit (w111Rows 0) j.val + 4 * digit (sumRows 0) j.val) % 5 == digit (rRows 0) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row1 :
    allRows (fun j => (digit (w111Rows 1) j.val + 4 * digit (sumRows 1) j.val) % 5 == digit (rRows 1) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row2 :
    allRows (fun j => (digit (w111Rows 2) j.val + 4 * digit (sumRows 2) j.val) % 5 == digit (rRows 2) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row3 :
    allRows (fun j => (digit (w111Rows 3) j.val + 4 * digit (sumRows 3) j.val) % 5 == digit (rRows 3) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row4 :
    allRows (fun j => (digit (w111Rows 4) j.val + 4 * digit (sumRows 4) j.val) % 5 == digit (rRows 4) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row5 :
    allRows (fun j => (digit (w111Rows 5) j.val + 4 * digit (sumRows 5) j.val) % 5 == digit (rRows 5) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row6 :
    allRows (fun j => (digit (w111Rows 6) j.val + 4 * digit (sumRows 6) j.val) % 5 == digit (rRows 6) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row7 :
    allRows (fun j => (digit (w111Rows 7) j.val + 4 * digit (sumRows 7) j.val) % 5 == digit (rRows 7) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row8 :
    allRows (fun j => (digit (w111Rows 8) j.val + 4 * digit (sumRows 8) j.val) % 5 == digit (rRows 8) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row9 :
    allRows (fun j => (digit (w111Rows 9) j.val + 4 * digit (sumRows 9) j.val) % 5 == digit (rRows 9) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row10 :
    allRows (fun j => (digit (w111Rows 10) j.val + 4 * digit (sumRows 10) j.val) % 5 == digit (rRows 10) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row11 :
    allRows (fun j => (digit (w111Rows 11) j.val + 4 * digit (sumRows 11) j.val) % 5 == digit (rRows 11) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row12 :
    allRows (fun j => (digit (w111Rows 12) j.val + 4 * digit (sumRows 12) j.val) % 5 == digit (rRows 12) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row13 :
    allRows (fun j => (digit (w111Rows 13) j.val + 4 * digit (sumRows 13) j.val) % 5 == digit (rRows 13) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row14 :
    allRows (fun j => (digit (w111Rows 14) j.val + 4 * digit (sumRows 14) j.val) % 5 == digit (rRows 14) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row15 :
    allRows (fun j => (digit (w111Rows 15) j.val + 4 * digit (sumRows 15) j.val) % 5 == digit (rRows 15) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row16 :
    allRows (fun j => (digit (w111Rows 16) j.val + 4 * digit (sumRows 16) j.val) % 5 == digit (rRows 16) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row17 :
    allRows (fun j => (digit (w111Rows 17) j.val + 4 * digit (sumRows 17) j.val) % 5 == digit (rRows 17) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row18 :
    allRows (fun j => (digit (w111Rows 18) j.val + 4 * digit (sumRows 18) j.val) % 5 == digit (rRows 18) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row19 :
    allRows (fun j => (digit (w111Rows 19) j.val + 4 * digit (sumRows 19) j.val) % 5 == digit (rRows 19) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row20 :
    allRows (fun j => (digit (w111Rows 20) j.val + 4 * digit (sumRows 20) j.val) % 5 == digit (rRows 20) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row21 :
    allRows (fun j => (digit (w111Rows 21) j.val + 4 * digit (sumRows 21) j.val) % 5 == digit (rRows 21) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row22 :
    allRows (fun j => (digit (w111Rows 22) j.val + 4 * digit (sumRows 22) j.val) % 5 == digit (rRows 22) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row23 :
    allRows (fun j => (digit (w111Rows 23) j.val + 4 * digit (sumRows 23) j.val) % 5 == digit (rRows 23) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row24 :
    allRows (fun j => (digit (w111Rows 24) j.val + 4 * digit (sumRows 24) j.val) % 5 == digit (rRows 24) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row25 :
    allRows (fun j => (digit (w111Rows 25) j.val + 4 * digit (sumRows 25) j.val) % 5 == digit (rRows 25) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row26 :
    allRows (fun j => (digit (w111Rows 26) j.val + 4 * digit (sumRows 26) j.val) % 5 == digit (rRows 26) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row27 :
    allRows (fun j => (digit (w111Rows 27) j.val + 4 * digit (sumRows 27) j.val) % 5 == digit (rRows 27) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row28 :
    allRows (fun j => (digit (w111Rows 28) j.val + 4 * digit (sumRows 28) j.val) % 5 == digit (rRows 28) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row29 :
    allRows (fun j => (digit (w111Rows 29) j.val + 4 * digit (sumRows 29) j.val) % 5 == digit (rRows 29) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row30 :
    allRows (fun j => (digit (w111Rows 30) j.val + 4 * digit (sumRows 30) j.val) % 5 == digit (rRows 30) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row31 :
    allRows (fun j => (digit (w111Rows 31) j.val + 4 * digit (sumRows 31) j.val) % 5 == digit (rRows 31) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row32 :
    allRows (fun j => (digit (w111Rows 32) j.val + 4 * digit (sumRows 32) j.val) % 5 == digit (rRows 32) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row33 :
    allRows (fun j => (digit (w111Rows 33) j.val + 4 * digit (sumRows 33) j.val) % 5 == digit (rRows 33) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row34 :
    allRows (fun j => (digit (w111Rows 34) j.val + 4 * digit (sumRows 34) j.val) % 5 == digit (rRows 34) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row35 :
    allRows (fun j => (digit (w111Rows 35) j.val + 4 * digit (sumRows 35) j.val) % 5 == digit (rRows 35) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row36 :
    allRows (fun j => (digit (w111Rows 36) j.val + 4 * digit (sumRows 36) j.val) % 5 == digit (rRows 36) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row37 :
    allRows (fun j => (digit (w111Rows 37) j.val + 4 * digit (sumRows 37) j.val) % 5 == digit (rRows 37) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row38 :
    allRows (fun j => (digit (w111Rows 38) j.val + 4 * digit (sumRows 38) j.val) % 5 == digit (rRows 38) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row39 :
    allRows (fun j => (digit (w111Rows 39) j.val + 4 * digit (sumRows 39) j.val) % 5 == digit (rRows 39) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row40 :
    allRows (fun j => (digit (w111Rows 40) j.val + 4 * digit (sumRows 40) j.val) % 5 == digit (rRows 40) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row41 :
    allRows (fun j => (digit (w111Rows 41) j.val + 4 * digit (sumRows 41) j.val) % 5 == digit (rRows 41) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row42 :
    allRows (fun j => (digit (w111Rows 42) j.val + 4 * digit (sumRows 42) j.val) % 5 == digit (rRows 42) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row43 :
    allRows (fun j => (digit (w111Rows 43) j.val + 4 * digit (sumRows 43) j.val) % 5 == digit (rRows 43) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row44 :
    allRows (fun j => (digit (w111Rows 44) j.val + 4 * digit (sumRows 44) j.val) % 5 == digit (rRows 44) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row45 :
    allRows (fun j => (digit (w111Rows 45) j.val + 4 * digit (sumRows 45) j.val) % 5 == digit (rRows 45) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row46 :
    allRows (fun j => (digit (w111Rows 46) j.val + 4 * digit (sumRows 46) j.val) % 5 == digit (rRows 46) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row47 :
    allRows (fun j => (digit (w111Rows 47) j.val + 4 * digit (sumRows 47) j.val) % 5 == digit (rRows 47) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row48 :
    allRows (fun j => (digit (w111Rows 48) j.val + 4 * digit (sumRows 48) j.val) % 5 == digit (rRows 48) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row49 :
    allRows (fun j => (digit (w111Rows 49) j.val + 4 * digit (sumRows 49) j.val) % 5 == digit (rRows 49) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row50 :
    allRows (fun j => (digit (w111Rows 50) j.val + 4 * digit (sumRows 50) j.val) % 5 == digit (rRows 50) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row51 :
    allRows (fun j => (digit (w111Rows 51) j.val + 4 * digit (sumRows 51) j.val) % 5 == digit (rRows 51) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row52 :
    allRows (fun j => (digit (w111Rows 52) j.val + 4 * digit (sumRows 52) j.val) % 5 == digit (rRows 52) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row53 :
    allRows (fun j => (digit (w111Rows 53) j.val + 4 * digit (sumRows 53) j.val) % 5 == digit (rRows 53) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row54 :
    allRows (fun j => (digit (w111Rows 54) j.val + 4 * digit (sumRows 54) j.val) % 5 == digit (rRows 54) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row55 :
    allRows (fun j => (digit (w111Rows 55) j.val + 4 * digit (sumRows 55) j.val) % 5 == digit (rRows 55) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row56 :
    allRows (fun j => (digit (w111Rows 56) j.val + 4 * digit (sumRows 56) j.val) % 5 == digit (rRows 56) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row57 :
    allRows (fun j => (digit (w111Rows 57) j.val + 4 * digit (sumRows 57) j.val) % 5 == digit (rRows 57) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row58 :
    allRows (fun j => (digit (w111Rows 58) j.val + 4 * digit (sumRows 58) j.val) % 5 == digit (rRows 58) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row59 :
    allRows (fun j => (digit (w111Rows 59) j.val + 4 * digit (sumRows 59) j.val) % 5 == digit (rRows 59) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row60 :
    allRows (fun j => (digit (w111Rows 60) j.val + 4 * digit (sumRows 60) j.val) % 5 == digit (rRows 60) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row61 :
    allRows (fun j => (digit (w111Rows 61) j.val + 4 * digit (sumRows 61) j.val) % 5 == digit (rRows 61) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row62 :
    allRows (fun j => (digit (w111Rows 62) j.val + 4 * digit (sumRows 62) j.val) % 5 == digit (rRows 62) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row63 :
    allRows (fun j => (digit (w111Rows 63) j.val + 4 * digit (sumRows 63) j.val) % 5 == digit (rRows 63) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row64 :
    allRows (fun j => (digit (w111Rows 64) j.val + 4 * digit (sumRows 64) j.val) % 5 == digit (rRows 64) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row65 :
    allRows (fun j => (digit (w111Rows 65) j.val + 4 * digit (sumRows 65) j.val) % 5 == digit (rRows 65) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row66 :
    allRows (fun j => (digit (w111Rows 66) j.val + 4 * digit (sumRows 66) j.val) % 5 == digit (rRows 66) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row67 :
    allRows (fun j => (digit (w111Rows 67) j.val + 4 * digit (sumRows 67) j.val) % 5 == digit (rRows 67) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row68 :
    allRows (fun j => (digit (w111Rows 68) j.val + 4 * digit (sumRows 68) j.val) % 5 == digit (rRows 68) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row69 :
    allRows (fun j => (digit (w111Rows 69) j.val + 4 * digit (sumRows 69) j.val) % 5 == digit (rRows 69) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row70 :
    allRows (fun j => (digit (w111Rows 70) j.val + 4 * digit (sumRows 70) j.val) % 5 == digit (rRows 70) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row71 :
    allRows (fun j => (digit (w111Rows 71) j.val + 4 * digit (sumRows 71) j.val) % 5 == digit (rRows 71) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row72 :
    allRows (fun j => (digit (w111Rows 72) j.val + 4 * digit (sumRows 72) j.val) % 5 == digit (rRows 72) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row73 :
    allRows (fun j => (digit (w111Rows 73) j.val + 4 * digit (sumRows 73) j.val) % 5 == digit (rRows 73) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row74 :
    allRows (fun j => (digit (w111Rows 74) j.val + 4 * digit (sumRows 74) j.val) % 5 == digit (rRows 74) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row75 :
    allRows (fun j => (digit (w111Rows 75) j.val + 4 * digit (sumRows 75) j.val) % 5 == digit (rRows 75) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row76 :
    allRows (fun j => (digit (w111Rows 76) j.val + 4 * digit (sumRows 76) j.val) % 5 == digit (rRows 76) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row77 :
    allRows (fun j => (digit (w111Rows 77) j.val + 4 * digit (sumRows 77) j.val) % 5 == digit (rRows 77) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row78 :
    allRows (fun j => (digit (w111Rows 78) j.val + 4 * digit (sumRows 78) j.val) % 5 == digit (rRows 78) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row79 :
    allRows (fun j => (digit (w111Rows 79) j.val + 4 * digit (sumRows 79) j.val) % 5 == digit (rRows 79) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row80 :
    allRows (fun j => (digit (w111Rows 80) j.val + 4 * digit (sumRows 80) j.val) % 5 == digit (rRows 80) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row81 :
    allRows (fun j => (digit (w111Rows 81) j.val + 4 * digit (sumRows 81) j.val) % 5 == digit (rRows 81) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row82 :
    allRows (fun j => (digit (w111Rows 82) j.val + 4 * digit (sumRows 82) j.val) % 5 == digit (rRows 82) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row83 :
    allRows (fun j => (digit (w111Rows 83) j.val + 4 * digit (sumRows 83) j.val) % 5 == digit (rRows 83) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row84 :
    allRows (fun j => (digit (w111Rows 84) j.val + 4 * digit (sumRows 84) j.val) % 5 == digit (rRows 84) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row85 :
    allRows (fun j => (digit (w111Rows 85) j.val + 4 * digit (sumRows 85) j.val) % 5 == digit (rRows 85) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row86 :
    allRows (fun j => (digit (w111Rows 86) j.val + 4 * digit (sumRows 86) j.val) % 5 == digit (rRows 86) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row87 :
    allRows (fun j => (digit (w111Rows 87) j.val + 4 * digit (sumRows 87) j.val) % 5 == digit (rRows 87) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row88 :
    allRows (fun j => (digit (w111Rows 88) j.val + 4 * digit (sumRows 88) j.val) % 5 == digit (rRows 88) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row89 :
    allRows (fun j => (digit (w111Rows 89) j.val + 4 * digit (sumRows 89) j.val) % 5 == digit (rRows 89) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row90 :
    allRows (fun j => (digit (w111Rows 90) j.val + 4 * digit (sumRows 90) j.val) % 5 == digit (rRows 90) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row91 :
    allRows (fun j => (digit (w111Rows 91) j.val + 4 * digit (sumRows 91) j.val) % 5 == digit (rRows 91) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row92 :
    allRows (fun j => (digit (w111Rows 92) j.val + 4 * digit (sumRows 92) j.val) % 5 == digit (rRows 92) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row93 :
    allRows (fun j => (digit (w111Rows 93) j.val + 4 * digit (sumRows 93) j.val) % 5 == digit (rRows 93) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row94 :
    allRows (fun j => (digit (w111Rows 94) j.val + 4 * digit (sumRows 94) j.val) % 5 == digit (rRows 94) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row95 :
    allRows (fun j => (digit (w111Rows 95) j.val + 4 * digit (sumRows 95) j.val) % 5 == digit (rRows 95) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row96 :
    allRows (fun j => (digit (w111Rows 96) j.val + 4 * digit (sumRows 96) j.val) % 5 == digit (rRows 96) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row97 :
    allRows (fun j => (digit (w111Rows 97) j.val + 4 * digit (sumRows 97) j.val) % 5 == digit (rRows 97) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row98 :
    allRows (fun j => (digit (w111Rows 98) j.val + 4 * digit (sumRows 98) j.val) % 5 == digit (rRows 98) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row99 :
    allRows (fun j => (digit (w111Rows 99) j.val + 4 * digit (sumRows 99) j.val) % 5 == digit (rRows 99) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row100 :
    allRows (fun j => (digit (w111Rows 100) j.val + 4 * digit (sumRows 100) j.val) % 5 == digit (rRows 100) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row101 :
    allRows (fun j => (digit (w111Rows 101) j.val + 4 * digit (sumRows 101) j.val) % 5 == digit (rRows 101) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row102 :
    allRows (fun j => (digit (w111Rows 102) j.val + 4 * digit (sumRows 102) j.val) % 5 == digit (rRows 102) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row103 :
    allRows (fun j => (digit (w111Rows 103) j.val + 4 * digit (sumRows 103) j.val) % 5 == digit (rRows 103) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row104 :
    allRows (fun j => (digit (w111Rows 104) j.val + 4 * digit (sumRows 104) j.val) % 5 == digit (rRows 104) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row105 :
    allRows (fun j => (digit (w111Rows 105) j.val + 4 * digit (sumRows 105) j.val) % 5 == digit (rRows 105) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row106 :
    allRows (fun j => (digit (w111Rows 106) j.val + 4 * digit (sumRows 106) j.val) % 5 == digit (rRows 106) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row107 :
    allRows (fun j => (digit (w111Rows 107) j.val + 4 * digit (sumRows 107) j.val) % 5 == digit (rRows 107) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row108 :
    allRows (fun j => (digit (w111Rows 108) j.val + 4 * digit (sumRows 108) j.val) % 5 == digit (rRows 108) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row109 :
    allRows (fun j => (digit (w111Rows 109) j.val + 4 * digit (sumRows 109) j.val) % 5 == digit (rRows 109) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem subtract_row110 :
    allRows (fun j => (digit (w111Rows 110) j.val + 4 * digit (sumRows 110) j.val) % 5 == digit (rRows 110) j.val) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
public theorem subtract_rows : ∀ i : Fin 111,
    allRows (fun j => (digit (w111Rows i) j.val + 4 * digit (sumRows i) j.val) % 5 == digit (rRows i) j.val) = true :=
  (Fin.cases subtract_row0
    (Fin.cases subtract_row1
    (Fin.cases subtract_row2
    (Fin.cases subtract_row3
    (Fin.cases subtract_row4
    (Fin.cases subtract_row5
    (Fin.cases subtract_row6
    (Fin.cases subtract_row7
    (Fin.cases subtract_row8
    (Fin.cases subtract_row9
    (Fin.cases subtract_row10
    (Fin.cases subtract_row11
    (Fin.cases subtract_row12
    (Fin.cases subtract_row13
    (Fin.cases subtract_row14
    (Fin.cases subtract_row15
    (Fin.cases subtract_row16
    (Fin.cases subtract_row17
    (Fin.cases subtract_row18
    (Fin.cases subtract_row19
    (Fin.cases subtract_row20
    (Fin.cases subtract_row21
    (Fin.cases subtract_row22
    (Fin.cases subtract_row23
    (Fin.cases subtract_row24
    (Fin.cases subtract_row25
    (Fin.cases subtract_row26
    (Fin.cases subtract_row27
    (Fin.cases subtract_row28
    (Fin.cases subtract_row29
    (Fin.cases subtract_row30
    (Fin.cases subtract_row31
    (Fin.cases subtract_row32
    (Fin.cases subtract_row33
    (Fin.cases subtract_row34
    (Fin.cases subtract_row35
    (Fin.cases subtract_row36
    (Fin.cases subtract_row37
    (Fin.cases subtract_row38
    (Fin.cases subtract_row39
    (Fin.cases subtract_row40
    (Fin.cases subtract_row41
    (Fin.cases subtract_row42
    (Fin.cases subtract_row43
    (Fin.cases subtract_row44
    (Fin.cases subtract_row45
    (Fin.cases subtract_row46
    (Fin.cases subtract_row47
    (Fin.cases subtract_row48
    (Fin.cases subtract_row49
    (Fin.cases subtract_row50
    (Fin.cases subtract_row51
    (Fin.cases subtract_row52
    (Fin.cases subtract_row53
    (Fin.cases subtract_row54
    (Fin.cases subtract_row55
    (Fin.cases subtract_row56
    (Fin.cases subtract_row57
    (Fin.cases subtract_row58
    (Fin.cases subtract_row59
    (Fin.cases subtract_row60
    (Fin.cases subtract_row61
    (Fin.cases subtract_row62
    (Fin.cases subtract_row63
    (Fin.cases subtract_row64
    (Fin.cases subtract_row65
    (Fin.cases subtract_row66
    (Fin.cases subtract_row67
    (Fin.cases subtract_row68
    (Fin.cases subtract_row69
    (Fin.cases subtract_row70
    (Fin.cases subtract_row71
    (Fin.cases subtract_row72
    (Fin.cases subtract_row73
    (Fin.cases subtract_row74
    (Fin.cases subtract_row75
    (Fin.cases subtract_row76
    (Fin.cases subtract_row77
    (Fin.cases subtract_row78
    (Fin.cases subtract_row79
    (Fin.cases subtract_row80
    (Fin.cases subtract_row81
    (Fin.cases subtract_row82
    (Fin.cases subtract_row83
    (Fin.cases subtract_row84
    (Fin.cases subtract_row85
    (Fin.cases subtract_row86
    (Fin.cases subtract_row87
    (Fin.cases subtract_row88
    (Fin.cases subtract_row89
    (Fin.cases subtract_row90
    (Fin.cases subtract_row91
    (Fin.cases subtract_row92
    (Fin.cases subtract_row93
    (Fin.cases subtract_row94
    (Fin.cases subtract_row95
    (Fin.cases subtract_row96
    (Fin.cases subtract_row97
    (Fin.cases subtract_row98
    (Fin.cases subtract_row99
    (Fin.cases subtract_row100
    (Fin.cases subtract_row101
    (Fin.cases subtract_row102
    (Fin.cases subtract_row103
    (Fin.cases subtract_row104
    (Fin.cases subtract_row105
    (Fin.cases subtract_row106
    (Fin.cases subtract_row107
    (Fin.cases subtract_row108
    (Fin.cases subtract_row109
    (Fin.cases subtract_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Lyons.SimplicityCertificate.LocalCommutant.Kernel
