module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Cyclic.Data
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Reduction

/-!
# Checked orbit column edges

The first column is the seed; each later column is selected from AQ or BQ
using exactly the parent index of the binary word recurrence.

Source: the literal ATLAS local words and matrices; attribution in
`Atlas111Source/` and `Atlas111InvolutionSource/`. Reproduce these candidates
with `Cyclic/source/Generate.py`. All numerical checks use the Lean kernel.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Cyclic

open Atlas111WordCertificate
open Words

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seed_digits :
    ∀ i : Fin 111, digit (qRows i) 0 = if i = 0 then 1 else 0 := by
  decide +kernel

public theorem seed_column : (fun i => qMatrix i 0) = localSeed := by
  funext i
  change (digit (qRows i) 0 : ZMod 5) = _
  rw [seed_digits]
  simp [localSeed, Pi.single_apply]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row0 : ∀ j : Fin 110,
    digit (qRows 0) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 0 else bqRows 0) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row1 : ∀ j : Fin 110,
    digit (qRows 1) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 1 else bqRows 1) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row2 : ∀ j : Fin 110,
    digit (qRows 2) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 2 else bqRows 2) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row3 : ∀ j : Fin 110,
    digit (qRows 3) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 3 else bqRows 3) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row4 : ∀ j : Fin 110,
    digit (qRows 4) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 4 else bqRows 4) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row5 : ∀ j : Fin 110,
    digit (qRows 5) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 5 else bqRows 5) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row6 : ∀ j : Fin 110,
    digit (qRows 6) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 6 else bqRows 6) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row7 : ∀ j : Fin 110,
    digit (qRows 7) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 7 else bqRows 7) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row8 : ∀ j : Fin 110,
    digit (qRows 8) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 8 else bqRows 8) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row9 : ∀ j : Fin 110,
    digit (qRows 9) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 9 else bqRows 9) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row10 : ∀ j : Fin 110,
    digit (qRows 10) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 10 else bqRows 10) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row11 : ∀ j : Fin 110,
    digit (qRows 11) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 11 else bqRows 11) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row12 : ∀ j : Fin 110,
    digit (qRows 12) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 12 else bqRows 12) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row13 : ∀ j : Fin 110,
    digit (qRows 13) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 13 else bqRows 13) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row14 : ∀ j : Fin 110,
    digit (qRows 14) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 14 else bqRows 14) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row15 : ∀ j : Fin 110,
    digit (qRows 15) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 15 else bqRows 15) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row16 : ∀ j : Fin 110,
    digit (qRows 16) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 16 else bqRows 16) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row17 : ∀ j : Fin 110,
    digit (qRows 17) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 17 else bqRows 17) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row18 : ∀ j : Fin 110,
    digit (qRows 18) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 18 else bqRows 18) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row19 : ∀ j : Fin 110,
    digit (qRows 19) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 19 else bqRows 19) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row20 : ∀ j : Fin 110,
    digit (qRows 20) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 20 else bqRows 20) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row21 : ∀ j : Fin 110,
    digit (qRows 21) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 21 else bqRows 21) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row22 : ∀ j : Fin 110,
    digit (qRows 22) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 22 else bqRows 22) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row23 : ∀ j : Fin 110,
    digit (qRows 23) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 23 else bqRows 23) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row24 : ∀ j : Fin 110,
    digit (qRows 24) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 24 else bqRows 24) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row25 : ∀ j : Fin 110,
    digit (qRows 25) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 25 else bqRows 25) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row26 : ∀ j : Fin 110,
    digit (qRows 26) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 26 else bqRows 26) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row27 : ∀ j : Fin 110,
    digit (qRows 27) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 27 else bqRows 27) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row28 : ∀ j : Fin 110,
    digit (qRows 28) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 28 else bqRows 28) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row29 : ∀ j : Fin 110,
    digit (qRows 29) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 29 else bqRows 29) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row30 : ∀ j : Fin 110,
    digit (qRows 30) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 30 else bqRows 30) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row31 : ∀ j : Fin 110,
    digit (qRows 31) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 31 else bqRows 31) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row32 : ∀ j : Fin 110,
    digit (qRows 32) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 32 else bqRows 32) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row33 : ∀ j : Fin 110,
    digit (qRows 33) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 33 else bqRows 33) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row34 : ∀ j : Fin 110,
    digit (qRows 34) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 34 else bqRows 34) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row35 : ∀ j : Fin 110,
    digit (qRows 35) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 35 else bqRows 35) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row36 : ∀ j : Fin 110,
    digit (qRows 36) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 36 else bqRows 36) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row37 : ∀ j : Fin 110,
    digit (qRows 37) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 37 else bqRows 37) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row38 : ∀ j : Fin 110,
    digit (qRows 38) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 38 else bqRows 38) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row39 : ∀ j : Fin 110,
    digit (qRows 39) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 39 else bqRows 39) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row40 : ∀ j : Fin 110,
    digit (qRows 40) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 40 else bqRows 40) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row41 : ∀ j : Fin 110,
    digit (qRows 41) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 41 else bqRows 41) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row42 : ∀ j : Fin 110,
    digit (qRows 42) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 42 else bqRows 42) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row43 : ∀ j : Fin 110,
    digit (qRows 43) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 43 else bqRows 43) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row44 : ∀ j : Fin 110,
    digit (qRows 44) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 44 else bqRows 44) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row45 : ∀ j : Fin 110,
    digit (qRows 45) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 45 else bqRows 45) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row46 : ∀ j : Fin 110,
    digit (qRows 46) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 46 else bqRows 46) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row47 : ∀ j : Fin 110,
    digit (qRows 47) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 47 else bqRows 47) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row48 : ∀ j : Fin 110,
    digit (qRows 48) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 48 else bqRows 48) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row49 : ∀ j : Fin 110,
    digit (qRows 49) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 49 else bqRows 49) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row50 : ∀ j : Fin 110,
    digit (qRows 50) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 50 else bqRows 50) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row51 : ∀ j : Fin 110,
    digit (qRows 51) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 51 else bqRows 51) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row52 : ∀ j : Fin 110,
    digit (qRows 52) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 52 else bqRows 52) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row53 : ∀ j : Fin 110,
    digit (qRows 53) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 53 else bqRows 53) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row54 : ∀ j : Fin 110,
    digit (qRows 54) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 54 else bqRows 54) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row55 : ∀ j : Fin 110,
    digit (qRows 55) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 55 else bqRows 55) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row56 : ∀ j : Fin 110,
    digit (qRows 56) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 56 else bqRows 56) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row57 : ∀ j : Fin 110,
    digit (qRows 57) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 57 else bqRows 57) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row58 : ∀ j : Fin 110,
    digit (qRows 58) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 58 else bqRows 58) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row59 : ∀ j : Fin 110,
    digit (qRows 59) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 59 else bqRows 59) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row60 : ∀ j : Fin 110,
    digit (qRows 60) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 60 else bqRows 60) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row61 : ∀ j : Fin 110,
    digit (qRows 61) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 61 else bqRows 61) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row62 : ∀ j : Fin 110,
    digit (qRows 62) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 62 else bqRows 62) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row63 : ∀ j : Fin 110,
    digit (qRows 63) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 63 else bqRows 63) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row64 : ∀ j : Fin 110,
    digit (qRows 64) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 64 else bqRows 64) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row65 : ∀ j : Fin 110,
    digit (qRows 65) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 65 else bqRows 65) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row66 : ∀ j : Fin 110,
    digit (qRows 66) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 66 else bqRows 66) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row67 : ∀ j : Fin 110,
    digit (qRows 67) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 67 else bqRows 67) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row68 : ∀ j : Fin 110,
    digit (qRows 68) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 68 else bqRows 68) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row69 : ∀ j : Fin 110,
    digit (qRows 69) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 69 else bqRows 69) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row70 : ∀ j : Fin 110,
    digit (qRows 70) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 70 else bqRows 70) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row71 : ∀ j : Fin 110,
    digit (qRows 71) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 71 else bqRows 71) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row72 : ∀ j : Fin 110,
    digit (qRows 72) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 72 else bqRows 72) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row73 : ∀ j : Fin 110,
    digit (qRows 73) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 73 else bqRows 73) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row74 : ∀ j : Fin 110,
    digit (qRows 74) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 74 else bqRows 74) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row75 : ∀ j : Fin 110,
    digit (qRows 75) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 75 else bqRows 75) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row76 : ∀ j : Fin 110,
    digit (qRows 76) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 76 else bqRows 76) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row77 : ∀ j : Fin 110,
    digit (qRows 77) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 77 else bqRows 77) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row78 : ∀ j : Fin 110,
    digit (qRows 78) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 78 else bqRows 78) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row79 : ∀ j : Fin 110,
    digit (qRows 79) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 79 else bqRows 79) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row80 : ∀ j : Fin 110,
    digit (qRows 80) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 80 else bqRows 80) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row81 : ∀ j : Fin 110,
    digit (qRows 81) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 81 else bqRows 81) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row82 : ∀ j : Fin 110,
    digit (qRows 82) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 82 else bqRows 82) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row83 : ∀ j : Fin 110,
    digit (qRows 83) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 83 else bqRows 83) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row84 : ∀ j : Fin 110,
    digit (qRows 84) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 84 else bqRows 84) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row85 : ∀ j : Fin 110,
    digit (qRows 85) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 85 else bqRows 85) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row86 : ∀ j : Fin 110,
    digit (qRows 86) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 86 else bqRows 86) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row87 : ∀ j : Fin 110,
    digit (qRows 87) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 87 else bqRows 87) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row88 : ∀ j : Fin 110,
    digit (qRows 88) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 88 else bqRows 88) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row89 : ∀ j : Fin 110,
    digit (qRows 89) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 89 else bqRows 89) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row90 : ∀ j : Fin 110,
    digit (qRows 90) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 90 else bqRows 90) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row91 : ∀ j : Fin 110,
    digit (qRows 91) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 91 else bqRows 91) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row92 : ∀ j : Fin 110,
    digit (qRows 92) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 92 else bqRows 92) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row93 : ∀ j : Fin 110,
    digit (qRows 93) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 93 else bqRows 93) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row94 : ∀ j : Fin 110,
    digit (qRows 94) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 94 else bqRows 94) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row95 : ∀ j : Fin 110,
    digit (qRows 95) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 95 else bqRows 95) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row96 : ∀ j : Fin 110,
    digit (qRows 96) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 96 else bqRows 96) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row97 : ∀ j : Fin 110,
    digit (qRows 97) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 97 else bqRows 97) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row98 : ∀ j : Fin 110,
    digit (qRows 98) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 98 else bqRows 98) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row99 : ∀ j : Fin 110,
    digit (qRows 99) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 99 else bqRows 99) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row100 : ∀ j : Fin 110,
    digit (qRows 100) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 100 else bqRows 100) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row101 : ∀ j : Fin 110,
    digit (qRows 101) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 101 else bqRows 101) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row102 : ∀ j : Fin 110,
    digit (qRows 102) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 102 else bqRows 102) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row103 : ∀ j : Fin 110,
    digit (qRows 103) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 103 else bqRows 103) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row104 : ∀ j : Fin 110,
    digit (qRows 104) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 104 else bqRows 104) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row105 : ∀ j : Fin 110,
    digit (qRows 105) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 105 else bqRows 105) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row106 : ∀ j : Fin 110,
    digit (qRows 106) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 106 else bqRows 106) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row107 : ∀ j : Fin 110,
    digit (qRows 107) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 107 else bqRows 107) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row108 : ∀ j : Fin 110,
    digit (qRows 108) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 108 else bqRows 108) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row109 : ∀ j : Fin 110,
    digit (qRows 109) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 109 else bqRows 109) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem edge_row110 : ∀ j : Fin 110,
    digit (qRows 110) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows 110 else bqRows 110) (j.val / 2) := by
  decide +kernel

set_option maxRecDepth 10000 in
public theorem edge_digits : ∀ (i : Fin 111) (j : Fin 110),
    digit (qRows i) (j.val + 1) =
      digit (if j.val % 2 = 0 then aqRows i else bqRows i) (j.val / 2) :=
  (Fin.cases edge_row0
    (Fin.cases edge_row1
    (Fin.cases edge_row2
    (Fin.cases edge_row3
    (Fin.cases edge_row4
    (Fin.cases edge_row5
    (Fin.cases edge_row6
    (Fin.cases edge_row7
    (Fin.cases edge_row8
    (Fin.cases edge_row9
    (Fin.cases edge_row10
    (Fin.cases edge_row11
    (Fin.cases edge_row12
    (Fin.cases edge_row13
    (Fin.cases edge_row14
    (Fin.cases edge_row15
    (Fin.cases edge_row16
    (Fin.cases edge_row17
    (Fin.cases edge_row18
    (Fin.cases edge_row19
    (Fin.cases edge_row20
    (Fin.cases edge_row21
    (Fin.cases edge_row22
    (Fin.cases edge_row23
    (Fin.cases edge_row24
    (Fin.cases edge_row25
    (Fin.cases edge_row26
    (Fin.cases edge_row27
    (Fin.cases edge_row28
    (Fin.cases edge_row29
    (Fin.cases edge_row30
    (Fin.cases edge_row31
    (Fin.cases edge_row32
    (Fin.cases edge_row33
    (Fin.cases edge_row34
    (Fin.cases edge_row35
    (Fin.cases edge_row36
    (Fin.cases edge_row37
    (Fin.cases edge_row38
    (Fin.cases edge_row39
    (Fin.cases edge_row40
    (Fin.cases edge_row41
    (Fin.cases edge_row42
    (Fin.cases edge_row43
    (Fin.cases edge_row44
    (Fin.cases edge_row45
    (Fin.cases edge_row46
    (Fin.cases edge_row47
    (Fin.cases edge_row48
    (Fin.cases edge_row49
    (Fin.cases edge_row50
    (Fin.cases edge_row51
    (Fin.cases edge_row52
    (Fin.cases edge_row53
    (Fin.cases edge_row54
    (Fin.cases edge_row55
    (Fin.cases edge_row56
    (Fin.cases edge_row57
    (Fin.cases edge_row58
    (Fin.cases edge_row59
    (Fin.cases edge_row60
    (Fin.cases edge_row61
    (Fin.cases edge_row62
    (Fin.cases edge_row63
    (Fin.cases edge_row64
    (Fin.cases edge_row65
    (Fin.cases edge_row66
    (Fin.cases edge_row67
    (Fin.cases edge_row68
    (Fin.cases edge_row69
    (Fin.cases edge_row70
    (Fin.cases edge_row71
    (Fin.cases edge_row72
    (Fin.cases edge_row73
    (Fin.cases edge_row74
    (Fin.cases edge_row75
    (Fin.cases edge_row76
    (Fin.cases edge_row77
    (Fin.cases edge_row78
    (Fin.cases edge_row79
    (Fin.cases edge_row80
    (Fin.cases edge_row81
    (Fin.cases edge_row82
    (Fin.cases edge_row83
    (Fin.cases edge_row84
    (Fin.cases edge_row85
    (Fin.cases edge_row86
    (Fin.cases edge_row87
    (Fin.cases edge_row88
    (Fin.cases edge_row89
    (Fin.cases edge_row90
    (Fin.cases edge_row91
    (Fin.cases edge_row92
    (Fin.cases edge_row93
    (Fin.cases edge_row94
    (Fin.cases edge_row95
    (Fin.cases edge_row96
    (Fin.cases edge_row97
    (Fin.cases edge_row98
    (Fin.cases edge_row99
    (Fin.cases edge_row100
    (Fin.cases edge_row101
    (Fin.cases edge_row102
    (Fin.cases edge_row103
    (Fin.cases edge_row104
    (Fin.cases edge_row105
    (Fin.cases edge_row106
    (Fin.cases edge_row107
    (Fin.cases edge_row108
    (Fin.cases edge_row109
    (Fin.cases edge_row110
    (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Lyons.SimplicityCertificate.LocalCommutant.Cyclic
