module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Rows

/-!
# Kernel-checked products for ambient J4 fusion, part 15

All arithmetic is checked by Lean's kernel; the external search is not trusted.
`decode_packedMul` supplies the interpretation as binary matrix multiplication.
-/

@[expose] public section
namespace Janko4.Simplicity.ThreeFusion
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem p560 : packedMul r478 q479_2 = q479_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p561 : packedMul q479_2 q479_3 = r479 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p562 : packedMul r474 r479 = r480 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p563 : packedMul r1 r2 = r481 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p564 : packedMul r481 r43 = r482 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p565 : packedMul r482 r43 = r483 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p566 : packedMul r483 r1 = r484 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p567 : packedMul r484 r1 = r485 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p568 : packedMul r485 r1 = r486 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p569 : packedMul r486 r0 = r487 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p570 : packedMul r487 r1 = r488 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p571 : packedMul r488 r43 = r489 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p572 : packedMul r489 r55 = r490 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p573 : packedMul r490 r43 = r491 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p574 : packedMul r491 r43 = r492 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p575 : packedMul r492 r55 = r493 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p576 : packedMul r493 r2 = r494 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p577 : packedMul r494 r495 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p578 : packedMul r495 r52 = r496 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p579 : packedMul r496 r494 = r497 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p580 : packedMul r52 r497 = r498 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p581 : packedMul r498 r498 = q499_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p582 : packedMul r498 q499_2 = q499_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p583 : packedMul q499_3 q499_3 = r499 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p584 : packedMul r415 r0 = r500 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p585 : packedMul r500 r1 = r501 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p586 : packedMul r501 r2 = r502 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p587 : packedMul r502 r1 = r503 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p588 : packedMul r503 r2 = r504 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p589 : packedMul r504 r55 = r505 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p590 : packedMul r505 r1 = r506 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p591 : packedMul r506 r55 = r507 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p592 : packedMul r507 r508 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p593 : packedMul r508 r52 = r509 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p594 : packedMul r509 r507 = r510 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p595 : packedMul r52 r510 = r511 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p596 : packedMul r511 r511 = q512_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p597 : packedMul r511 q512_2 = q512_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p598 : packedMul q512_3 q512_3 = r512 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p599 : packedMul r93 r55 = r513 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)


end Janko4.Simplicity.ThreeFusion
