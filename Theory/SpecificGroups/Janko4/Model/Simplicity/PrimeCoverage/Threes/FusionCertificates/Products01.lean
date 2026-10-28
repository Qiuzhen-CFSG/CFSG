module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Rows

/-!
# Kernel-checked products for ambient J4 fusion, part 2

All arithmetic is checked by Lean's kernel; the external search is not trusted.
`decode_packedMul` supplies the interpretation as binary matrix multiplication.
-/

@[expose] public section
namespace Janko4.Simplicity.ThreeFusion
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem p40 : packedMul r25 r13 = r26 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p41 : packedMul r26 r13 = r27 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p42 : packedMul r21 r13 = r28 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p43 : packedMul r28 r20 = r29 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p44 : packedMul r29 r13 = r30 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p45 : packedMul r30 r13 = r31 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p46 : packedMul r31 r13 = r32 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p47 : packedMul r32 r20 = r33 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p48 : packedMul r33 r13 = r34 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p49 : packedMul r34 r13 = r35 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p50 : packedMul r35 r13 = r36 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p51 : packedMul r36 r13 = r37 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p52 : packedMul r27 r38 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p53 : packedMul r37 r39 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p54 : packedMul r38 r39 = r40 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p55 : packedMul r40 r27 = r41 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p56 : packedMul r41 r37 = r42 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p57 : packedMul r2 r1 = r43 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p58 : packedMul r43 r0 = r44 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p59 : packedMul r44 r1 = r45 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p60 : packedMul r45 r0 = r46 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p61 : packedMul r46 r1 = r47 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p62 : packedMul r47 r0 = r48 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p63 : packedMul r48 r1 = r49 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p64 : packedMul r49 r1 = r50 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p65 : packedMul r50 r50 = q51_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p66 : packedMul r50 q51_2 = q51_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p67 : packedMul q51_2 q51_3 = q51_5 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p68 : packedMul q51_3 q51_3 = q51_6 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p69 : packedMul q51_5 q51_6 = q51_11 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p70 : packedMul q51_11 q51_11 = r51 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p71 : packedMul r50 r50 = q52_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p72 : packedMul q52_2 q52_2 = q52_4 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p73 : packedMul q52_4 q52_4 = q52_8 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p74 : packedMul q52_8 q52_8 = q52_16 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p75 : packedMul r50 q52_2 = q52_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p76 : packedMul q52_2 q52_3 = q52_5 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p77 : packedMul q52_4 q52_5 = q52_9 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p78 : packedMul q52_8 q52_9 = q52_17 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p79 : packedMul q52_16 q52_17 = r52 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)


end Janko4.Simplicity.ThreeFusion
