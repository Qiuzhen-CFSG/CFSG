module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Rows

/-!
# Kernel-checked products for ambient J4 fusion, part 1

All arithmetic is checked by Lean's kernel; the external search is not trusted.
`decode_packedMul` supplies the interpretation as binary matrix multiplication.
-/

@[expose] public section
namespace Janko4.Simplicity.ThreeFusion
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem p0 : packedMul r0 r1 = r2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p1 : packedMul r1 r0 = r3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p2 : packedMul r2 r2 = q4_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p3 : packedMul q4_2 q4_2 = q4_4 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p4 : packedMul q4_4 q4_4 = q4_8 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p5 : packedMul q4_8 q4_8 = r4 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p6 : packedMul r4 r5 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p7 : packedMul r3 r3 = q6_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p8 : packedMul r3 q6_2 = q6_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p9 : packedMul q6_3 q6_3 = q6_6 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p10 : packedMul q6_6 q6_6 = q6_12 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p11 : packedMul q6_12 q6_12 = r6 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p12 : packedMul r5 r6 = r7 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p13 : packedMul r2 r2 = q8_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p14 : packedMul r2 q8_2 = r8 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p15 : packedMul r8 r1 = r9 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p16 : packedMul r9 r9 = q10_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p17 : packedMul q10_2 q10_2 = r10 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p18 : packedMul r7 r11 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p19 : packedMul r11 r10 = r12 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p20 : packedMul r12 r7 = r13 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p21 : packedMul r3 r3 = q14_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p22 : packedMul q14_2 q14_2 = q14_4 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p23 : packedMul q14_4 q14_4 = r14 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p24 : packedMul r2 r14 = r15 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p25 : packedMul r2 r2 = q16_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p26 : packedMul q16_2 q16_2 = q16_4 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p27 : packedMul r2 q16_2 = q16_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p28 : packedMul q16_2 q16_3 = q16_5 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p29 : packedMul q16_4 q16_5 = q16_9 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p30 : packedMul q16_9 q16_9 = r16 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p31 : packedMul r15 r16 = r17 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p32 : packedMul r17 r18 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p33 : packedMul r18 r0 = r19 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p34 : packedMul r19 r17 = r20 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p35 : packedMul r20 r13 = r21 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p36 : packedMul r21 r20 = r22 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p37 : packedMul r22 r13 = r23 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p38 : packedMul r23 r13 = r24 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p39 : packedMul r24 r13 = r25 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)


end Janko4.Simplicity.ThreeFusion
