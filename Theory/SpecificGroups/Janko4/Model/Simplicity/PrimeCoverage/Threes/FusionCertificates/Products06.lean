module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Rows

/-!
# Kernel-checked products for ambient J4 fusion, part 7

All arithmetic is checked by Lean's kernel; the external search is not trusted.
`decode_packedMul` supplies the interpretation as binary matrix multiplication.
-/

@[expose] public section
namespace Janko4.Simplicity.ThreeFusion
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem p240 : packedMul r196 r20 = r197 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p241 : packedMul r197 r195 = r198 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p242 : packedMul r20 r198 = r199 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p243 : packedMul r199 r199 = q200_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p244 : packedMul r199 q200_2 = q200_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p245 : packedMul q200_3 q200_3 = r200 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p246 : packedMul r56 r1 = r201 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p247 : packedMul r201 r55 = r202 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p248 : packedMul r202 r0 = r203 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p249 : packedMul r203 r1 = r204 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p250 : packedMul r204 r1 = r205 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p251 : packedMul r205 r43 = r206 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p252 : packedMul r206 r2 = r207 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p253 : packedMul r207 r43 = r208 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p254 : packedMul r208 r209 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p255 : packedMul r209 r20 = r210 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p256 : packedMul r210 r208 = r211 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p257 : packedMul r20 r211 = r212 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p258 : packedMul r212 r212 = q213_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p259 : packedMul r212 q213_2 = q213_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p260 : packedMul q213_3 q213_3 = r213 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p261 : packedMul r142 r55 = r214 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p262 : packedMul r214 r55 = r215 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p263 : packedMul r215 r1 = r216 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p264 : packedMul r216 r43 = r217 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p265 : packedMul r217 r43 = r218 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p266 : packedMul r218 r43 = r219 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p267 : packedMul r219 r1 = r220 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p268 : packedMul r220 r55 = r221 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p269 : packedMul r221 r222 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p270 : packedMul r222 r20 = r223 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p271 : packedMul r223 r221 = r224 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p272 : packedMul r20 r224 = r225 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p273 : packedMul r225 r225 = q226_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p274 : packedMul r225 q226_2 = q226_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p275 : packedMul q226_3 q226_3 = r226 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p276 : packedMul r92 r55 = r227 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p277 : packedMul r227 r2 = r228 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p278 : packedMul r228 r43 = r229 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p279 : packedMul r229 r43 = r230 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)


end Janko4.Simplicity.ThreeFusion
