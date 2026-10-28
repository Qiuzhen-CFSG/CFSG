module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Rows

/-!
# Kernel-checked products for ambient J4 fusion, part 5

All arithmetic is checked by Lean's kernel; the external search is not trusted.
`decode_packedMul` supplies the interpretation as binary matrix multiplication.
-/

@[expose] public section
namespace Janko4.Simplicity.ThreeFusion
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem p160 : packedMul r124 r1 = r125 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p161 : packedMul r125 r55 = r126 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p162 : packedMul r126 r55 = r127 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p163 : packedMul r127 r43 = r128 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p164 : packedMul r128 r43 = r129 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p165 : packedMul r129 r2 = r130 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p166 : packedMul r130 r1 = r131 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p167 : packedMul r131 r55 = r132 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p168 : packedMul r132 r55 = r133 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p169 : packedMul r133 r1 = r134 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p170 : packedMul r134 r135 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p171 : packedMul r135 r20 = r136 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p172 : packedMul r136 r134 = r137 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p173 : packedMul r20 r137 = r138 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p174 : packedMul r138 r138 = q139_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p175 : packedMul r138 q139_2 = q139_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p176 : packedMul q139_3 q139_3 = r139 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p177 : packedMul r55 r2 = r140 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p178 : packedMul r140 r1 = r141 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p179 : packedMul r141 r43 = r142 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p180 : packedMul r142 r43 = r143 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p181 : packedMul r143 r43 = r144 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p182 : packedMul r144 r55 = r145 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p183 : packedMul r145 r1 = r146 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p184 : packedMul r146 r43 = r147 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p185 : packedMul r147 r43 = r148 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p186 : packedMul r148 r55 = r149 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p187 : packedMul r149 r2 = r150 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p188 : packedMul r150 r0 = r151 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p189 : packedMul r151 r1 = r152 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p190 : packedMul r152 r55 = r153 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p191 : packedMul r153 r154 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p192 : packedMul r154 r20 = r155 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p193 : packedMul r155 r153 = r156 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p194 : packedMul r20 r156 = r157 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p195 : packedMul r157 r157 = q158_2 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p196 : packedMul r157 q158_2 = q158_3 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p197 : packedMul q158_2 q158_3 = r158 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p198 : packedMul r153 r158 = r159 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem p199 : packedMul r53 r2 = r160 :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)


end Janko4.Simplicity.ThreeFusion
