module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.Transport
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.WordValues.BasisProducts
import Mathlib.Tactic.FinCases

/-!
# The nine fixed O'Nan binary word values

The product certificates first recover the two local generators, including their
inverse operations. Associativity then identifies the nine positive words with
their candidate matrices. All numerical steps are kernel-checked in the
`WordValues` descendants; no external group identification is used.

Sources and multiplication conventions: `Two/source/README.md` and
`refs/original/onan/README.md`. The intermediate matrix generator is preserved
in `WordValues/Generate.py`.
-/

namespace ONan.Simplicity.TwoCertificate.Enumeration

open WordValues

-- Arithmetic is already certified; keep its large data opaque during assembly.
attribute [local irreducible]
  WordValues.decode WordValues.a WordValues.aT WordValues.b WordValues.bT WordValues.one
  WordValues.oneT WordValues.c WordValues.cT WordValues.d WordValues.dT WordValues.e WordValues.eT
  WordValues.f WordValues.fT WordValues.fe WordValues.feT WordValues.h WordValues.hT WordValues.c2
  WordValues.c2T WordValues.c4 WordValues.c4T WordValues.d2 WordValues.d2T WordValues.d4
  WordValues.d4T WordValues.h2 WordValues.h2T WordValues.h4 WordValues.h4T WordValues.c4inv
  WordValues.c4invT WordValues.d4inv WordValues.d4invT WordValues.ua WordValues.uaT WordValues.u
  WordValues.uT WordValues.vh WordValues.vhT WordValues.v WordValues.vT WordValues.w0
  WordValues.w0T WordValues.w1 WordValues.w1T WordValues.w2 WordValues.w2T WordValues.w3
  WordValues.w3T WordValues.w4 WordValues.w4T WordValues.w5 WordValues.w5T WordValues.w6
  WordValues.w6T WordValues.w7 WordValues.w7T WordValues.w8 WordValues.w8T WordValues.w9
  WordValues.w9T WordValues.w10 WordValues.w10T WordValues.w11 WordValues.w11T WordValues.w12
  WordValues.w12T WordValues.w13 WordValues.w13T WordValues.w14 WordValues.w14T WordValues.w15
  WordValues.w15T WordValues.w16 WordValues.w16T WordValues.w17 WordValues.w17T WordValues.w18
  WordValues.w18T WordValues.w19 WordValues.w19T WordValues.w20 WordValues.w20T WordValues.w21
  WordValues.w21T WordValues.w22 WordValues.w22T WordValues.w23 WordValues.w23T WordValues.w24
  WordValues.w24T WordValues.w25 WordValues.w25T WordValues.w26 WordValues.w26T WordValues.w27
  WordValues.w27T WordValues.w28 WordValues.w28T

private theorem fourth_value (x : Linear) (m m2 m4 : Mat)
    (hx : (x : Mat) = m) (h2 : m * m = m2) (h4 : m2 * m2 = m4) :
    ((x ^ 4 : Linear) : Mat) = m4 := by
  change (x : Mat) ^ 4 = m4
  calc
    (x : Mat) ^ 4 = (x : Mat) ^ 2 * (x : Mat) ^ 2 := pow_add _ 2 2
    _ = m4 := by rw [hx, pow_two, h2, h4]

private theorem inverse_value (x : Linear) (m : Mat) (h : m * (x : Mat) = 1) :
    ((x⁻¹ : Linear) : Mat) = m := by
  calc
    ((x⁻¹ : Linear) : Mat) = 1 * ((x⁻¹ : Linear) : Mat) := (one_mul _).symm
    _ = (m * (x : Mat)) * ((x⁻¹ : Linear) : Mat) := by rw [h]
    _ = m := by rw [mul_assoc, Units.mul_inv, mul_one]

/-- The two conjugated local words have the certified packed matrix values. -/
public theorem localGenerators_eq_wordMatrices (i : Fin 2) :
    ((localGenerators linearA linearB i : Linear) : Mat) = ![decode u, decode v] i := by
  let cL := linearA * linearB
  let dL := cL * linearB
  let eL := cL * dL
  let fL := cL * eL
  let hL := cL * (fL * eL)
  have ha : (linearA : Mat) = decode a := decode_a.symm
  have hb : (linearB : Mat) = decode b := decode_b.symm
  have hc : (cL : Mat) = decode c := by
    simpa only [cL, Units.val_mul, ha, hb] using a_mul_b
  have hd : (dL : Mat) = decode d := by
    simpa only [dL, Units.val_mul, hc, hb] using c_mul_b
  have he : (eL : Mat) = decode e := by
    simpa only [eL, Units.val_mul, hc, hd] using c_mul_d
  have hf : (fL : Mat) = decode f := by
    simpa only [fL, Units.val_mul, hc, he] using c_mul_e
  have hh : (hL : Mat) = decode h := by
    simp only [hL, Units.val_mul, hc, hf, he, f_mul_e, c_mul_fe]
  have hc4 := fourth_value cL _ _ _ hc c_mul_c c2_mul_c2
  have hd4 := fourth_value dL _ _ _ hd d_mul_d d2_mul_d2
  have hh4 := fourth_value hL _ _ _ hh h_mul_h h2_mul_h2
  have hci : (((cL ^ 4)⁻¹ : Linear) : Mat) = decode c4inv := by
    apply inverse_value
    rw [hc4, c4inv_mul_c4, decode_one]
  have hdi : (((dL ^ 4)⁻¹ : Linear) : Mat) = decode d4inv := by
    apply inverse_value
    rw [hd4, d4inv_mul_d4, decode_one]
  fin_cases i
  · change ((((cL ^ 4)⁻¹ * linearA * cL ^ 4 : Linear) : Mat)) = decode u
    rw [Units.val_mul, Units.val_mul, hci, ha, hc4, c4inv_mul_a, ua_mul_c4]
  · change ((((dL ^ 4)⁻¹ * hL ^ 4 * dL ^ 4 : Linear) : Mat)) = decode v
    rw [Units.val_mul, Units.val_mul, hdi, hh4, hd4, d4inv_mul_h4, vh_mul_d4]

private theorem coe_basis_word (i : Fin 9) :
    (linearGenerators i : Mat) =
      ((basisWords i).map (fun j => ![decode u, decode v] j)).prod := by
  change (Units.coeHom Mat) (((basisWords i).map (localGenerators linearA linearB)).prod) = _
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact localGenerators_eq_wordMatrices j

private theorem word_w0 : ((decode u) * (decode v)) = decode w0 :=
  (congrArg₂ (fun x y : Mat => x * y) (rfl : decode u = decode u) (rfl : decode v = decode v)).trans u_mul_v

private theorem word_w1 : (((decode u) * (decode v)) * ((decode u) * (decode v))) = decode w1 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w0 word_w0).trans w0_mul_w0

private theorem word_w2 : ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) = decode w2 :=
  (congrArg₂ (fun x y : Mat => x * y) (rfl : decode v = decode v) word_w1).trans v_mul_w1

private theorem word_w3 : (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) = decode w3 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w0 word_w2).trans w0_mul_w2

private theorem word_w4 : ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))))) = decode w4 :=
  (congrArg₂ (fun x y : Mat => x * y) (rfl : decode v = decode v) word_w3).trans v_mul_w3

private theorem word_w5 : (((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) * ((decode u) * (decode v))) = decode w5 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w2 word_w0).trans w2_mul_w0

private theorem word_w6 : ((decode v) * (decode u)) = decode w6 :=
  (congrArg₂ (fun x y : Mat => x * y) (rfl : decode v = decode v) (rfl : decode u = decode u)).trans v_mul_u

private theorem word_w7 : ((((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) = decode w7 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w3 word_w4).trans w3_mul_w4

private theorem word_w8 : (((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) * (((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) * ((decode u) * (decode v)))) = decode w8 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w2 word_w5).trans w2_mul_w5

private theorem word_w9 : ((((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) * (((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) * ((decode u) * (decode v)))) * (decode u)) = decode w9 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w8 (rfl : decode u = decode u)).trans w8_mul_u

private theorem word_w10 : ((((decode u) * (decode v)) * ((decode u) * (decode v))) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) = decode w10 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w1 word_w2).trans w1_mul_w2

private theorem word_w11 : (((((decode u) * (decode v)) * ((decode u) * (decode v))) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (decode u))) = decode w11 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w10 word_w6).trans w10_mul_w6

private theorem word_w12 : (((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) * ((((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))))))) = decode w12 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w2 word_w7).trans w2_mul_w7

private theorem word_w13 : ((((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) * ((((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))))))) * ((decode u) * (decode v))) = decode w13 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w12 word_w0).trans w12_mul_w0

private theorem word_w14 : (((((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) * ((((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))))))) * ((decode u) * (decode v))) * (decode u)) = decode w14 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w13 (rfl : decode u = decode u)).trans w13_mul_u

private theorem word_w15 : ((decode v) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) = decode w15 :=
  (congrArg₂ (fun x y : Mat => x * y) (rfl : decode v = decode v) word_w2).trans v_mul_w2

private theorem word_w16 : (((decode v) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) = decode w16 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w15 word_w4).trans w15_mul_w4

private theorem word_w17 : ((((decode v) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) * ((decode u) * (decode v))) = decode w17 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w16 word_w0).trans w16_mul_w0

private theorem word_w18 : (((((decode v) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) * ((decode u) * (decode v))) * (decode v)) = decode w18 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w17 (rfl : decode v = decode v)).trans w17_mul_v

private theorem word_w19 : ((((((decode v) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) * ((decode u) * (decode v))) * (decode v)) * ((decode u) * (decode v))) = decode w19 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w18 word_w0).trans w18_mul_w0

private theorem word_w20 : ((((decode u) * (decode v)) * ((decode u) * (decode v))) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))))) = decode w20 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w1 word_w3).trans w1_mul_w3

private theorem word_w21 : (((((decode u) * (decode v)) * ((decode u) * (decode v))) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))))) * ((decode u) * (decode v))) = decode w21 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w20 word_w0).trans w20_mul_w0

private theorem word_w22 : (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) = decode w22 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w0 word_w4).trans w0_mul_w4

private theorem word_w23 : ((((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) * ((((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))))))) = decode w23 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w22 word_w7).trans w22_mul_w7

private theorem word_w24 : (((((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) * ((((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))))))) * (decode u)) = decode w24 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w23 (rfl : decode u = decode u)).trans w23_mul_u

private theorem word_w25 : ((((decode u) * (decode v)) * ((decode u) * (decode v))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) = decode w25 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w1 word_w4).trans w1_mul_w4

private theorem word_w26 : (((((decode u) * (decode v)) * ((decode u) * (decode v))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) * (((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) * ((decode u) * (decode v)))) = decode w26 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w25 word_w5).trans w25_mul_w5

private theorem word_w27 : ((((((decode u) * (decode v)) * ((decode u) * (decode v))) * ((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v))))))) * (((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))) * ((decode u) * (decode v)))) * ((decode v) * (decode u))) = decode w27 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w26 word_w6).trans w26_mul_w6

private theorem word_w28 : (((decode v) * (((decode u) * (decode v)) * ((decode v) * (((decode u) * (decode v)) * ((decode u) * (decode v)))))) * (decode v)) = decode w28 :=
  (congrArg₂ (fun x y : Mat => x * y) word_w4 (rfl : decode v = decode v)).trans w4_mul_v

/-- The actual nine GL words evaluate to the specified basis matrices. -/
public theorem linearGenerators_eq_basisMatrices (i : Fin 9) :
    (linearGenerators i : Mat) = basisMatrices i := by
  rw [coe_basis_word]
  fin_cases i
  · change (decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((1 : Mat)))))))) = basisMatrix0
    simpa only [mul_assoc, mul_one] using word_w3.trans decode_w3
  · change (decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((1 : Mat)))))))))))))) = basisMatrix1
    simpa only [mul_assoc, mul_one] using word_w9.trans decode_w9
  · change (decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((1 : Mat)))))))))))) = basisMatrix2
    simpa only [mul_assoc, mul_one] using word_w11.trans decode_w11
  · change (decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((1 : Mat)))))))))))))))))))))))) = basisMatrix3
    simpa only [mul_assoc, mul_one] using word_w14.trans decode_w14
  · change (decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((1 : Mat)))))))))))))))))))) = basisMatrix4
    simpa only [mul_assoc, mul_one] using word_w19.trans decode_w19
  · change (decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((1 : Mat)))))))))))))) = basisMatrix5
    simpa only [mul_assoc, mul_one] using word_w21.trans decode_w21
  · change (decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((1 : Mat))))))))))))))))))))))))))) = basisMatrix6
    simpa only [mul_assoc, mul_one] using word_w24.trans decode_w24
  · change (decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((1 : Mat)))))))))))))))))))))) = basisMatrix7
    simpa only [mul_assoc, mul_one] using word_w27.trans decode_w27
  · change (decode v) * ((decode u) * ((decode v) * ((decode v) * ((decode u) * ((decode v) * ((decode u) * ((decode v) * ((decode v) * ((1 : Mat)))))))))) = basisMatrix8
    simpa only [mul_assoc, mul_one] using word_w28.trans decode_w28

end ONan.Simplicity.TwoCertificate.Enumeration
