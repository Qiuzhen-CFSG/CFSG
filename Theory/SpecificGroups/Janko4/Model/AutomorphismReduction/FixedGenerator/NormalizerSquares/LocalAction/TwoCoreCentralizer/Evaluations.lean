module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Words
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Products0
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Products1
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Products2
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Products3

/-!
# Explicit words bridging the ATLAS second local subgroup to the first generator

The original word program is `J4G1-max2W1` from the online ATLAS of Finite
Group Representations (R. A. Wilson, S. J. Nickerson, J. N. Bray):
https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/words/J4G1-max2W1 .
Its outputs X,Y centralize t = (XYXYY)^22. With g = b*b*a*b,
d = t*g⁻¹*a*g and h = d^6*g⁻¹, the matrix identities certify h⁻¹*t*h = a
and that h⁻¹*X*h and h⁻¹*Y*h commute with a. All words are evaluated in
the literal matrix carrier. No assertion of full centralizer generation,
two-core structure, group order or simplicity is made here.

Row tables are untrusted witnesses. Packed multiplication is checked by
`decide +kernel`, then transferred by `decode_packedMul`. Source matrices
and bit conventions are documented in `Janko4.Model.Data`.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open Janko4.GeneratorCertificates

private theorem mul_certificate {g h : Model} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hh : toMatrix h = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g * h) = decodeRows ts := by
  rw [map_mul, hg, hh, ← decode_packedMul, hc]

private theorem pow_certificate {g : Model} {m n : ℕ} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix (g ^ m) = decodeRows rs) (hh : toMatrix (g ^ n) = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g ^ (m + n)) = decodeRows ts := by
  rw [pow_add]
  exact mul_certificate hg hh hc

private theorem inv_certificate {g : Model} {rs ss : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hc : packedMul rs ss = packedOne) :
    toMatrix g⁻¹ = decodeRows ss := by
  have h : toMatrix g * decodeRows ss = 1 := by
    rw [hg, ← decode_packedMul, hc, decode_packedOne]
  calc
    toMatrix g⁻¹ = toMatrix g⁻¹ * 1 := (mul_one _).symm
    _ = toMatrix g⁻¹ * (toMatrix g * decodeRows ss) := by rw [h]
    _ = decodeRows ss := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem eval_a : toMatrix a = decodeRows aRows := rfl
private theorem eval_b : toMatrix b = decodeRows bRows := rfl

theorem eval_w0 : toMatrix w0 = decodeRows w0Rows :=
  mul_certificate eval_a eval_b product_w0

theorem eval_w1 : toMatrix w1 = decodeRows w1Rows :=
  mul_certificate eval_w0 eval_b product_w1

theorem eval_w2 : toMatrix w2 = decodeRows w2Rows :=
  mul_certificate eval_w0 eval_w1 product_w2

theorem eval_w3 : toMatrix w3 = decodeRows w3Rows :=
  mul_certificate eval_w0 eval_w2 product_w3

private theorem base_w4 : toMatrix (w2 ^ 1) = decodeRows w2Rows := by
  simpa only [pow_one] using eval_w2

theorem eval_w4p2 : toMatrix (w2 ^ 2) = decodeRows w4p2Rows := by
  exact pow_certificate (g := w2) (m := 1) (n := 1) base_w4 base_w4 product_w4p2

theorem eval_w4p3 : toMatrix (w2 ^ 3) = decodeRows w4p3Rows := by
  exact pow_certificate (g := w2) (m := 1) (n := 2) base_w4 eval_w4p2 product_w4p3

theorem eval_w4 : toMatrix w4 = decodeRows w4Rows := by
  exact pow_certificate (g := w2) (m := 2) (n := 3) eval_w4p2 eval_w4p3 product_w4

theorem eval_w5 : toMatrix w5 = decodeRows w5Rows :=
  mul_certificate eval_w1 eval_b product_w5

private theorem base_w6 : toMatrix (w3 ^ 1) = decodeRows w3Rows := by
  simpa only [pow_one] using eval_w3

theorem eval_w6p2 : toMatrix (w3 ^ 2) = decodeRows w6p2Rows := by
  exact pow_certificate (g := w3) (m := 1) (n := 1) base_w6 base_w6 product_w6p2

theorem eval_w6p4 : toMatrix (w3 ^ 4) = decodeRows w6p4Rows := by
  exact pow_certificate (g := w3) (m := 2) (n := 2) eval_w6p2 eval_w6p2 product_w6p4

theorem eval_w6 : toMatrix w6 = decodeRows w6Rows := by
  exact pow_certificate (g := w3) (m := 4) (n := 4) eval_w6p4 eval_w6p4 product_w6

private theorem base_w7 : toMatrix (w0 ^ 1) = decodeRows w0Rows := by
  simpa only [pow_one] using eval_w0

theorem eval_w7p2 : toMatrix (w0 ^ 2) = decodeRows w7p2Rows := by
  exact pow_certificate (g := w0) (m := 1) (n := 1) base_w7 base_w7 product_w7p2

theorem eval_w7p4 : toMatrix (w0 ^ 4) = decodeRows w7p4Rows := by
  exact pow_certificate (g := w0) (m := 2) (n := 2) eval_w7p2 eval_w7p2 product_w7p4

theorem eval_w7p3 : toMatrix (w0 ^ 3) = decodeRows w7p3Rows := by
  exact pow_certificate (g := w0) (m := 1) (n := 2) base_w7 eval_w7p2 product_w7p3

theorem eval_w7p5 : toMatrix (w0 ^ 5) = decodeRows w7p5Rows := by
  exact pow_certificate (g := w0) (m := 2) (n := 3) eval_w7p2 eval_w7p3 product_w7p5

theorem eval_w7 : toMatrix w7 = decodeRows w7Rows := by
  exact pow_certificate (g := w0) (m := 4) (n := 5) eval_w7p4 eval_w7p5 product_w7

theorem eval_w8 : toMatrix w8 = decodeRows w8Rows :=
  inv_certificate eval_w7 product_w8

theorem eval_w9 : toMatrix w9 = decodeRows w9Rows :=
  mul_certificate eval_w8 eval_w4 product_w9

theorem eval_w10 : toMatrix w10 = decodeRows w10Rows :=
  mul_certificate eval_w9 eval_w7 product_w10

private theorem base_w11 : toMatrix (w5 ^ 1) = decodeRows w5Rows := by
  simpa only [pow_one] using eval_w5

theorem eval_w11p2 : toMatrix (w5 ^ 2) = decodeRows w11p2Rows := by
  exact pow_certificate (g := w5) (m := 1) (n := 1) base_w11 base_w11 product_w11p2

theorem eval_w11p3 : toMatrix (w5 ^ 3) = decodeRows w11p3Rows := by
  exact pow_certificate (g := w5) (m := 1) (n := 2) base_w11 eval_w11p2 product_w11p3

theorem eval_w11p5 : toMatrix (w5 ^ 5) = decodeRows w11p5Rows := by
  exact pow_certificate (g := w5) (m := 2) (n := 3) eval_w11p2 eval_w11p3 product_w11p5

theorem eval_w11p10 : toMatrix (w5 ^ 10) = decodeRows w11p10Rows := by
  exact pow_certificate (g := w5) (m := 5) (n := 5) eval_w11p5 eval_w11p5 product_w11p10

theorem eval_w11p6 : toMatrix (w5 ^ 6) = decodeRows w11p6Rows := by
  exact pow_certificate (g := w5) (m := 3) (n := 3) eval_w11p3 eval_w11p3 product_w11p6

theorem eval_w11p11 : toMatrix (w5 ^ 11) = decodeRows w11p11Rows := by
  exact pow_certificate (g := w5) (m := 5) (n := 6) eval_w11p5 eval_w11p6 product_w11p11

theorem eval_w11 : toMatrix w11 = decodeRows w11Rows := by
  exact pow_certificate (g := w5) (m := 10) (n := 11) eval_w11p10 eval_w11p11 product_w11

theorem eval_w12 : toMatrix w12 = decodeRows w12Rows :=
  inv_certificate eval_w11 product_w12

theorem eval_w13 : toMatrix w13 = decodeRows w13Rows :=
  mul_certificate eval_w12 eval_w6 product_w13

theorem eval_w14 : toMatrix w14 = decodeRows w14Rows :=
  mul_certificate eval_w13 eval_w11 product_w14

theorem eval_xy : toMatrix xy = decodeRows xyRows :=
  mul_certificate eval_w10 eval_w14 product_xy

theorem eval_xyx : toMatrix xyx = decodeRows xyxRows :=
  mul_certificate eval_xy eval_w10 product_xyx

theorem eval_xyxy : toMatrix xyxy = decodeRows xyxyRows :=
  mul_certificate eval_xyx eval_w14 product_xyxy

theorem eval_xyxyy : toMatrix xyxyy = decodeRows xyxyyRows :=
  mul_certificate eval_xyxy eval_w14 product_xyxyy

private theorem base_t : toMatrix (xyxyy ^ 1) = decodeRows xyxyyRows := by
  simpa only [pow_one] using eval_xyxyy

theorem eval_tp2 : toMatrix (xyxyy ^ 2) = decodeRows tp2Rows := by
  exact pow_certificate (g := xyxyy) (m := 1) (n := 1) base_t base_t product_tp2

theorem eval_tp3 : toMatrix (xyxyy ^ 3) = decodeRows tp3Rows := by
  exact pow_certificate (g := xyxyy) (m := 1) (n := 2) base_t eval_tp2 product_tp3

theorem eval_tp5 : toMatrix (xyxyy ^ 5) = decodeRows tp5Rows := by
  exact pow_certificate (g := xyxyy) (m := 2) (n := 3) eval_tp2 eval_tp3 product_tp5

theorem eval_tp6 : toMatrix (xyxyy ^ 6) = decodeRows tp6Rows := by
  exact pow_certificate (g := xyxyy) (m := 3) (n := 3) eval_tp3 eval_tp3 product_tp6

theorem eval_tp11 : toMatrix (xyxyy ^ 11) = decodeRows tp11Rows := by
  exact pow_certificate (g := xyxyy) (m := 5) (n := 6) eval_tp5 eval_tp6 product_tp11

theorem eval_t : toMatrix t = decodeRows tRows := by
  exact pow_certificate (g := xyxyy) (m := 11) (n := 11) eval_tp11 eval_tp11 product_t

theorem eval_bb : toMatrix bb = decodeRows bbRows :=
  mul_certificate eval_b eval_b product_bb

theorem eval_bba : toMatrix bba = decodeRows bbaRows :=
  mul_certificate eval_bb eval_a product_bba

theorem eval_g : toMatrix g = decodeRows gRows :=
  mul_certificate eval_bba eval_b product_g

theorem eval_gi : toMatrix gi = decodeRows giRows :=
  inv_certificate eval_g product_gi

theorem eval_gia : toMatrix gia = decodeRows giaRows :=
  mul_certificate eval_gi eval_a product_gia

theorem eval_ag : toMatrix ag = decodeRows agRows :=
  mul_certificate eval_gia eval_g product_ag

theorem eval_d : toMatrix d = decodeRows dRows :=
  mul_certificate eval_t eval_ag product_d

private theorem base_d6 : toMatrix (d ^ 1) = decodeRows dRows := by
  simpa only [pow_one] using eval_d

theorem eval_d6p2 : toMatrix (d ^ 2) = decodeRows d6p2Rows := by
  exact pow_certificate (g := d) (m := 1) (n := 1) base_d6 base_d6 product_d6p2

theorem eval_d6p3 : toMatrix (d ^ 3) = decodeRows d6p3Rows := by
  exact pow_certificate (g := d) (m := 1) (n := 2) base_d6 eval_d6p2 product_d6p3

theorem eval_d6 : toMatrix d6 = decodeRows d6Rows := by
  exact pow_certificate (g := d) (m := 3) (n := 3) eval_d6p3 eval_d6p3 product_d6

theorem eval_h : toMatrix h = decodeRows hRows :=
  mul_certificate eval_d6 eval_gi product_h

theorem eval_hi : toMatrix hi = decodeRows hiRows :=
  inv_certificate eval_h product_hi

theorem eval_hit : toMatrix hit = decodeRows hitRows :=
  mul_certificate eval_hi eval_t product_hit

theorem eval_ta : toMatrix ta = decodeRows taRows :=
  mul_certificate eval_hit eval_h product_ta

theorem eval_hix : toMatrix hix = decodeRows hixRows :=
  mul_certificate eval_hi eval_w10 product_hix

theorem eval_cx : toMatrix cx = decodeRows cxRows :=
  mul_certificate eval_hix eval_h product_cx

theorem eval_hiy : toMatrix hiy = decodeRows hiyRows :=
  mul_certificate eval_hi eval_w14 product_hiy

theorem eval_cy : toMatrix cy = decodeRows cyRows :=
  mul_certificate eval_hiy eval_h product_cy

theorem eval_cxa : toMatrix cxa = decodeRows cxaRows :=
  mul_certificate eval_cx eval_a product_cxa

theorem eval_acx : toMatrix acx = decodeRows acxRows :=
  mul_certificate eval_a eval_cx product_acx

theorem eval_cya : toMatrix cya = decodeRows cyaRows :=
  mul_certificate eval_cy eval_a product_cya

theorem eval_acy : toMatrix acy = decodeRows acyRows :=
  mul_certificate eval_a eval_cy product_acy

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
