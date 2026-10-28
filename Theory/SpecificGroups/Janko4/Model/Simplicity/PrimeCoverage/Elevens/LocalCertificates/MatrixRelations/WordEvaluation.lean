module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.MatrixRelations.Products
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.MatrixRelations.Transfer

/-!
# Evaluation of the eleven-local straight-line program

The words follow ATLAS J4G1-max7W1, attributed and transcribed in
`Elevens.Words`. Literal tables are untrusted witnesses: `decide +kernel`
checks their products and `decode_packedMul` transfers them to matrices.
-/

@[expose] public section
namespace Janko4.Simplicity.Elevens.MatrixCertificates
open Janko4.GeneratorCertificates

def t1 {G : Type*} [Group G] (a b : G) : G := a * b

def t2 {G : Type*} [Group G] (a b : G) : G := (t1 a b) * b

def t3 {G : Type*} [Group G] (a b : G) : G := (t1 a b) * (t2 a b)

def t4 {G : Type*} [Group G] (a b : G) : G := (t1 a b) * (t3 a b)

def t5 {G : Type*} [Group G] (a b : G) : G := (t4 a b) * (t2 a b)

def t6 {G : Type*} [Group G] (a b : G) : G := (t2 a b) ^ 4

def t7 {G : Type*} [Group G] (a b : G) : G := (t5 a b) ^ 8

def t8 {G : Type*} [Group G] (a b : G) : G := (t7 a b)⁻¹

def t9 {G : Type*} [Group G] (a b : G) : G := (t8 a b) * (t6 a b)

def t10 {G : Type*} [Group G] (a b : G) : G := (t9 a b) * (t7 a b)

def t11 {G : Type*} [Group G] (a b : G) : G := a * (t10 a b)

def t12 {G : Type*} [Group G] (a b : G) : G := (t11 a b) * (t10 a b)

def t13 {G : Type*} [Group G] (a b : G) : G := (t12 a b) ^ 3

def t14 {G : Type*} [Group G] (a b : G) : G := (t11 a b) * (t11 a b)

def t15 {G : Type*} [Group G] (a b : G) : G := (t13 a b) * (t14 a b)

def t16 {G : Type*} [Group G] (a b : G) : G := (t11 a b) ^ 6

def t17 {G : Type*} [Group G] (a b : G) : G := (t16 a b) * (t15 a b)

def t18 {G : Type*} [Group G] (a b : G) : G := (t17 a b) ^ 20

def t19 {G : Type*} [Group G] (a b : G) : G := (t18 a b) * b

def t20 {G : Type*} [Group G] (a b : G) : G := b * (t18 a b)

def t21 {G : Type*} [Group G] (a b : G) : G := (t20 a b)⁻¹

def t22 {G : Type*} [Group G] (a b : G) : G := (t21 a b) * (t19 a b)

def t23 {G : Type*} [Group G] (a b : G) : G := (t22 a b) ^ 3

def t24 {G : Type*} [Group G] (a b : G) : G := (t17 a b) * (t23 a b)

def t25 {G : Type*} [Group G] (a b : G) : G := (t17 a b) * (t24 a b)

def t26 {G : Type*} [Group G] (a b : G) : G := (t25 a b) ^ 7

def t27 {G : Type*} [Group G] (a b : G) : G := (t17 a b)⁻¹

def t28 {G : Type*} [Group G] (a b : G) : G := (t27 a b) * (t23 a b)

def t29 {G : Type*} [Group G] (a b : G) : G := (t23 a b) * (t28 a b)

def t30 {G : Type*} [Group G] (a b : G) : G := (t17 a b) ^ 8

def t31 {G : Type*} [Group G] (a b : G) : G := (t30 a b) * (t29 a b)

def t32 {G : Type*} [Group G] (a b : G) : G := (t31 a b)⁻¹

def t33 {G : Type*} [Group G] (a b : G) : G := a * (t17 a b)

def t34 {G : Type*} [Group G] (a b : G) : G := (t32 a b) * (t26 a b)

def t35 {G : Type*} [Group G] (a b : G) : G := (t34 a b) * (t31 a b)

def v15 {G : Type*} [Group G] (a b : G) : G := (t33 a b) ^ 15

def uv15 {G : Type*} [Group G] (a b : G) : G := (t35 a b) * (v15 a b)

def x {G : Type*} [Group G] (a b : G) : G := (uv15 a b) ^ 2

def vi {G : Type*} [Group G] (a b : G) : G := (t33 a b)⁻¹

def vix {G : Type*} [Group G] (a b : G) : G := (vi a b) * (x a b)

def y {G : Type*} [Group G] (a b : G) : G := (vix a b) * (t33 a b)

def xi {G : Type*} [Group G] (a b : G) : G := (x a b)⁻¹

def yi {G : Type*} [Group G] (a b : G) : G := (y a b)⁻¹

def xiyi {G : Type*} [Group G] (a b : G) : G := (xi a b) * (yi a b)

def xiyix {G : Type*} [Group G] (a b : G) : G := (xiyi a b) * (x a b)

def z {G : Type*} [Group G] (a b : G) : G := (xiyix a b) * (y a b)

def x11 {G : Type*} [Group G] (a b : G) : G := (x a b) ^ 11

def y11 {G : Type*} [Group G] (a b : G) : G := (y a b) ^ 11

def z11 {G : Type*} [Group G] (a b : G) : G := (z a b) ^ 11

def xz {G : Type*} [Group G] (a b : G) : G := (x a b) * (z a b)

def zx {G : Type*} [Group G] (a b : G) : G := (z a b) * (x a b)

def yz {G : Type*} [Group G] (a b : G) : G := (y a b) * (z a b)

def zy {G : Type*} [Group G] (a b : G) : G := (z a b) * (y a b)

def ui {G : Type*} [Group G] (a b : G) : G := (t35 a b)⁻¹

def uix {G : Type*} [Group G] (a b : G) : G := (ui a b) * (x a b)

def ux {G : Type*} [Group G] (a b : G) : G := (uix a b) * (t35 a b)

def uiy {G : Type*} [Group G] (a b : G) : G := (ui a b) * (y a b)

def uy {G : Type*} [Group G] (a b : G) : G := (uiy a b) * (t35 a b)

def uiz {G : Type*} [Group G] (a b : G) : G := (ui a b) * (z a b)

def uz {G : Type*} [Group G] (a b : G) : G := (uiz a b) * (t35 a b)

def viy {G : Type*} [Group G] (a b : G) : G := (vi a b) * (y a b)

def vy {G : Type*} [Group G] (a b : G) : G := (viy a b) * (t33 a b)

def viz {G : Type*} [Group G] (a b : G) : G := (vi a b) * (z a b)

def vz {G : Type*} [Group G] (a b : G) : G := (viz a b) * (t33 a b)

def y3 {G : Type*} [Group G] (a b : G) : G := (y a b) ^ 3

def x7 {G : Type*} [Group G] (a b : G) : G := (x a b) ^ 7

def y10 {G : Type*} [Group G] (a b : G) : G := (y a b) ^ 10

def z2 {G : Type*} [Group G] (a b : G) : G := (z a b) ^ 2

def x5 {G : Type*} [Group G] (a b : G) : G := (x a b) ^ 5

def z4 {G : Type*} [Group G] (a b : G) : G := (z a b) ^ 4

def z6 {G : Type*} [Group G] (a b : G) : G := (z a b) ^ 6

def rhsux {G : Type*} [Group G] (a b : G) : G := (y3 a b) * (z a b)

def rhsuy1 {G : Type*} [Group G] (a b : G) : G := (x7 a b) * (y10 a b)

def rhsuy {G : Type*} [Group G] (a b : G) : G := (rhsuy1 a b) * (z2 a b)

def rhsvy1 {G : Type*} [Group G] (a b : G) : G := (x5 a b) * (y a b)

def rhsvy {G : Type*} [Group G] (a b : G) : G := (rhsvy1 a b) * (z4 a b)

lemma eval_a (hA : matrixA * matrixA = 1) (_hB : matrixB ^ 4 = 1) :
    toMatrix (Simplicity.a hA) = decodeRows aRows := rfl

lemma eval_b (_hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix (Simplicity.b hB) = decodeRows bRows := rfl

lemma eval_t1 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t1 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t1Rows := by
  exact mul_certificate (eval_a hA hB) (eval_b hA hB) product_t1

lemma eval_t2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t2 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t2Rows := by
  exact mul_certificate (eval_t1 hA hB) (eval_b hA hB) product_t2

lemma eval_t3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t3 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t3Rows := by
  exact mul_certificate (eval_t1 hA hB) (eval_t2 hA hB) product_t3

lemma eval_t4 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t4 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t4Rows := by
  exact mul_certificate (eval_t1 hA hB) (eval_t3 hA hB) product_t4

lemma eval_t5 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t5 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t5Rows := by
  exact mul_certificate (eval_t4 hA hB) (eval_t2 hA hB) product_t5

lemma eval_t6_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t2 (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows t2Rows := by
  simpa only [pow_one] using (eval_t2 hA hB)

lemma eval_t6p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t2 (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows t6p2Rows := by
  exact pow_certificate (g := (t2 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_t6_base hA hB) (eval_t6_base hA hB) product_t6p2

lemma eval_t6 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t6 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t6Rows := by
  exact pow_certificate (g := (t2 (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 2) (eval_t6p2 hA hB) (eval_t6p2 hA hB) product_t6

lemma eval_t7_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t5 (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows t5Rows := by
  simpa only [pow_one] using (eval_t5 hA hB)

lemma eval_t7p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t5 (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows t7p2Rows := by
  exact pow_certificate (g := (t5 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_t7_base hA hB) (eval_t7_base hA hB) product_t7p2

lemma eval_t7p4 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t5 (Simplicity.a hA) (Simplicity.b hB)) ^ 4) = decodeRows t7p4Rows := by
  exact pow_certificate (g := (t5 (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 2) (eval_t7p2 hA hB) (eval_t7p2 hA hB) product_t7p4

lemma eval_t7 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t7 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t7Rows := by
  exact pow_certificate (g := (t5 (Simplicity.a hA) (Simplicity.b hB))) (m := 4) (n := 4) (eval_t7p4 hA hB) (eval_t7p4 hA hB) product_t7

lemma eval_t8 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t8 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t8Rows := by
  exact inv_certificate (eval_t7 hA hB) product_t8

lemma eval_t9 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t9 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t9Rows := by
  exact mul_certificate (eval_t8 hA hB) (eval_t6 hA hB) product_t9

lemma eval_t10 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t10 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t10Rows := by
  exact mul_certificate (eval_t9 hA hB) (eval_t7 hA hB) product_t10

lemma eval_t11 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t11 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t11Rows := by
  exact mul_certificate (eval_a hA hB) (eval_t10 hA hB) product_t11

lemma eval_t12 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t12 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t12Rows := by
  exact mul_certificate (eval_t11 hA hB) (eval_t10 hA hB) product_t12

lemma eval_t13_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t12 (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows t12Rows := by
  simpa only [pow_one] using (eval_t12 hA hB)

lemma eval_t13p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t12 (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows t13p2Rows := by
  exact pow_certificate (g := (t12 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_t13_base hA hB) (eval_t13_base hA hB) product_t13p2

lemma eval_t13 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t13 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t13Rows := by
  exact pow_certificate (g := (t12 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_t13_base hA hB) (eval_t13p2 hA hB) product_t13

lemma eval_t14 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t14 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t14Rows := by
  exact mul_certificate (eval_t11 hA hB) (eval_t11 hA hB) product_t14

lemma eval_t15 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t15 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t15Rows := by
  exact mul_certificate (eval_t13 hA hB) (eval_t14 hA hB) product_t15

lemma eval_t16_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t11 (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows t11Rows := by
  simpa only [pow_one] using (eval_t11 hA hB)

lemma eval_t16p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t11 (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows t14Rows := by
  exact pow_certificate (g := (t11 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_t16_base hA hB) (eval_t16_base hA hB) product_t16p2

lemma eval_t16p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t11 (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows t16p3Rows := by
  exact pow_certificate (g := (t11 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_t16_base hA hB) (eval_t16p2 hA hB) product_t16p3

lemma eval_t16 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t16 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t16Rows := by
  exact pow_certificate (g := (t11 (Simplicity.a hA) (Simplicity.b hB))) (m := 3) (n := 3) (eval_t16p3 hA hB) (eval_t16p3 hA hB) product_t16

lemma eval_t17 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t17 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t17Rows := by
  exact mul_certificate (eval_t16 hA hB) (eval_t15 hA hB) product_t17

lemma eval_t18_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t17 (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows t17Rows := by
  simpa only [pow_one] using (eval_t17 hA hB)

lemma eval_t18p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t17 (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows t18p2Rows := by
  exact pow_certificate (g := (t17 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_t18_base hA hB) (eval_t18_base hA hB) product_t18p2

lemma eval_t18p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t17 (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows t18p3Rows := by
  exact pow_certificate (g := (t17 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_t18_base hA hB) (eval_t18p2 hA hB) product_t18p3

lemma eval_t18p5 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t17 (Simplicity.a hA) (Simplicity.b hB)) ^ 5) = decodeRows t18p5Rows := by
  exact pow_certificate (g := (t17 (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 3) (eval_t18p2 hA hB) (eval_t18p3 hA hB) product_t18p5

lemma eval_t18p10 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t17 (Simplicity.a hA) (Simplicity.b hB)) ^ 10) = decodeRows t18p10Rows := by
  exact pow_certificate (g := (t17 (Simplicity.a hA) (Simplicity.b hB))) (m := 5) (n := 5) (eval_t18p5 hA hB) (eval_t18p5 hA hB) product_t18p10

lemma eval_t18 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t18 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t18Rows := by
  exact pow_certificate (g := (t17 (Simplicity.a hA) (Simplicity.b hB))) (m := 10) (n := 10) (eval_t18p10 hA hB) (eval_t18p10 hA hB) product_t18

lemma eval_t19 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t19 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t19Rows := by
  exact mul_certificate (eval_t18 hA hB) (eval_b hA hB) product_t19

lemma eval_t20 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t20 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t20Rows := by
  exact mul_certificate (eval_b hA hB) (eval_t18 hA hB) product_t20

lemma eval_t21 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t21 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t21Rows := by
  exact inv_certificate (eval_t20 hA hB) product_t21

lemma eval_t22 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t22 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t22Rows := by
  exact mul_certificate (eval_t21 hA hB) (eval_t19 hA hB) product_t22

lemma eval_t23_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t22 (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows t22Rows := by
  simpa only [pow_one] using (eval_t22 hA hB)

lemma eval_t23p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t22 (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows t23p2Rows := by
  exact pow_certificate (g := (t22 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_t23_base hA hB) (eval_t23_base hA hB) product_t23p2

lemma eval_t23 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t23 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t23Rows := by
  exact pow_certificate (g := (t22 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_t23_base hA hB) (eval_t23p2 hA hB) product_t23

lemma eval_t24 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t24 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t24Rows := by
  exact mul_certificate (eval_t17 hA hB) (eval_t23 hA hB) product_t24

lemma eval_t25 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t25 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t25Rows := by
  exact mul_certificate (eval_t17 hA hB) (eval_t24 hA hB) product_t25

lemma eval_t26_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t25 (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows t25Rows := by
  simpa only [pow_one] using (eval_t25 hA hB)

lemma eval_t26p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t25 (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows t26p2Rows := by
  exact pow_certificate (g := (t25 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_t26_base hA hB) (eval_t26_base hA hB) product_t26p2

lemma eval_t26p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t25 (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows t26p3Rows := by
  exact pow_certificate (g := (t25 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_t26_base hA hB) (eval_t26p2 hA hB) product_t26p3

lemma eval_t26p4 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t25 (Simplicity.a hA) (Simplicity.b hB)) ^ 4) = decodeRows t26p4Rows := by
  exact pow_certificate (g := (t25 (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 2) (eval_t26p2 hA hB) (eval_t26p2 hA hB) product_t26p4

lemma eval_t26 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t26 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t26Rows := by
  exact pow_certificate (g := (t25 (Simplicity.a hA) (Simplicity.b hB))) (m := 3) (n := 4) (eval_t26p3 hA hB) (eval_t26p4 hA hB) product_t26

lemma eval_t27 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t27 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t27Rows := by
  exact inv_certificate (eval_t17 hA hB) product_t27

lemma eval_t28 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t28 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t28Rows := by
  exact mul_certificate (eval_t27 hA hB) (eval_t23 hA hB) product_t28

lemma eval_t29 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t29 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t29Rows := by
  exact mul_certificate (eval_t23 hA hB) (eval_t28 hA hB) product_t29

lemma eval_t30_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t17 (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows t17Rows := by
  simpa only [pow_one] using (eval_t17 hA hB)

lemma eval_t30p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t17 (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows t18p2Rows := by
  exact pow_certificate (g := (t17 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_t30_base hA hB) (eval_t30_base hA hB) product_t30p2

lemma eval_t30p4 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t17 (Simplicity.a hA) (Simplicity.b hB)) ^ 4) = decodeRows t30p4Rows := by
  exact pow_certificate (g := (t17 (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 2) (eval_t30p2 hA hB) (eval_t30p2 hA hB) product_t30p4

lemma eval_t30 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t30 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t30Rows := by
  exact pow_certificate (g := (t17 (Simplicity.a hA) (Simplicity.b hB))) (m := 4) (n := 4) (eval_t30p4 hA hB) (eval_t30p4 hA hB) product_t30

lemma eval_t31 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t31 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t31Rows := by
  exact mul_certificate (eval_t30 hA hB) (eval_t29 hA hB) product_t31

lemma eval_t32 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t32 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t32Rows := by
  exact inv_certificate (eval_t31 hA hB) product_t32

lemma eval_t33 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t33 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t33Rows := by
  exact mul_certificate (eval_a hA hB) (eval_t17 hA hB) product_t33

lemma eval_t34 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t34 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t34Rows := by
  exact mul_certificate (eval_t32 hA hB) (eval_t26 hA hB) product_t34

lemma eval_t35 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t35 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows t35Rows := by
  exact mul_certificate (eval_t34 hA hB) (eval_t31 hA hB) product_t35

lemma eval_v15_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t33 (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows t33Rows := by
  simpa only [pow_one] using (eval_t33 hA hB)

lemma eval_v15p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t33 (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows v15p2Rows := by
  exact pow_certificate (g := (t33 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_v15_base hA hB) (eval_v15_base hA hB) product_v15p2

lemma eval_v15p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t33 (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows v15p3Rows := by
  exact pow_certificate (g := (t33 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_v15_base hA hB) (eval_v15p2 hA hB) product_v15p3

lemma eval_v15p4 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t33 (Simplicity.a hA) (Simplicity.b hB)) ^ 4) = decodeRows v15p4Rows := by
  exact pow_certificate (g := (t33 (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 2) (eval_v15p2 hA hB) (eval_v15p2 hA hB) product_v15p4

lemma eval_v15p7 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t33 (Simplicity.a hA) (Simplicity.b hB)) ^ 7) = decodeRows v15p7Rows := by
  exact pow_certificate (g := (t33 (Simplicity.a hA) (Simplicity.b hB))) (m := 3) (n := 4) (eval_v15p3 hA hB) (eval_v15p4 hA hB) product_v15p7

lemma eval_v15p8 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((t33 (Simplicity.a hA) (Simplicity.b hB)) ^ 8) = decodeRows v15p8Rows := by
  exact pow_certificate (g := (t33 (Simplicity.a hA) (Simplicity.b hB))) (m := 4) (n := 4) (eval_v15p4 hA hB) (eval_v15p4 hA hB) product_v15p8

lemma eval_v15 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((v15 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows v15Rows := by
  exact pow_certificate (g := (t33 (Simplicity.a hA) (Simplicity.b hB))) (m := 7) (n := 8) (eval_v15p7 hA hB) (eval_v15p8 hA hB) product_v15

lemma eval_uv15 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((uv15 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows uv15Rows := by
  exact mul_certificate (eval_t35 hA hB) (eval_v15 hA hB) product_uv15

lemma eval_x_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((uv15 (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows uv15Rows := by
  simpa only [pow_one] using (eval_uv15 hA hB)

lemma eval_x (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB))) = decodeRows xRows := by
  exact pow_certificate (g := (uv15 (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_x_base hA hB) (eval_x_base hA hB) product_x

lemma eval_vi (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((vi (Simplicity.a hA) (Simplicity.b hB))) = decodeRows viRows := by
  exact inv_certificate (eval_t33 hA hB) product_vi

lemma eval_vix (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((vix (Simplicity.a hA) (Simplicity.b hB))) = decodeRows vixRows := by
  exact mul_certificate (eval_vi hA hB) (eval_x hA hB) product_vix

lemma eval_y (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB))) = decodeRows yRows := by
  exact mul_certificate (eval_vix hA hB) (eval_t33 hA hB) product_y

lemma eval_xi (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((xi (Simplicity.a hA) (Simplicity.b hB))) = decodeRows xiRows := by
  exact inv_certificate (eval_x hA hB) product_xi

lemma eval_yi (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((yi (Simplicity.a hA) (Simplicity.b hB))) = decodeRows yiRows := by
  exact inv_certificate (eval_y hA hB) product_yi

lemma eval_xiyi (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((xiyi (Simplicity.a hA) (Simplicity.b hB))) = decodeRows xiyiRows := by
  exact mul_certificate (eval_xi hA hB) (eval_yi hA hB) product_xiyi

lemma eval_xiyix (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((xiyix (Simplicity.a hA) (Simplicity.b hB))) = decodeRows xiyixRows := by
  exact mul_certificate (eval_xiyi hA hB) (eval_x hA hB) product_xiyix

lemma eval_z (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB))) = decodeRows zRows := by
  exact mul_certificate (eval_xiyix hA hB) (eval_y hA hB) product_z

lemma eval_x11_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows xRows := by
  simpa only [pow_one] using (eval_x hA hB)

lemma eval_x11p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows x11p2Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_x11_base hA hB) (eval_x11_base hA hB) product_x11p2

lemma eval_x11p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows x11p3Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_x11_base hA hB) (eval_x11p2 hA hB) product_x11p3

lemma eval_x11p5 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 5) = decodeRows x11p5Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 3) (eval_x11p2 hA hB) (eval_x11p3 hA hB) product_x11p5

lemma eval_x11p6 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 6) = decodeRows x11p6Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 3) (n := 3) (eval_x11p3 hA hB) (eval_x11p3 hA hB) product_x11p6

lemma eval_x11 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x11 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows packedOne := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 5) (n := 6) (eval_x11p5 hA hB) (eval_x11p6 hA hB) product_x11

lemma eval_y11_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows yRows := by
  simpa only [pow_one] using (eval_y hA hB)

lemma eval_y11p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows y11p2Rows := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_y11_base hA hB) (eval_y11_base hA hB) product_y11p2

lemma eval_y11p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows y11p3Rows := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_y11_base hA hB) (eval_y11p2 hA hB) product_y11p3

lemma eval_y11p5 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 5) = decodeRows y11p5Rows := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 3) (eval_y11p2 hA hB) (eval_y11p3 hA hB) product_y11p5

lemma eval_y11p6 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 6) = decodeRows y11p6Rows := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 3) (n := 3) (eval_y11p3 hA hB) (eval_y11p3 hA hB) product_y11p6

lemma eval_y11 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y11 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows packedOne := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 5) (n := 6) (eval_y11p5 hA hB) (eval_y11p6 hA hB) product_y11

lemma eval_z11_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows zRows := by
  simpa only [pow_one] using (eval_z hA hB)

lemma eval_z11p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows z11p2Rows := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_z11_base hA hB) (eval_z11_base hA hB) product_z11p2

lemma eval_z11p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows z11p3Rows := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_z11_base hA hB) (eval_z11p2 hA hB) product_z11p3

lemma eval_z11p5 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 5) = decodeRows z11p5Rows := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 3) (eval_z11p2 hA hB) (eval_z11p3 hA hB) product_z11p5

lemma eval_z11p6 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 6) = decodeRows z11p6Rows := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 3) (n := 3) (eval_z11p3 hA hB) (eval_z11p3 hA hB) product_z11p6

lemma eval_z11 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z11 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows packedOne := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 5) (n := 6) (eval_z11p5 hA hB) (eval_z11p6 hA hB) product_z11

lemma eval_xz (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((xz (Simplicity.a hA) (Simplicity.b hB))) = decodeRows xzRows := by
  exact mul_certificate (eval_x hA hB) (eval_z hA hB) product_xz

lemma eval_zx (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((zx (Simplicity.a hA) (Simplicity.b hB))) = decodeRows xzRows := by
  exact mul_certificate (eval_z hA hB) (eval_x hA hB) product_zx

lemma eval_yz (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((yz (Simplicity.a hA) (Simplicity.b hB))) = decodeRows yzRows := by
  exact mul_certificate (eval_y hA hB) (eval_z hA hB) product_yz

lemma eval_zy (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((zy (Simplicity.a hA) (Simplicity.b hB))) = decodeRows yzRows := by
  exact mul_certificate (eval_z hA hB) (eval_y hA hB) product_zy

lemma eval_ui (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((ui (Simplicity.a hA) (Simplicity.b hB))) = decodeRows uiRows := by
  exact inv_certificate (eval_t35 hA hB) product_ui

lemma eval_uix (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((uix (Simplicity.a hA) (Simplicity.b hB))) = decodeRows uixRows := by
  exact mul_certificate (eval_ui hA hB) (eval_x hA hB) product_uix

lemma eval_ux (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((ux (Simplicity.a hA) (Simplicity.b hB))) = decodeRows uxRows := by
  exact mul_certificate (eval_uix hA hB) (eval_t35 hA hB) product_ux

lemma eval_uiy (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((uiy (Simplicity.a hA) (Simplicity.b hB))) = decodeRows uiyRows := by
  exact mul_certificate (eval_ui hA hB) (eval_y hA hB) product_uiy

lemma eval_uy (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((uy (Simplicity.a hA) (Simplicity.b hB))) = decodeRows uyRows := by
  exact mul_certificate (eval_uiy hA hB) (eval_t35 hA hB) product_uy

lemma eval_uiz (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((uiz (Simplicity.a hA) (Simplicity.b hB))) = decodeRows uizRows := by
  exact mul_certificate (eval_ui hA hB) (eval_z hA hB) product_uiz

lemma eval_uz (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((uz (Simplicity.a hA) (Simplicity.b hB))) = decodeRows zRows := by
  exact mul_certificate (eval_uiz hA hB) (eval_t35 hA hB) product_uz

lemma eval_viy (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((viy (Simplicity.a hA) (Simplicity.b hB))) = decodeRows viyRows := by
  exact mul_certificate (eval_vi hA hB) (eval_y hA hB) product_viy

lemma eval_vy (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((vy (Simplicity.a hA) (Simplicity.b hB))) = decodeRows vyRows := by
  exact mul_certificate (eval_viy hA hB) (eval_t33 hA hB) product_vy

lemma eval_viz (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((viz (Simplicity.a hA) (Simplicity.b hB))) = decodeRows vizRows := by
  exact mul_certificate (eval_vi hA hB) (eval_z hA hB) product_viz

lemma eval_vz (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((vz (Simplicity.a hA) (Simplicity.b hB))) = decodeRows z11p6Rows := by
  exact mul_certificate (eval_viz hA hB) (eval_t33 hA hB) product_vz

lemma eval_y3_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows yRows := by
  simpa only [pow_one] using (eval_y hA hB)

lemma eval_y3p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows y11p2Rows := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_y3_base hA hB) (eval_y3_base hA hB) product_y3p2

lemma eval_y3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y3 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows y11p3Rows := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_y3_base hA hB) (eval_y3p2 hA hB) product_y3

lemma eval_x7_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows xRows := by
  simpa only [pow_one] using (eval_x hA hB)

lemma eval_x7p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows x11p2Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_x7_base hA hB) (eval_x7_base hA hB) product_x7p2

lemma eval_x7p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows x11p3Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_x7_base hA hB) (eval_x7p2 hA hB) product_x7p3

lemma eval_x7p4 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 4) = decodeRows x7p4Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 2) (eval_x7p2 hA hB) (eval_x7p2 hA hB) product_x7p4

lemma eval_x7 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x7 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows x7Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 3) (n := 4) (eval_x7p3 hA hB) (eval_x7p4 hA hB) product_x7

lemma eval_y10_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows yRows := by
  simpa only [pow_one] using (eval_y hA hB)

lemma eval_y10p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows y11p2Rows := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_y10_base hA hB) (eval_y10_base hA hB) product_y10p2

lemma eval_y10p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows y11p3Rows := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_y10_base hA hB) (eval_y10p2 hA hB) product_y10p3

lemma eval_y10p5 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y (Simplicity.a hA) (Simplicity.b hB)) ^ 5) = decodeRows y11p5Rows := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 3) (eval_y10p2 hA hB) (eval_y10p3 hA hB) product_y10p5

lemma eval_y10 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((y10 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows yiRows := by
  exact pow_certificate (g := (y (Simplicity.a hA) (Simplicity.b hB))) (m := 5) (n := 5) (eval_y10p5 hA hB) (eval_y10p5 hA hB) product_y10

lemma eval_z2_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows zRows := by
  simpa only [pow_one] using (eval_z hA hB)

lemma eval_z2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z2 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows z11p2Rows := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_z2_base hA hB) (eval_z2_base hA hB) product_z2

lemma eval_x5_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows xRows := by
  simpa only [pow_one] using (eval_x hA hB)

lemma eval_x5p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows x11p2Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_x5_base hA hB) (eval_x5_base hA hB) product_x5p2

lemma eval_x5p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows x11p3Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_x5_base hA hB) (eval_x5p2 hA hB) product_x5p3

lemma eval_x5 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((x5 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows x11p5Rows := by
  exact pow_certificate (g := (x (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 3) (eval_x5p2 hA hB) (eval_x5p3 hA hB) product_x5

lemma eval_z4_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows zRows := by
  simpa only [pow_one] using (eval_z hA hB)

lemma eval_z4p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows z11p2Rows := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_z4_base hA hB) (eval_z4_base hA hB) product_z4p2

lemma eval_z4 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z4 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows z4Rows := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 2) (n := 2) (eval_z4p2 hA hB) (eval_z4p2 hA hB) product_z4

lemma eval_z6_base (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 1) = decodeRows zRows := by
  simpa only [pow_one] using (eval_z hA hB)

lemma eval_z6p2 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 2) = decodeRows z11p2Rows := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 1) (eval_z6_base hA hB) (eval_z6_base hA hB) product_z6p2

lemma eval_z6p3 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z (Simplicity.a hA) (Simplicity.b hB)) ^ 3) = decodeRows z11p3Rows := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 1) (n := 2) (eval_z6_base hA hB) (eval_z6p2 hA hB) product_z6p3

lemma eval_z6 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((z6 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows z11p6Rows := by
  exact pow_certificate (g := (z (Simplicity.a hA) (Simplicity.b hB))) (m := 3) (n := 3) (eval_z6p3 hA hB) (eval_z6p3 hA hB) product_z6

lemma eval_rhsux (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((rhsux (Simplicity.a hA) (Simplicity.b hB))) = decodeRows uxRows := by
  exact mul_certificate (eval_y3 hA hB) (eval_z hA hB) product_rhsux

lemma eval_rhsuy1 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((rhsuy1 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows rhsuy1Rows := by
  exact mul_certificate (eval_x7 hA hB) (eval_y10 hA hB) product_rhsuy1

lemma eval_rhsuy (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((rhsuy (Simplicity.a hA) (Simplicity.b hB))) = decodeRows uyRows := by
  exact mul_certificate (eval_rhsuy1 hA hB) (eval_z2 hA hB) product_rhsuy

lemma eval_rhsvy1 (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((rhsvy1 (Simplicity.a hA) (Simplicity.b hB))) = decodeRows rhsvy1Rows := by
  exact mul_certificate (eval_x5 hA hB) (eval_y hA hB) product_rhsvy1

lemma eval_rhsvy (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    toMatrix ((rhsvy (Simplicity.a hA) (Simplicity.b hB))) = decodeRows vyRows := by
  exact mul_certificate (eval_rhsvy1 hA hB) (eval_z4 hA hB) product_rhsvy

end Janko4.Simplicity.Elevens.MatrixCertificates
