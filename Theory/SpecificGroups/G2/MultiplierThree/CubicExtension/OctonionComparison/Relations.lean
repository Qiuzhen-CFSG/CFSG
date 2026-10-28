module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PairMatrices
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.Presentation

/-!
# The marked octonion pair satisfies all six source relations

A shared circuit of small matrix products evaluates the exact ATLAS words,
including the inverse-first source commutators. Powers are assembled from
certified smaller powers. Faithfulness transfers the six identity matrices
to identities of the actual octonion automorphisms.

Generated witnesses: `source/GenerateCertificates.py`. The generator is not
trusted; each product is proved by `decide +kernel`. Source and conventions:
`Presentation.lean` and `source/README.md`.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison

set_option maxRecDepth 4096

private def e0 : Model (ZMod 3) := generator false
private def m0 : Mat := !![2,0,0,0,0,0,0,0;
    0,0,2,0,0,0,0,0;
    0,2,0,0,0,0,0,0;
    0,0,0,1,0,0,0,0;
    0,0,0,0,1,0,0,0;
    0,0,0,0,0,0,2,0;
    0,0,0,0,0,2,0,0;
    0,0,0,0,0,0,0,2]
private theorem check0 : coordinateMatrix e0 = m0 :=
  coordinateMatrix_false

private def e1 : Model (ZMod 3) := generator true
private def m1 : Mat := !![1,0,2,0,0,0,0,0;
    2,1,0,2,1,0,1,0;
    0,0,1,0,0,0,0,0;
    0,0,1,1,0,0,2,0;
    0,0,2,0,1,0,1,0;
    0,0,1,1,2,1,2,1;
    0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,1,1]
private theorem check1 : coordinateMatrix e1 = m1 :=
  coordinateMatrix_true

private def e2 : Model (ZMod 3) := e0 * e1
private def m2 : Mat := !![2,0,1,0,0,0,0,0;
    0,0,2,0,0,0,0,0;
    1,2,0,1,2,0,2,0;
    0,0,1,1,0,0,2,0;
    0,0,2,0,1,0,1,0;
    0,0,0,0,0,0,2,0;
    0,0,2,2,1,2,1,2;
    0,0,0,0,0,0,2,2]
private theorem check2 : coordinateMatrix e2 = m2 :=
  mul_certificate check0 check1 (by decide +kernel)

private def e3 : Model (ZMod 3) := e1⁻¹
private def m3 : Mat := !![1,0,1,0,0,0,0,0;
    1,1,2,1,2,0,1,0;
    0,0,1,0,0,0,0,0;
    0,0,2,1,0,0,1,0;
    0,0,1,0,1,0,2,0;
    0,0,1,2,1,1,0,2;
    0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,2,1]
private theorem check3 : coordinateMatrix e3 = m3 :=
  inv_certificate check1 (by decide +kernel)

private def e4 : Model (ZMod 3) := e0 * e3
private def m4 : Mat := !![2,0,2,0,0,0,0,0;
    0,0,2,0,0,0,0,0;
    2,2,1,2,1,0,2,0;
    0,0,2,1,0,0,1,0;
    0,0,1,0,1,0,2,0;
    0,0,0,0,0,0,2,0;
    0,0,2,1,2,2,0,1;
    0,0,0,0,0,0,1,2]
private theorem check4 : coordinateMatrix e4 = m4 :=
  mul_certificate check0 check3 (by decide +kernel)

private def e5 : Model (ZMod 3) := e0⁻¹
private def m5 : Mat := !![2,0,0,0,0,0,0,0;
    0,0,2,0,0,0,0,0;
    0,2,0,0,0,0,0,0;
    0,0,0,1,0,0,0,0;
    0,0,0,0,1,0,0,0;
    0,0,0,0,0,0,2,0;
    0,0,0,0,0,2,0,0;
    0,0,0,0,0,0,0,2]
private theorem check5 : coordinateMatrix e5 = m5 :=
  inv_certificate check0 (by decide +kernel)

private def e6 : Model (ZMod 3) := e5 * e3
private def m6 : Mat := !![2,0,2,0,0,0,0,0;
    0,0,2,0,0,0,0,0;
    2,2,1,2,1,0,2,0;
    0,0,2,1,0,0,1,0;
    0,0,1,0,1,0,2,0;
    0,0,0,0,0,0,2,0;
    0,0,2,1,2,2,0,1;
    0,0,0,0,0,0,1,2]
private theorem check6 : coordinateMatrix e6 = m6 :=
  mul_certificate check5 check3 (by decide +kernel)

private def e7 : Model (ZMod 3) := e6 * e0
private def m7 : Mat := !![1,1,0,0,0,0,0,0;
    0,1,0,0,0,0,0,0;
    1,2,1,2,1,1,0,0;
    0,1,0,1,0,2,0,0;
    0,2,0,0,1,1,0,0;
    0,0,0,0,0,1,0,0;
    0,1,0,1,2,0,1,2;
    0,0,0,0,0,2,0,1]
private theorem check7 : coordinateMatrix e7 = m7 :=
  mul_certificate check6 check0 (by decide +kernel)

private def e8 : Model (ZMod 3) := e7 * e1
private def m8 : Mat := !![0,1,2,2,1,0,1,0;
    2,1,0,2,1,0,1,0;
    2,2,2,1,2,1,0,1;
    2,1,0,2,2,2,1,2;
    1,2,0,2,2,1,2,1;
    0,0,1,1,2,1,2,1;
    2,1,2,0,0,0,2,2;
    0,0,2,2,1,2,2,0]
private theorem check8 : coordinateMatrix e8 = m8 :=
  mul_certificate check7 check1 (by decide +kernel)

private def e9 : Model (ZMod 3) := e1 * e0
private def m9 : Mat := !![2,1,0,0,0,0,0,0;
    1,0,2,2,1,2,0,0;
    0,2,0,0,0,0,0,0;
    0,2,0,1,0,1,0,0;
    0,1,0,0,1,2,0,0;
    0,2,0,1,2,1,2,2;
    0,0,0,0,0,2,0,0;
    0,0,0,0,0,2,0,2]
private theorem check9 : coordinateMatrix e9 = m9 :=
  mul_certificate check1 check0 (by decide +kernel)

private def e10 : Model (ZMod 3) := e9 * e1
private def m10 : Mat := !![1,1,1,2,1,0,1,0;
    1,0,1,1,2,2,0,2;
    1,2,0,1,2,0,2,0;
    1,2,2,0,1,1,0,1;
    2,1,1,1,0,2,0,2;
    1,2,0,0,0,1,0,0;
    0,0,2,2,1,2,1,2;
    0,0,2,2,1,2,0,1]
private theorem check10 : coordinateMatrix e10 = m10 :=
  mul_certificate check9 check1 (by decide +kernel)

private def e11 : Model (ZMod 3) := e2 ^ 1
private def m11 : Mat := !![2,0,1,0,0,0,0,0;
    0,0,2,0,0,0,0,0;
    1,2,0,1,2,0,2,0;
    0,0,1,1,0,0,2,0;
    0,0,2,0,1,0,1,0;
    0,0,0,0,0,0,2,0;
    0,0,2,2,1,2,1,2;
    0,0,0,0,0,0,2,2]
private theorem check11 : coordinateMatrix e11 = m11 :=
  by
    change coordinateMatrix (e2 ^ 1) = m2
    simpa only [pow_one] using check2

private def e12 : Model (ZMod 3) := e2 ^ 2
private def m12 : Mat := !![2,2,2,1,2,0,2,0;
    2,1,0,2,1,0,1,0;
    2,0,2,2,1,1,0,1;
    1,2,2,0,1,1,0,1;
    2,1,1,1,0,2,0,2;
    0,0,1,1,2,1,2,1;
    2,1,0,0,0,2,0,0;
    0,0,1,1,2,1,0,2]
private theorem check12 : coordinateMatrix e12 = m12 :=
  pow_certificate (k := 1) (l := 1) check11 check11 (by decide +kernel)

private def e13 : Model (ZMod 3) := e2 ^ 3
private def m13 : Mat := !![0,1,0,1,2,1,1,1;
    1,0,1,1,2,2,0,2;
    0,1,0,1,2,0,1,2;
    1,1,1,2,2,0,0,2;
    2,2,2,2,2,0,0,1;
    1,2,0,0,0,1,0,0;
    1,0,1,0,0,0,1,0;
    1,2,2,2,1,0,0,1]
private theorem check13 : coordinateMatrix e13 = m13 :=
  pow_certificate (k := 1) (l := 2) check11 check12 (by decide +kernel)

private def e14 : Model (ZMod 3) := e13 * e4
private def m14 : Mat := !![0,0,2,2,1,2,2,0;
    1,2,1,0,0,0,1,1;
    0,0,2,2,1,2,1,2;
    1,2,2,1,0,0,1,1;
    2,1,1,0,1,0,2,2;
    2,0,0,0,0,0,2,0;
    1,2,2,0,0,2,2,1;
    0,1,1,0,0,0,0,2]
private theorem check14 : coordinateMatrix e14 = m14 :=
  mul_certificate check13 check4 (by decide +kernel)

private def e15 : Model (ZMod 3) := e14 ^ 1
private def m15 : Mat := !![0,0,2,2,1,2,2,0;
    1,2,1,0,0,0,1,1;
    0,0,2,2,1,2,1,2;
    1,2,2,1,0,0,1,1;
    2,1,1,0,1,0,2,2;
    2,0,0,0,0,0,2,0;
    1,2,2,0,0,2,2,1;
    0,1,1,0,0,0,0,2]
private theorem check15 : coordinateMatrix e15 = m15 :=
  by
    change coordinateMatrix (e14 ^ 1) = m14
    simpa only [pow_one] using check14

private def e16 : Model (ZMod 3) := e14 ^ 2
private def m16 : Mat := !![1,0,1,0,0,2,2,1;
    0,1,0,1,2,0,1,1;
    0,0,1,0,0,0,0,1;
    1,0,1,1,0,2,0,1;
    2,0,2,0,1,1,0,2;
    2,1,2,1,2,2,2,2;
    2,0,1,0,0,1,2,1;
    1,1,2,2,1,2,2,1]
private theorem check16 : coordinateMatrix e16 = m16 :=
  pow_certificate (k := 1) (l := 1) check15 check15 (by decide +kernel)

private def e17 : Model (ZMod 3) := e16 * e12
private def m17 : Mat := !![2,1,1,0,0,2,0,2;
    0,0,2,2,1,2,1,1;
    2,0,0,0,0,2,0,0;
    2,1,0,0,1,2,0,0;
    1,2,0,1,0,1,0,0;
    1,2,1,2,1,0,0,1;
    1,0,2,0,0,1,0,1;
    1,1,2,2,1,1,1,1]
private theorem check17 : coordinateMatrix e17 = m17 :=
  mul_certificate check16 check12 (by decide +kernel)

private def e18 : Model (ZMod 3) := e4 ^ 1
private def m18 : Mat := !![2,0,2,0,0,0,0,0;
    0,0,2,0,0,0,0,0;
    2,2,1,2,1,0,2,0;
    0,0,2,1,0,0,1,0;
    0,0,1,0,1,0,2,0;
    0,0,0,0,0,0,2,0;
    0,0,2,1,2,2,0,1;
    0,0,0,0,0,0,1,2]
private theorem check18 : coordinateMatrix e18 = m18 :=
  by
    change coordinateMatrix (e4 ^ 1) = m4
    simpa only [pow_one] using check4

private def e19 : Model (ZMod 3) := e4 ^ 2
private def m19 : Mat := !![2,1,0,1,2,0,1,0;
    1,1,2,1,2,0,1,0;
    0,2,0,0,0,1,0,2;
    1,1,0,0,1,2,2,1;
    2,2,0,1,0,1,1,2;
    0,0,1,2,1,1,0,2;
    1,1,0,2,1,0,2,2;
    0,0,2,1,2,2,2,2]
private theorem check19 : coordinateMatrix e19 = m19 :=
  pow_certificate (k := 1) (l := 1) check18 check18 (by decide +kernel)

private def e20 : Model (ZMod 3) := e17 * e19
private def m20 : Mat := !![2,2,2,0,0,1,1,1;
    2,0,1,2,1,2,0,1;
    1,2,2,0,0,2,2,1;
    1,2,1,2,2,0,1,0;
    2,1,2,2,2,0,2,0;
    2,0,0,2,1,2,1,2;
    2,2,0,1,2,2,0,2;
    2,2,2,2,1,1,2,2]
private theorem check20 : coordinateMatrix e20 = m20 :=
  mul_certificate check17 check19 (by decide +kernel)

private def e21 : Model (ZMod 3) := e20 ^ 1
private def m21 : Mat := !![2,2,2,0,0,1,1,1;
    2,0,1,2,1,2,0,1;
    1,2,2,0,0,2,2,1;
    1,2,1,2,2,0,1,0;
    2,1,2,2,2,0,2,0;
    2,0,0,2,1,2,1,2;
    2,2,0,1,2,2,0,2;
    2,2,2,2,1,1,2,2]
private theorem check21 : coordinateMatrix e21 = m21 :=
  by
    change coordinateMatrix (e20 ^ 1) = m20
    simpa only [pow_one] using check20

private def e22 : Model (ZMod 3) := e20 ^ 2
private def m22 : Mat := 1
private theorem check22 : coordinateMatrix e22 = m22 :=
  pow_certificate (k := 1) (l := 1) check21 check21 (by decide +kernel)

private def e23 : Model (ZMod 3) := e0 ^ 1
private def m23 : Mat := !![2,0,0,0,0,0,0,0;
    0,0,2,0,0,0,0,0;
    0,2,0,0,0,0,0,0;
    0,0,0,1,0,0,0,0;
    0,0,0,0,1,0,0,0;
    0,0,0,0,0,0,2,0;
    0,0,0,0,0,2,0,0;
    0,0,0,0,0,0,0,2]
private theorem check23 : coordinateMatrix e23 = m23 :=
  by
    change coordinateMatrix (e0 ^ 1) = m0
    simpa only [pow_one] using check0

private def e24 : Model (ZMod 3) := e0 ^ 2
private def m24 : Mat := 1
private theorem check24 : coordinateMatrix e24 = m24 :=
  pow_certificate (k := 1) (l := 1) check23 check23 (by decide +kernel)

private def e25 : Model (ZMod 3) := e1 ^ 1
private def m25 : Mat := !![1,0,2,0,0,0,0,0;
    2,1,0,2,1,0,1,0;
    0,0,1,0,0,0,0,0;
    0,0,1,1,0,0,2,0;
    0,0,2,0,1,0,1,0;
    0,0,1,1,2,1,2,1;
    0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,1,1]
private theorem check25 : coordinateMatrix e25 = m25 :=
  by
    change coordinateMatrix (e1 ^ 1) = m1
    simpa only [pow_one] using check1

private def e26 : Model (ZMod 3) := e1 ^ 2
private def m26 : Mat := !![1,0,1,0,0,0,0,0;
    1,1,2,1,2,0,1,0;
    0,0,1,0,0,0,0,0;
    0,0,2,1,0,0,1,0;
    0,0,1,0,1,0,2,0;
    0,0,1,2,1,1,0,2;
    0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,2,1]
private theorem check26 : coordinateMatrix e26 = m26 :=
  pow_certificate (k := 1) (l := 1) check25 check25 (by decide +kernel)

private def e27 : Model (ZMod 3) := e1 ^ 3
private def m27 : Mat := 1
private theorem check27 : coordinateMatrix e27 = m27 :=
  pow_certificate (k := 1) (l := 2) check25 check26 (by decide +kernel)

private def e28 : Model (ZMod 3) := e2 ^ 6
private def m28 : Mat := !![0,0,0,0,0,0,1,1;
    0,0,0,0,0,0,2,0;
    0,0,2,2,1,2,1,2;
    0,0,2,0,1,0,2,1;
    0,0,1,1,0,0,1,2;
    0,0,2,0,0,0,1,2;
    1,2,1,2,1,1,0,0;
    1,0,2,1,2,2,0,0]
private theorem check28 : coordinateMatrix e28 = m28 :=
  pow_certificate (k := 3) (l := 3) check13 check13 (by decide +kernel)

private def e29 : Model (ZMod 3) := e2 ^ 4
private def m29 : Mat := !![0,0,0,0,0,2,0,1;
    0,2,0,2,1,0,2,1;
    0,0,0,0,0,2,0,0;
    0,2,0,0,1,0,0,1;
    0,1,0,1,0,0,0,2;
    2,0,2,0,0,0,2,0;
    0,2,0,0,0,2,0,2;
    1,1,0,1,2,0,2,2]
private theorem check29 : coordinateMatrix e29 = m29 :=
  pow_certificate (k := 2) (l := 2) check12 check12 (by decide +kernel)

private def e30 : Model (ZMod 3) := e2 ^ 7
private def m30 : Mat := !![0,0,2,2,1,2,0,1;
    0,0,1,1,2,1,2,1;
    2,1,0,0,0,2,0,0;
    2,1,0,0,1,1,0,0;
    1,2,0,1,0,2,0,0;
    2,1,2,1,2,2,0,0;
    0,2,0,0,0,0,0,0;
    1,1,0,0,0,0,0,0]
private theorem check30 : coordinateMatrix e30 = m30 :=
  pow_certificate (k := 3) (l := 4) check13 check29 (by decide +kernel)

private def e31 : Model (ZMod 3) := e2 ^ 13
private def m31 : Mat := 1
private theorem check31 : coordinateMatrix e31 = m31 :=
  pow_certificate (k := 6) (l := 7) check28 check30 (by decide +kernel)

private def e32 : Model (ZMod 3) := e8 ^ 1
private def m32 : Mat := !![0,1,2,2,1,0,1,0;
    2,1,0,2,1,0,1,0;
    2,2,2,1,2,1,0,1;
    2,1,0,2,2,2,1,2;
    1,2,0,2,2,1,2,1;
    0,0,1,1,2,1,2,1;
    2,1,2,0,0,0,2,2;
    0,0,2,2,1,2,2,0]
private theorem check32 : coordinateMatrix e32 = m32 :=
  by
    change coordinateMatrix (e8 ^ 1) = m8
    simpa only [pow_one] using check8

private def e33 : Model (ZMod 3) := e8 ^ 2
private def m33 : Mat := !![1,1,0,1,2,1,1,0;
    0,2,0,0,0,2,0,1;
    0,1,2,1,2,0,1,1;
    1,1,0,2,2,0,1,1;
    2,2,0,2,2,0,2,2;
    1,0,0,1,2,2,1,1;
    1,0,1,0,0,0,2,0;
    1,1,1,1,2,0,0,1]
private theorem check33 : coordinateMatrix e33 = m33 :=
  pow_certificate (k := 1) (l := 1) check32 check32 (by decide +kernel)

private def e34 : Model (ZMod 3) := e8 ^ 3
private def m34 : Mat := !![2,2,2,2,1,2,2,1;
    1,2,1,2,1,1,2,2;
    0,2,2,0,0,2,1,2;
    1,0,0,2,2,2,0,2;
    2,0,0,2,2,1,0,1;
    0,1,2,0,0,2,2,2;
    0,2,2,0,0,1,2,2;
    2,0,0,1,2,1,0,2]
private theorem check34 : coordinateMatrix e34 = m34 :=
  pow_certificate (k := 1) (l := 2) check32 check33 (by decide +kernel)

private def e35 : Model (ZMod 3) := e8 ^ 6
private def m35 : Mat := !![0,0,0,0,0,1,0,1;
    0,1,0,2,1,2,1,1;
    0,0,0,0,0,1,0,0;
    0,1,0,0,1,2,0,0;
    0,2,0,1,0,1,0,0;
    2,0,1,1,2,1,0,0;
    0,1,0,0,0,0,0,0;
    1,2,0,0,0,0,0,0]
private theorem check35 : coordinateMatrix e35 = m35 :=
  pow_certificate (k := 3) (l := 3) check34 check34 (by decide +kernel)

private def e36 : Model (ZMod 3) := e8 ^ 4
private def m36 : Mat := !![2,2,1,2,1,2,0,1;
    0,2,1,0,0,2,2,2;
    1,1,0,0,0,2,0,0;
    0,1,2,1,0,0,0,2;
    0,2,1,0,1,0,0,1;
    1,1,2,1,2,2,1,2;
    0,2,1,2,1,1,0,1;
    1,1,0,0,0,0,1,2]
private theorem check36 : coordinateMatrix e36 = m36 :=
  pow_certificate (k := 2) (l := 2) check33 check33 (by decide +kernel)

private def e37 : Model (ZMod 3) := e8 ^ 7
private def m37 : Mat := !![0,0,0,0,0,0,1,1;
    0,0,0,0,0,0,1,0;
    0,0,1,1,2,1,2,1;
    0,0,2,0,1,0,1,0;
    0,0,1,1,0,0,2,0;
    0,0,1,0,0,0,0,0;
    2,1,0,2,1,0,1,0;
    1,0,2,0,0,0,0,0]
private theorem check37 : coordinateMatrix e37 = m37 :=
  pow_certificate (k := 3) (l := 4) check34 check36 (by decide +kernel)

private def e38 : Model (ZMod 3) := e8 ^ 13
private def m38 : Mat := 1
private theorem check38 : coordinateMatrix e38 = m38 :=
  pow_certificate (k := 6) (l := 7) check35 check37 (by decide +kernel)

private def e39 : Model (ZMod 3) := e12 * e36
private def m39 : Mat := !![0,1,1,0,0,2,1,0;
    1,0,0,2,1,1,2,1;
    2,0,0,1,2,1,2,2;
    0,0,0,0,1,0,0,1;
    0,0,0,1,0,0,0,2;
    0,0,2,0,0,0,2,1;
    0,2,1,0,0,1,1,2;
    1,0,0,2,1,1,0,1]
private theorem check39 : coordinateMatrix e39 = m39 :=
  mul_certificate check12 check36 (by decide +kernel)

private def e40 : Model (ZMod 3) := e39 * e13
private def m40 : Mat := !![1,2,2,2,1,1,2,1;
    2,0,2,0,0,2,0,1;
    1,1,2,0,0,0,1,2;
    0,1,1,1,0,0,0,2;
    0,2,2,0,1,0,0,1;
    0,1,1,1,2,0,1,2;
    0,1,1,1,2,2,2,2;
    0,0,0,0,0,2,1,1]
private theorem check40 : coordinateMatrix e40 = m40 :=
  mul_certificate check39 check13 (by decide +kernel)

private def e41 : Model (ZMod 3) := e10⁻¹
private def m41 : Mat := !![1,2,0,2,1,0,2,0;
    0,1,0,0,0,2,0,1;
    2,2,1,2,1,0,2,0;
    1,1,0,0,1,2,2,1;
    2,2,0,1,0,1,1,2;
    2,2,0,1,2,0,1,1;
    0,0,2,1,2,2,0,1;
    0,0,1,2,1,1,1,1]
private theorem check41 : coordinateMatrix e41 = m41 :=
  inv_certificate check10 (by decide +kernel)

private def e42 : Model (ZMod 3) := e5 * e41
private def m42 : Mat := !![2,1,0,1,2,0,1,0;
    1,1,2,1,2,0,1,0;
    0,2,0,0,0,1,0,2;
    1,1,0,0,1,2,2,1;
    2,2,0,1,0,1,1,2;
    0,0,1,2,1,1,0,2;
    1,1,0,2,1,0,2,2;
    0,0,2,1,2,2,2,2]
private theorem check42 : coordinateMatrix e42 = m42 :=
  mul_certificate check5 check41 (by decide +kernel)

private def e43 : Model (ZMod 3) := e42 * e0
private def m43 : Mat := !![1,0,2,1,2,2,0,0;
    2,1,2,1,2,2,0,0;
    0,0,1,0,0,0,2,1;
    2,0,2,0,1,1,1,2;
    1,0,1,1,0,2,2,1;
    0,2,0,2,1,0,2,1;
    2,0,2,2,1,1,0,1;
    0,1,0,1,2,1,1,1]
private theorem check43 : coordinateMatrix e43 = m43 :=
  mul_certificate check42 check0 (by decide +kernel)

private def e44 : Model (ZMod 3) := e43 * e10
private def m44 : Mat := !![1,1,2,0,0,1,2,2;
    0,2,1,0,0,0,0,1;
    1,2,0,1,2,0,1,2;
    1,0,0,1,0,0,1,0;
    2,0,0,0,1,0,2,0;
    0,2,1,0,0,2,2,1;
    0,1,0,0,0,1,0,2;
    1,0,0,1,2,0,1,1]
private theorem check44 : coordinateMatrix e44 = m44 :=
  mul_certificate check43 check10 (by decide +kernel)

private def e45 : Model (ZMod 3) := e44 ^ 1
private def m45 : Mat := !![1,1,2,0,0,1,2,2;
    0,2,1,0,0,0,0,1;
    1,2,0,1,2,0,1,2;
    1,0,0,1,0,0,1,0;
    2,0,0,0,1,0,2,0;
    0,2,1,0,0,2,2,1;
    0,1,0,0,0,1,0,2;
    1,0,0,1,2,0,1,1]
private theorem check45 : coordinateMatrix e45 = m45 :=
  by
    change coordinateMatrix (e44 ^ 1) = m44
    simpa only [pow_one] using check44

private def e46 : Model (ZMod 3) := e44 ^ 2
private def m46 : Mat := !![2,2,1,1,2,2,2,2;
    2,0,2,2,1,0,2,2;
    2,0,1,0,0,2,0,2;
    2,2,2,1,0,2,0,1;
    1,1,1,0,1,1,0,2;
    2,0,1,2,1,0,0,2;
    2,1,2,2,1,2,1,1;
    1,2,2,2,1,2,2,2]
private theorem check46 : coordinateMatrix e46 = m46 :=
  pow_certificate (k := 1) (l := 1) check45 check45 (by decide +kernel)

private def e47 : Model (ZMod 3) := e44 ^ 3
private def m47 : Mat := !![1,2,2,1,2,2,1,1;
    1,2,1,0,0,1,0,2;
    2,2,0,0,0,0,2,1;
    0,2,2,1,0,0,0,1;
    0,1,1,0,1,0,0,2;
    0,1,1,2,1,2,2,2;
    0,1,1,2,1,1,0,2;
    0,0,0,0,0,1,2,1]
private theorem check47 : coordinateMatrix e47 = m47 :=
  pow_certificate (k := 1) (l := 2) check45 check46 (by decide +kernel)

private def e48 : Model (ZMod 3) := e40 * e47
private def m48 : Mat := 1
private theorem check48 : coordinateMatrix e48 = m48 :=
  mul_certificate check40 check47 (by decide +kernel)

/-- The six literal source words hold on the fixed actual octonion pair. -/
theorem generator_relations (i : Fin 6) :
    Presentation.word (generator false) (generator true) i = 1 := by
  apply coordinateMatrix_injective
  rw [map_one]
  fin_cases i
  · exact check24
  · exact check27
  · exact check31
  · exact check38
  · exact check48
  · exact check22

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison
