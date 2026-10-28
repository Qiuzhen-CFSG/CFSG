module

public import Theory.SpecificGroups.Janko1.Model.Basic

/-!
# Short matrix words for the J₁ order certificate

The two words `x` and `y` give the subgroup used in the order certificate.
Their products `x*y` and `x*y²` have orders five and eleven. Literal prefix
matrices make each check a small kernel computation. The words were found by
finite search in the ATLAS matrices documented in `Model.Basic`; none of the
external search results is assumed by the proofs.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

public abbrev Mat := Matrix (Fin 7) (Fin 7) (ZMod 11)

@[expose] public def matrixValue : Model →* Mat where
  toFun g := (inclusion g).val
  map_one' := rfl
  map_mul' _ _ := rfl

public theorem matrixValue_injective : Function.Injective matrixValue :=
  Units.val_injective.comp inclusion_injective

private def T1 : Mat := !![9, 9, 2, 1, 3, 8, 6;
    2, 5, 5, 9, 2, 2, 1;
    5, 9, 9, 9, 8, 10, 3;
    5, 5, 7, 10, 9, 2, 5;
    7, 1, 5, 3, 5, 8, 2;
    6, 9, 10, 1, 10, 2, 3;
    1, 9, 6, 5, 9, 5, 4]

private theorem syllable1 : matrixValue (a * b ^ 1) = T1 := by
  change matrixA * matrixB ^ 1 = T1
  decide +kernel

private def T2 : Mat := !![1, 10, 3, 9, 10, 9, 6;
    5, 9, 4, 9, 6, 6, 1;
    9, 3, 6, 9, 10, 3, 9;
    5, 9, 10, 6, 9, 2, 9;
    9, 3, 8, 2, 9, 10, 6;
    4, 9, 5, 5, 1, 9, 5;
    5, 6, 9, 10, 3, 8, 4]

private theorem syllable2 : matrixValue (a * b ^ 2) = T2 := by
  change matrixA * matrixB ^ 2 = T2
  decide +kernel

@[expose] public def x : Model := (a * b ^ 1) * (a * b ^ 2) * (a * b ^ 1) * (a * b ^ 1) * (a * b ^ 2) * (a * b ^ 2) * (a * b ^ 1) * (a * b ^ 2)

private def xP1 : Mat := !![1, 6, 5, 6, 6, 7, 7;
    5, 4, 5, 10, 6, 6, 4;
    6, 8, 6, 5, 3, 8, 3;
    4, 6, 7, 5, 8, 0, 8;
    5, 0, 7, 7, 3, 8, 6;
    6, 4, 10, 5, 5, 7, 6;
    4, 8, 5, 4, 3, 5, 0]

private theorem xStep1 : T1 * T2 = xP1 := by decide +kernel

private def xP2 : Mat := !![2, 4, 8, 0, 8, 3, 8;
    1, 3, 6, 10, 4, 0, 2;
    10, 0, 1, 5, 7, 2, 8;
    7, 3, 4, 4, 6, 8, 3;
    3, 8, 0, 9, 8, 7, 8;
    0, 3, 2, 3, 3, 8, 7;
    5, 2, 10, 10, 4, 8, 0]

private theorem xStep2 : xP1 * T1 = xP2 := by decide +kernel

private def xP3 : Mat := !![5, 8, 5, 1, 0, 5, 9;
    4, 7, 8, 6, 9, 4, 5;
    2, 1, 2, 0, 1, 2, 8;
    4, 8, 1, 8, 1, 2, 4;
    7, 2, 3, 5, 2, 0, 8;
    8, 10, 4, 6, 9, 8, 5;
    5, 7, 5, 2, 3, 3, 1]

private theorem xStep3 : xP2 * T1 = xP3 := by decide +kernel

private def xP4 : Mat := !![6, 3, 6, 8, 2, 7, 10;
    10, 10, 10, 9, 8, 5, 9;
    5, 5, 2, 5, 4, 1, 2;
    9, 1, 8, 8, 6, 9, 2;
    6, 9, 9, 2, 1, 2, 6;
    9, 2, 8, 1, 8, 6, 9;
    7, 1, 9, 9, 6, 6, 5]

private theorem xStep4 : xP3 * T2 = xP4 := by decide +kernel

private def xP5 : Mat := !![2, 9, 1, 3, 1, 5, 10;
    2, 6, 5, 4, 5, 10, 9;
    2, 3, 9, 6, 1, 2, 3;
    6, 9, 6, 1, 9, 9, 2;
    2, 1, 2, 3, 9, 6, 8;
    6, 9, 4, 5, 10, 6, 9;
    10, 3, 6, 2, 3, 4, 5]

private theorem xStep5 : xP4 * T2 = xP5 := by decide +kernel

private def xP6 : Mat := !![4, 3, 7, 4, 6, 8, 8;
    3, 3, 0, 2, 3, 4, 8;
    0, 3, 9, 3, 3, 8, 4;
    6, 2, 1, 10, 4, 8, 0;
    9, 4, 3, 0, 8, 3, 3;
    1, 8, 6, 1, 7, 0, 2;
    10, 0, 1, 6, 4, 9, 8]

private theorem xStep6 : xP5 * T1 = xP6 := by decide +kernel

@[expose] public def xMatrix : Mat := !![8, 9, 2, 7, 8, 4, 3;
    1, 3, 3, 7, 0, 3, 10;
    3, 10, 9, 3, 6, 9, 9;
    0, 2, 6, 2, 7, 3, 3;
    1, 6, 2, 7, 8, 3, 6;
    8, 10, 1, 10, 9, 9, 6;
    7, 1, 3, 4, 2, 4, 4]

private theorem xStep7 : xP6 * T2 = xMatrix := by decide +kernel

public theorem matrixValue_x : matrixValue x = xMatrix := by
  have h1 : matrixValue a * matrixValue (b ^ 1) = T1 := syllable1
  have h2 : matrixValue a * matrixValue (b ^ 2) = T2 := syllable2
  simp only [x, map_mul, h1, h2]
  rw [xStep1, xStep2, xStep3, xStep4, xStep5, xStep6, xStep7]

@[expose] public def y : Model := (a * b ^ 1) * (a * b ^ 1) * (a * b ^ 2) * (a * b ^ 1) * (a * b ^ 1) * (a * b ^ 2) * (a * b ^ 1) * (a * b ^ 1)

private def yP1 : Mat := !![2, 3, 10, 0, 10, 6, 7;
    4, 8, 8, 8, 0, 9, 3;
    8, 0, 5, 9, 1, 1, 4;
    0, 2, 10, 3, 6, 10, 7;
    3, 3, 4, 3, 4, 4, 5;
    3, 7, 0, 3, 2, 3, 8;
    3, 3, 2, 7, 3, 0, 8]

private theorem yStep1 : T1 * T1 = yP1 := by decide +kernel

private def yP2 : Mat := !![3, 5, 9, 2, 2, 1, 3;
    9, 10, 2, 6, 5, 9, 2;
    10, 3, 6, 9, 2, 2, 3;
    2, 5, 6, 5, 4, 1, 2;
    3, 9, 7, 10, 5, 3, 5;
    2, 3, 5, 9, 1, 10, 1;
    6, 7, 1, 2, 6, 5, 9]

private theorem yStep2 : yP1 * T2 = yP2 := by decide +kernel

private def yP3 : Mat := !![5, 5, 10, 6, 2, 7, 2;
    1, 8, 2, 2, 8, 5, 2;
    2, 9, 2, 6, 2, 1, 5;
    9, 10, 6, 9, 3, 8, 2;
    1, 9, 5, 4, 9, 5, 5;
    8, 3, 7, 6, 5, 2, 1;
    10, 9, 6, 1, 10, 3, 9]

private theorem yStep3 : yP2 * T1 = yP3 := by decide +kernel

private def yP4 : Mat := !![6, 9, 6, 3, 4, 4, 7;
    1, 5, 0, 7, 7, 0, 3;
    2, 2, 5, 6, 5, 10, 7;
    5, 4, 6, 6, 3, 0, 0;
    5, 9, 3, 4, 6, 4, 4;
    4, 3, 0, 4, 7, 3, 1;
    9, 4, 7, 2, 2, 5, 3]

private theorem yStep4 : yP3 * T1 = yP4 := by decide +kernel

private def yP5 : Mat := !![9, 1, 4, 8, 9, 0, 0;
    7, 3, 0, 8, 10, 4, 7;
    9, 1, 4, 5, 3, 0, 1;
    4, 2, 8, 1, 6, 8, 6;
    0, 1, 4, 7, 9, 2, 9;
    9, 3, 1, 5, 9, 2, 3;
    1, 3, 8, 9, 3, 10, 1]

private theorem yStep5 : yP4 * T2 = yP5 := by decide +kernel

private def yP6 : Mat := !![8, 6, 6, 7, 2, 4, 4;
    1, 7, 8, 7, 10, 3, 2;
    7, 5, 5, 8, 9, 10, 3;
    5, 2, 1, 6, 0, 3, 5;
    9, 8, 0, 2, 1, 1, 9;
    8, 8, 6, 7, 2, 2, 0;
    6, 1, 9, 5, 3, 7, 8]

private theorem yStep6 : yP5 * T1 = yP6 := by decide +kernel

@[expose] public def yMatrix : Mat := !![4, 1, 3, 7, 2, 7, 7;
    1, 8, 8, 7, 0, 3, 10;
    0, 2, 6, 9, 7, 8, 8;
    8, 1, 10, 10, 2, 9, 6;
    8, 2, 9, 7, 3, 4, 3;
    3, 1, 2, 3, 5, 9, 9;
    10, 6, 2, 4, 8, 8, 5]

private theorem yStep7 : yP6 * T1 = yMatrix := by decide +kernel

public theorem matrixValue_y : matrixValue y = yMatrix := by
  have h1 : matrixValue a * matrixValue (b ^ 1) = T1 := syllable1
  have h2 : matrixValue a * matrixValue (b ^ 2) = T2 := syllable2
  simp only [y, map_mul, h1, h2]
  rw [yStep1, yStep2, yStep3, yStep4, yStep5, yStep6, yStep7]

public theorem orderOf_five : orderOf (x * y) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply matrixValue_injective
    simp only [map_pow, map_mul, matrixValue_x, matrixValue_y, map_one]
    decide +kernel
  · intro h
    have hm := congrArg matrixValue h
    simp only [map_mul, matrixValue_x, matrixValue_y, map_one] at hm
    exact (by decide +kernel : xMatrix * yMatrix ≠ 1) hm

public theorem orderOf_eleven : orderOf (x * y ^ 2) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply matrixValue_injective
    simp only [map_pow, map_mul, matrixValue_x, matrixValue_y, map_one]
    decide +kernel
  · intro h
    have hm := congrArg matrixValue h
    simp only [map_mul, map_pow, matrixValue_x, matrixValue_y, map_one] at hm
    exact (by decide +kernel : xMatrix * yMatrix ^ 2 ≠ 1) hm

/-- The fixed subgroup whose 266 cosets will bound the model order. -/
@[expose] public def H : Subgroup Model := Subgroup.closure {x, y}

public theorem x_mem_H : x ∈ H := Subgroup.subset_closure (by simp)
public theorem y_mem_H : y ∈ H := Subgroup.subset_closure (by simp)

end Janko1.OrderCertificate
