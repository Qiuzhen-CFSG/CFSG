module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyRootCurves

/-!
# Explicit Weyl lifts for the G2 Chevalley carrier

This module constructs the two simple Weyl representatives in the closed G2
Chevalley carrier.  The representatives are the explicit root-curve words
`x_i(1) x_{-i}(1) x_i(1)`; the inverse representatives use the same word with
parameter `-1`.  Finite matrix calculations identify these words with the
certified integral Weyl matrices from `G2ChevalleyRepresentation`, then the
identities are specialized over an arbitrary commutative ring.

The torus normalization is checked by an explicit diagonal-matrix calculation
in the two simple-coroot coordinates.  The root-curve conjugation formula is a
direct consequence of the certified divided-power Weyl relation.  Both
arguments are characteristic-free, including characteristics two and three.
They use only the integral representation, the closed carrier, and the root
curve package; in particular they do not use root exhaustiveness,
semisimplicity, center results, or `theorem_1_10_3_d`.
-/

open scoped BigOperators Matrix

open Theory AlgebraicGroup

namespace Theory.AlgebraicGroup.G2Chevalley

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose] public section

/-- The certified simple Weyl matrix, packaged as a unit over any commutative ring. -/
public def weylMatrixUnit {R : Type*} [CommRing R] (i : Fin 2) :
    (Matrix Basis Basis R)ˣ where
  val := specialize (R := R) (weyl i)
  inv := specialize (R := R) (weylInv i)
  val_inv := by
    rw [← specialize_mul, weyl_mul_inv]
    ext a b
    simp [specialize, Matrix.one_apply]
  inv_val := by
    rw [← specialize_mul, weyl_inv_mul]
    ext a b
    simp [specialize, Matrix.one_apply]

/-- The root-curve word representing the simple Weyl reflection. -/
public def simpleWeylWord {R : Type*} [CommRing R] (i : Fin 2) :
    (Matrix Basis Basis R)ˣ :=
  rootCurveUnit (simpleRoot i) (1 : R) *
    rootCurveUnit (-simpleRoot i) (1 : R) *
    rootCurveUnit (simpleRoot i) (1 : R)

/-- The inverse root-curve word for the simple Weyl representative. -/
public def simpleWeylWordInv {R : Type*} [CommRing R] (i : Fin 2) :
    (Matrix Basis Basis R)ˣ :=
  rootCurveUnit (simpleRoot i) (-1 : R) *
    rootCurveUnit (-simpleRoot i) (-1 : R) *
    rootCurveUnit (simpleRoot i) (-1 : R)

private lemma rootCurve_one_specialize {R : Type*} [CommRing R]
    (r : Root) :
    rootCurve (R := R) r 1 =
      specialize (R := R) (rootCurve (R := ℤ) r 1) := by
  ext a b
  simp [rootCurve, specialize, Matrix.one_apply]

private lemma rootCurve_neg_one_specialize {R : Type*} [CommRing R]
    (r : Root) :
    rootCurve (R := R) r (-1) =
      specialize (R := R) (rootCurve (R := ℤ) r (-1)) := by
  ext a b
  simp [rootCurve, specialize, Matrix.one_apply]
  ring_nf

private lemma simpleWeylWord_val_specialize {R : Type*} [CommRing R]
    (i : Fin 2) :
    (simpleWeylWord (R := R) i).val =
      specialize (R := R) ((simpleWeylWord (R := ℤ) i).val) := by
  change rootCurve (simpleRoot i) (1 : R) *
        rootCurve (-simpleRoot i) (1 : R) *
        rootCurve (simpleRoot i) (1 : R) =
      specialize (R := R)
        (rootCurve (simpleRoot i) (1 : ℤ) *
          rootCurve (-simpleRoot i) (1 : ℤ) *
          rootCurve (simpleRoot i) (1 : ℤ))
  rw [specialize_mul, specialize_mul]
  rw [← rootCurve_one_specialize (R := R) (simpleRoot i),
    ← rootCurve_one_specialize (R := R) (-simpleRoot i)]

private lemma simpleWeylWordInv_val_specialize {R : Type*} [CommRing R]
    (i : Fin 2) :
    (simpleWeylWordInv (R := R) i).val =
      specialize (R := R) ((simpleWeylWordInv (R := ℤ) i).val) := by
  change rootCurve (simpleRoot i) (-1 : R) *
        rootCurve (-simpleRoot i) (-1 : R) *
        rootCurve (simpleRoot i) (-1 : R) =
      specialize (R := R)
        (rootCurve (simpleRoot i) (-1 : ℤ) *
          rootCurve (-simpleRoot i) (-1 : ℤ) *
          rootCurve (simpleRoot i) (-1 : ℤ))
  rw [specialize_mul, specialize_mul]
  rw [← rootCurve_neg_one_specialize (R := R) (simpleRoot i),
    ← rootCurve_neg_one_specialize (R := R) (-simpleRoot i)]

public theorem simpleWeylWord_val_eq_specialize_weyl {R : Type*} [CommRing R]
    (i : Fin 2) :
    (simpleWeylWord (R := R) i).val = specialize (R := R) (weyl i) := by
  rw [simpleWeylWord_val_specialize]
  congr 1
  fin_cases i <;> decide

public theorem simpleWeylWordInv_val_eq_specialize_weylInv
    {R : Type*} [CommRing R] (i : Fin 2) :
    (simpleWeylWordInv (R := R) i).val =
      specialize (R := R) (weylInv i) := by
  rw [simpleWeylWordInv_val_specialize]
  congr 1
  fin_cases i <;> decide

public theorem simpleWeylWord_eq_weylMatrixUnit {R : Type*} [CommRing R]
    (i : Fin 2) :
    simpleWeylWord (R := R) i = weylMatrixUnit (R := R) i := by
  apply Units.ext
  exact simpleWeylWord_val_eq_specialize_weyl i

public theorem simpleWeylWordInv_eq_weylMatrixUnit_inv
    {R : Type*} [CommRing R] (i : Fin 2) :
    simpleWeylWordInv (R := R) i = (weylMatrixUnit (R := R) i)⁻¹ := by
  apply Units.ext
  exact simpleWeylWordInv_val_eq_specialize_weylInv i

public theorem simpleWeylWord_mul_inv {R : Type*} [CommRing R] (i : Fin 2) :
    simpleWeylWord (R := R) i * simpleWeylWordInv (R := R) i = 1 := by
  rw [simpleWeylWord_eq_weylMatrixUnit,
    simpleWeylWordInv_eq_weylMatrixUnit_inv, mul_inv_cancel]

public theorem simpleWeylWordInv_mul {R : Type*} [CommRing R] (i : Fin 2) :
    simpleWeylWordInv (R := R) i * simpleWeylWord (R := R) i = 1 := by
  rw [simpleWeylWord_eq_weylMatrixUnit,
    simpleWeylWordInv_eq_weylMatrixUnit_inv, inv_mul_cancel]

private lemma specialize_weyl_dividedPower {R : Type*} [CommRing R]
    (i : Fin 2) (r : Root) (m : Fin 4) :
    specialize (R := R) (weylInv i) *
          specialize (R := R) (rootDividedPower r m) *
          specialize (R := R) (weyl i) =
      ((weylRootSign i r ^ m.val : ℤ) : R) •
        specialize (R := R) (rootDividedPower (simpleReflection i r) m) := by
  rw [← specialize_mul, ← specialize_mul, weyl_dividedPower, specialize_int_smul]

private lemma weylMatrixUnit_rootCurve_conjugation {R : Type*} [CommRing R]
    (i : Fin 2) (r : Root) (t : R) :
    specialize (R := R) (weylInv i) *
          rootCurve r t *
          specialize (R := R) (weyl i) =
      rootCurve (simpleReflection i r) ((weylRootSign i r : R) * t) := by
  have h0 := specialize_weyl_dividedPower (R := R) i r 0
  have h1 := specialize_weyl_dividedPower (R := R) i r 1
  have h2 := specialize_weyl_dividedPower (R := R) i r 2
  have h3 := specialize_weyl_dividedPower (R := R) i r 3
  have h0' :
      specialize (R := R) (weylInv i) * 1 * specialize (R := R) (weyl i) = 1 := by
    rw [mul_one, ← specialize_mul, weyl_inv_mul]
    ext a b
    simp [specialize, Matrix.one_apply]
  have h1' :
      specialize (R := R) (weylInv i) *
            specialize (R := R) (rootDividedPower r 1) *
            specialize (R := R) (weyl i) =
        (weylRootSign i r : R) •
          specialize (R := R) (rootDividedPower (simpleReflection i r) 1) := by
    simpa using h1
  have h2' :
      specialize (R := R) (weylInv i) *
            specialize (R := R) (rootDividedPower r 2) *
            specialize (R := R) (weyl i) =
        (weylRootSign i r : R) ^ 2 •
          specialize (R := R) (rootDividedPower (simpleReflection i r) 2) := by
    simpa [Int.cast_pow] using h2
  have h3' :
      specialize (R := R) (weylInv i) *
            specialize (R := R) (rootDividedPower r 3) *
            specialize (R := R) (weyl i) =
        (weylRootSign i r : R) ^ 3 •
          specialize (R := R) (rootDividedPower (simpleReflection i r) 3) := by
    simpa [Int.cast_pow] using h3
  simp only [rootCurve]
  rw [show specialize (R := R) (weylInv i) * (1 +
          t • specialize (R := R) (rootDividedPower r 1) +
          t ^ 2 • specialize (R := R) (rootDividedPower r 2) +
          t ^ 3 • specialize (R := R) (rootDividedPower r 3)) *
          specialize (R := R) (weyl i) =
        specialize (R := R) (weylInv i) * 1 * specialize (R := R) (weyl i) +
          t • (specialize (R := R) (weylInv i) *
            specialize (R := R) (rootDividedPower r 1) *
            specialize (R := R) (weyl i)) +
          t ^ 2 • (specialize (R := R) (weylInv i) *
            specialize (R := R) (rootDividedPower r 2) *
            specialize (R := R) (weyl i)) +
          t ^ 3 • (specialize (R := R) (weylInv i) *
            specialize (R := R) (rootDividedPower r 3) *
            specialize (R := R) (weyl i)) by
      noncomm_ring]
  rw [h0', h1', h2', h3']
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf

public theorem weylMatrixUnit_rootCurveUnit_conjugation
    {R : Type*} [CommRing R] (i : Fin 2) (r : Root) (t : R) :
    (weylMatrixUnit i)⁻¹ * rootCurveUnit r t * weylMatrixUnit i =
      rootCurveUnit (simpleReflection i r) ((weylRootSign i r : R) * t) := by
  apply Units.ext
  exact weylMatrixUnit_rootCurve_conjugation i r t

/-- Simple-reflection action on the two split-torus coordinates. -/
public def simpleReflectionTorusParameter {R : Type*} [CommRing R]
    (i : Fin 2) (u : TorusParameter R) : TorusParameter R :=
  fun j =>
    match i, j with
    | 0, 0 => (u 0)⁻¹ * u 1
    | 0, 1 => u 1
    | 1, 0 => u 0
    | 1, 1 => (u 0) ^ 3 * (u 1)⁻¹

private lemma basisTorusUnit_simpleReflectionTorusParameter {R : Type*} [CommRing R]
    (i : Fin 2) (u : TorusParameter R) (b : Basis) :
    basisTorusUnit (simpleReflectionTorusParameter i u) b =
      match basisRoot b with
      | none => 1
      | some r => basisTorusUnit u (rootBasis (simpleReflection i r)) := by
  fin_cases i <;> fin_cases b <;>
    simp [basisTorusUnit, basisWeight, basisRoot, rootBasis,
      Root.pairingSimple, Root.coord, simpleReflectionTorusParameter,
      simpleReflection, zpow_neg, mul_assoc, mul_left_comm, mul_comm] <;>
    simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

private lemma basisTorusUnit_simpleReflectionTorusParameter_val
    {R : Type*} [CommRing R] (i : Fin 2) (u : TorusParameter R) (r : Root) :
    (basisTorusUnit (simpleReflectionTorusParameter i u) (rootBasis r) : R) =
      (basisTorusUnit u (rootBasis (simpleReflection i r)) : R) := by
  have h := basisTorusUnit_simpleReflectionTorusParameter i u (rootBasis r)
  fin_cases r <;>
    simpa [basisRoot, rootBasis] using
      congrArg Units.val h

set_option linter.unusedSimpArgs false

private lemma weylInv_diagonal_weyl_eq_aux0_row0 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 0 b =
      Matrix.diagonal d' 0 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row1 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 1 b =
      Matrix.diagonal d' 1 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row2 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 2 b =
      Matrix.diagonal d' 2 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row3 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 3 b =
      Matrix.diagonal d' 3 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row4 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 4 b =
      Matrix.diagonal d' 4 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row5 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 5 b =
      Matrix.diagonal d' 5 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row6 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 6 b =
      Matrix.diagonal d' 6 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row7 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 7 b =
      Matrix.diagonal d' 7 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row8 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 8 b =
      Matrix.diagonal d' 8 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row9 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 9 b =
      Matrix.diagonal d' 9 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row10 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 10 b =
      Matrix.diagonal d' 10 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row11 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 11 b =
      Matrix.diagonal d' 11 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row12 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 12 b =
      Matrix.diagonal d' 12 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux0_row13 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) (b : Basis) :
    (specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0)) 13 b =
      Matrix.diagonal d' 13 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private theorem weylInv_diagonal_weyl_eq_aux0 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 0 r))) :
    specialize (R := R) (weylInv 0) * Matrix.diagonal d *
        specialize (R := R) (weyl 0) =
      Matrix.diagonal d' := by
  ext a b
  fin_cases a
  · exact weylInv_diagonal_weyl_eq_aux0_row0 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row1 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row2 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row3 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row4 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row5 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row6 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row7 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row8 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row9 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row10 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row11 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row12 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux0_row13 d d' hcartan hcartan' hroot b

private lemma weylInv_diagonal_weyl_eq_aux1_row0 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 0 b =
      Matrix.diagonal d' 0 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row1 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 1 b =
      Matrix.diagonal d' 1 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row2 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 2 b =
      Matrix.diagonal d' 2 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row3 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 3 b =
      Matrix.diagonal d' 3 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row4 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 4 b =
      Matrix.diagonal d' 4 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row5 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 5 b =
      Matrix.diagonal d' 5 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row6 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 6 b =
      Matrix.diagonal d' 6 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row7 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 7 b =
      Matrix.diagonal d' 7 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row8 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 8 b =
      Matrix.diagonal d' 8 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row9 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 9 b =
      Matrix.diagonal d' 9 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row10 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 10 b =
      Matrix.diagonal d' 10 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row11 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 11 b =
      Matrix.diagonal d' 11 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row12 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 12 b =
      Matrix.diagonal d' 12 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private lemma weylInv_diagonal_weyl_eq_aux1_row13 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) (b : Basis) :
    (specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1)) 13 b =
      Matrix.diagonal d' 13 b := by
  have hd0 : d 0 = 1 := by simpa [cartanBasis] using hcartan 0
  have hd1 : d 1 = 1 := by simpa [cartanBasis] using hcartan 1
  have hd0' : d' 0 = 1 := by simpa [cartanBasis] using hcartan' 0
  have hd1' : d' 1 = 1 := by simpa [cartanBasis] using hcartan' 1
  have hr0 : d' 2 = d 4 := by simpa [rootBasis, simpleReflection] using hroot 0
  have hr1 : d' 3 = d 9 := by simpa [rootBasis, simpleReflection] using hroot 1
  have hr2 : d' 4 = d 2 := by simpa [rootBasis, simpleReflection] using hroot 2
  have hr3 : d' 5 = d 5 := by simpa [rootBasis, simpleReflection] using hroot 3
  have hr4 : d' 6 = d 7 := by simpa [rootBasis, simpleReflection] using hroot 4
  have hr5 : d' 7 = d 6 := by simpa [rootBasis, simpleReflection] using hroot 5
  have hr6 : d' 8 = d 10 := by simpa [rootBasis, simpleReflection] using hroot 6
  have hr7 : d' 9 = d 3 := by simpa [rootBasis, simpleReflection] using hroot 7
  have hr8 : d' 10 = d 8 := by simpa [rootBasis, simpleReflection] using hroot 8
  have hr9 : d' 11 = d 11 := by simpa [rootBasis, simpleReflection] using hroot 9
  have hr10 : d' 12 = d 13 := by simpa [rootBasis, simpleReflection] using hroot 10
  have hr11 : d' 13 = d 12 := by simpa [rootBasis, simpleReflection] using hroot 11
  rw [Matrix.mul_apply]
  fin_cases b <;>
    simp [Fin.sum_univ_succ, hd0, hd1, hd0', hd1', hr0, hr1, hr2,
      hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, specialize,
      weyl, weylInv, weylEntries, weylInvEntries, matrixOfEntries,
      Matrix.mul_diagonal]

private theorem weylInv_diagonal_weyl_eq_aux1 {R : Type*} [CommRing R]
    (d d' : Basis → R)
    (hcartan : ∀ j : Fin 2, d (cartanBasis j) = 1)
    (hcartan' : ∀ j : Fin 2, d' (cartanBasis j) = 1)
    (hroot : ∀ r : Root, d' (rootBasis r) =
      d (rootBasis (simpleReflection 1 r))) :
    specialize (R := R) (weylInv 1) * Matrix.diagonal d *
        specialize (R := R) (weyl 1) =
      Matrix.diagonal d' := by
  ext a b
  fin_cases a
  · exact weylInv_diagonal_weyl_eq_aux1_row0 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row1 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row2 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row3 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row4 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row5 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row6 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row7 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row8 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row9 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row10 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row11 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row12 d d' hcartan hcartan' hroot b
  · exact weylInv_diagonal_weyl_eq_aux1_row13 d d' hcartan hcartan' hroot b

set_option linter.unusedSimpArgs true

private lemma basisTorusUnit_cartan_val {R : Type*} [CommRing R]
    (u : TorusParameter R) (j : Fin 2) :
    (basisTorusUnit u (cartanBasis j) : R) = 1 := by
  fin_cases j <;>
    simp [basisTorusUnit, basisWeight, basisRoot, cartanBasis]

public theorem weylMatrixUnit_torusElement_conjugation
    {R : Type*} [CommRing R] (i : Fin 2) (u : TorusParameter R) :
    (weylMatrixUnit i)⁻¹ * torusElement u * weylMatrixUnit i =
      torusElement (simpleReflectionTorusParameter i u) := by
  apply Units.ext
  change specialize (R := R) (weylInv i) *
        Matrix.diagonal (fun b : Basis => (basisTorusUnit u b : R)) *
        specialize (R := R) (weyl i) =
      Matrix.diagonal
        (fun b : Basis =>
          (basisTorusUnit (simpleReflectionTorusParameter i u) b : R))
  fin_cases i
  · apply weylInv_diagonal_weyl_eq_aux0
    · intro j
      exact basisTorusUnit_cartan_val u j
    · intro j
      exact basisTorusUnit_cartan_val (simpleReflectionTorusParameter 0 u) j
    · intro r
      exact basisTorusUnit_simpleReflectionTorusParameter_val 0 u r
  · apply weylInv_diagonal_weyl_eq_aux1
    · intro j
      exact basisTorusUnit_cartan_val u j
    · intro j
      exact basisTorusUnit_cartan_val (simpleReflectionTorusParameter 1 u) j
    · intro r
      exact basisTorusUnit_simpleReflectionTorusParameter_val 1 u r

private noncomputable def ambientRepresentationPointHom :
    LinearMap.GeneralLinearGroup k (Basis → k) →*
      Variety.Point (Ambient k) where
  toFun g := generalLinearRepresentationPoint (carrierBasis (k := k)) g
  map_one' := by
    simpa [Ambient, glVarietyOf] using
      generalLinearRepresentationPoint_one (carrierBasis (k := k))
  map_mul' g h := by
    simpa [Ambient, glVarietyOf] using
      generalLinearRepresentationPoint_mul (carrierBasis (k := k)) g h

private lemma rootMorphism_ambient_point (r : Root) (a : k) :
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        ((rootMorphism r).onPoints (kPlusPoint a)) =
      ambientRepresentationPointHom
        (Matrix.GeneralLinearGroup.toLin (rootCurveUnit r a)) := by
  rw [rootMorphism_inclusion_apply, rootAmbientMorphism_apply]
  rfl

private lemma splitTorus_ambient_point
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        ((splitTorus (k := k)).includePoint s) =
      ambientRepresentationPointHom
        (Matrix.GeneralLinearGroup.toLin
          (torusElement
            (dPointEquiv 2 ((splitTorusIso (k := k)).inv.onPoints s)))) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  exact splitTorus_inclusion_torusElement_apply s

/-- The carrier point `x_i(1) x_{-i}(1) x_i(1)` lifting a simple reflection. -/
public noncomputable def carrierWeylRepresentative (i : Fin 2) :
    Variety.Point (Carrier (k := k)) :=
  (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint (1 : k)) *
    (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint (1 : k)) *
    (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint (1 : k))

/-- The inverse carrier Weyl representative, written with parameter `-1`. -/
public noncomputable def carrierWeylRepresentativeInv (i : Fin 2) :
    Variety.Point (Carrier (k := k)) :=
  (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint (-1 : k)) *
    (rootMorphism (k := k) (-simpleRoot i)).onPoints (kPlusPoint (-1 : k)) *
    (rootMorphism (k := k) (simpleRoot i)).onPoints (kPlusPoint (-1 : k))

public theorem carrierWeylRepresentative_ambient_matrix (i : Fin 2) :
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        (carrierWeylRepresentative (k := k) i) =
      generalLinearRepresentationPoint (carrierBasis (k := k))
        (Matrix.GeneralLinearGroup.toLin (weylMatrixUnit (R := k) i)) := by
  simp only [carrierWeylRepresentative, map_mul, rootMorphism_ambient_point]
  let ρ := ambientRepresentationPointHom (k := k)
  change ρ _ * ρ _ * ρ _ = ρ _
  rw [← ρ.map_mul, ← ρ.map_mul]
  congr 1
  simpa [simpleWeylWord, map_mul] using
    congrArg Matrix.GeneralLinearGroup.toLin
      (simpleWeylWord_eq_weylMatrixUnit (R := k) i)

public theorem carrierWeylRepresentativeInv_ambient_matrix (i : Fin 2) :
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        (carrierWeylRepresentativeInv (k := k) i) =
      generalLinearRepresentationPoint (carrierBasis (k := k))
        (Matrix.GeneralLinearGroup.toLin ((weylMatrixUnit (R := k) i)⁻¹)) := by
  simp only [carrierWeylRepresentativeInv, map_mul, rootMorphism_ambient_point]
  let ρ := ambientRepresentationPointHom (k := k)
  change ρ _ * ρ _ * ρ _ = ρ _
  rw [← ρ.map_mul, ← ρ.map_mul]
  congr 1
  simpa [simpleWeylWordInv, map_mul] using
    congrArg Matrix.GeneralLinearGroup.toLin
      (simpleWeylWordInv_eq_weylMatrixUnit_inv (R := k) i)

public theorem carrierWeylRepresentative_inv (i : Fin 2) :
    (carrierWeylRepresentative (k := k) i)⁻¹ =
      carrierWeylRepresentativeInv (k := k) i := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  simp only [map_inv]
  rw [carrierWeylRepresentative_ambient_matrix,
    carrierWeylRepresentativeInv_ambient_matrix]
  let ρ := ambientRepresentationPointHom (k := k)
  change (ρ _)⁻¹ = ρ _
  simp only [map_inv]

public theorem carrierWeylRepresentativeInv_inv (i : Fin 2) :
    (carrierWeylRepresentativeInv (k := k) i)⁻¹ =
      carrierWeylRepresentative (k := k) i := by
  rw [← carrierWeylRepresentative_inv, inv_inv]

public theorem carrierWeylRepresentative_mul_inv (i : Fin 2) :
    carrierWeylRepresentative (k := k) i *
        carrierWeylRepresentativeInv (k := k) i = 1 := by
  rw [← carrierWeylRepresentative_inv, mul_inv_cancel]

public theorem carrierWeylRepresentativeInv_mul (i : Fin 2) :
    carrierWeylRepresentativeInv (k := k) i *
        carrierWeylRepresentative (k := k) i = 1 := by
  rw [← carrierWeylRepresentative_inv, inv_mul_cancel]

/-- The split-torus point obtained by applying the simple reflection to
the two torus coordinates. -/
public noncomputable def simpleReflectionTorusPoint (i : Fin 2)
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    Variety.Point (splitTorus (k := k)).carrierVariety := by
  letI := (splitTorus (k := k)).carrierAlgebraicGroup
  exact (splitTorusIso (k := k)).hom.onPoints
    ((dPointEquiv 2).symm
      (simpleReflectionTorusParameter i
        (dPointEquiv 2 ((splitTorusIso (k := k)).inv.onPoints s))))

private lemma simpleReflectionTorusPoint_ambient (i : Fin 2)
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        ((splitTorus (k := k)).includePoint
          (simpleReflectionTorusPoint (k := k) i s)) =
      ambientRepresentationPointHom
        (Matrix.GeneralLinearGroup.toLin
          (torusElement
            (simpleReflectionTorusParameter i
              (dPointEquiv 2 ((splitTorusIso (k := k)).inv.onPoints s))))) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  rw [splitTorus_ambient_point]
  change ambientRepresentationPointHom
        (Matrix.GeneralLinearGroup.toLin
          (torusElement
            (dPointEquiv 2
              ((splitTorusIso (k := k)).inv.onPoints
                ((splitTorusIso (k := k)).hom.onPoints
                  ((dPointEquiv 2).symm
                    (simpleReflectionTorusParameter i
                      (dPointEquiv 2
                        ((splitTorusIso (k := k)).inv.onPoints s))))))))) =
      ambientRepresentationPointHom
        (Matrix.GeneralLinearGroup.toLin
          (torusElement
            (simpleReflectionTorusParameter i
              (dPointEquiv 2 ((splitTorusIso (k := k)).inv.onPoints s)))))
  rw [(splitTorusIso (k := k)).hom_inv_id]
  simp

public theorem carrierWeylRepresentative_splitTorus_conjugation
    (i : Fin 2) (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (carrierWeylRepresentative (k := k) i)⁻¹ *
        (splitTorus (k := k)).includePoint s *
        carrierWeylRepresentative (k := k) i =
      (splitTorus (k := k)).includePoint
        (simpleReflectionTorusPoint (k := k) i s) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  simp only [map_mul, map_inv]
  rw [carrierWeylRepresentative_ambient_matrix, splitTorus_ambient_point,
    simpleReflectionTorusPoint_ambient]
  let ρ := ambientRepresentationPointHom (k := k)
  change (ρ _)⁻¹ * ρ _ * ρ _ = ρ _
  rw [← ρ.map_inv, ← ρ.map_mul, ← ρ.map_mul]
  congr 1
  simpa only [map_mul, map_inv] using
    congrArg Matrix.GeneralLinearGroup.toLin
      (weylMatrixUnit_torusElement_conjugation (R := k) i
        (dPointEquiv 2 ((splitTorusIso (k := k)).inv.onPoints s)))

public theorem carrierWeylRepresentative_rootMorphism_conjugation
    (i : Fin 2) (r : Root) (a : k) :
    (carrierWeylRepresentative (k := k) i)⁻¹ *
        (rootMorphism (k := k) r).onPoints (kPlusPoint a) *
        carrierWeylRepresentative (k := k) i =
      (rootMorphism (k := k) (simpleReflection i r)).onPoints
        (kPlusPoint ((weylRootSign i r : k) * a)) := by
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  simp only [map_mul, map_inv]
  rw [carrierWeylRepresentative_ambient_matrix, rootMorphism_ambient_point,
    rootMorphism_ambient_point]
  let ρ := ambientRepresentationPointHom (k := k)
  change (ρ _)⁻¹ * ρ _ * ρ _ = ρ _
  rw [← ρ.map_inv, ← ρ.map_mul, ← ρ.map_mul]
  congr 1
  simpa only [map_mul, map_inv] using
    congrArg Matrix.GeneralLinearGroup.toLin
      (weylMatrixUnit_rootCurveUnit_conjugation (R := k) i r a)

end

end Theory.AlgebraicGroup.G2Chevalley
