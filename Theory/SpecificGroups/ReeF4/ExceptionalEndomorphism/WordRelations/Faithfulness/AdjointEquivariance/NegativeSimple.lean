module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.Construction
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.RoutedCurves

/-!
# Opposition and negative-simple adjoint equivariance

The specialized integral omega matrix fixes the Cartan coordinates and exchanges
opposite root coordinates. In characteristic two it commutes with every Tits
word: this follows on Cartan coordinates from the simple-reflection formula,
and on root coordinates from disappearance of the integral signs and commutation
of reflections with root negation. Opposite routed operators use the same
positive route, so omega conjugates each actual root operator to its opposite.
On Cartan operators it exchanges the two simple factors of the commutator;
the resulting minus sign also disappears in characteristic two.

Consequently the fixed `adjointMap` is omega-equivariant on every coordinate.
The defining integral divided-power identity then conjugates each positive
simple curve to the negative simple curve, including every cubic coefficient.
`negative_simple_equivariant_of_positive` has exactly positive-simple
equivariance for this same map as its premise. The all-root assembly owner
must supply that independent result.

The sources are Geck's integral construction as implemented in
`IntegralGeckConstruction`, the common positive route in
`IntegralAllRootOperators`, and the polynomial curves in `SimpleGeckGroup`.
No comparison of independently chosen routes is needed.
-/

@[expose] public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup

namespace ReeF4.WordRelations.Faithfulness.Adjoint
noncomputable section
variable {K : Type*} [CommRing K]

/-- The actual specialized integral omega matrix, with itself as inverse. -/
def omegaUnit : (Matrix Coordinate Coordinate K)ˣ where
  val := (omegaMatrix (P := typeF4RootPairing) (b := typeF4RootPairing_base)).map
    (Int.castRingHom K)
  inv := (omegaMatrix (P := typeF4RootPairing) (b := typeF4RootPairing_base)).map
    (Int.castRingHom K)
  val_inv := by rw [← Matrix.map_mul, omegaMatrix_sq]; simp
  inv_val := by rw [← Matrix.map_mul, omegaMatrix_sq]; simp

/-- The matrix underlying the opposition unit. -/
lemma omegaUnit_val : (omegaUnit (K := K) : Matrix Coordinate Coordinate K) =
    (omegaMatrix (P := typeF4RootPairing) (b := typeF4RootPairing_base)).map
      (Int.castRingHom K) := rfl

/-- The inverse unit has the same underlying involution. -/
lemma omegaUnit_inv_val : (↑(omegaUnit (K := K))⁻¹ : Matrix Coordinate Coordinate K) =
    (omegaUnit (K := K) : Matrix Coordinate Coordinate K) := rfl

/-- Opposition squares to the identity after specialization. -/
lemma omegaUnit_mul_self : (omegaUnit (K := K) : Matrix Coordinate Coordinate K) *
    (omegaUnit (K := K) : Matrix Coordinate Coordinate K) = 1 := (omegaUnit (K := K)).val_inv

private lemma cast_mulVec (A : Matrix Coordinate Coordinate ℤ) (v : Coordinate → ℤ) :
    (Int.castRingHom K) ∘ (A *ᵥ v) =
      A.map (Int.castRingHom K) *ᵥ ((Int.castRingHom K) ∘ v) := by
  ext i
  exact (Int.castRingHom K).map_mulVec A v i

private lemma cast_single (j : Coordinate) :
    (Int.castRingHom K) ∘ (Pi.single j (1 : ℤ)) = Pi.single j 1 := by
  classical
  ext i
  simp [Pi.single_apply]

/-- Opposition fixes each Cartan coordinate. -/
lemma omegaUnit_mulVec_cartan (j : typeF4RootPairing_base.support) :
    (omegaUnit (K := K) : Matrix Coordinate Coordinate K) *ᵥ Pi.single (Sum.inl j) 1 =
      Pi.single (Sum.inl j) 1 := by
  have h := congrArg (fun v : Coordinate → ℤ => (Int.castRingHom K) ∘ v)
    (omegaMatrix_mulVec_u (P := typeF4RootPairing) j)
  simpa only [cast_mulVec, u, cast_single, omegaUnit_val] using h

/-- Opposition exchanges each pair of opposite root coordinates. -/
lemma omegaUnit_mulVec_root (r : typeF4Roots) :
    let := typeF4RootPairing.indexNeg
    (omegaUnit (K := K) : Matrix Coordinate Coordinate K) *ᵥ Pi.single (Sum.inr r) 1 =
      Pi.single (Sum.inr (-r)) 1 := by
  let := typeF4RootPairing.indexNeg
  have h := congrArg (fun v : Coordinate → ℤ => (Int.castRingHom K) ∘ v)
    (omegaMatrix_mulVec_v (P := typeF4RootPairing) (b := typeF4RootPairing_base) r)
  simpa only [cast_mulVec, v, cast_single, omegaUnit_val] using h

private lemma cast_sub (v w : Coordinate → ℤ) :
    (Int.castRingHom K) ∘ (v - w) =
      (Int.castRingHom K) ∘ v - (Int.castRingHom K) ∘ w := by ext i; simp

private lemma cast_smul (z : ℤ) (v : Coordinate → ℤ) :
    (Int.castRingHom K) ∘ (z • v) = (z : K) • ((Int.castRingHom K) ∘ v) := by
  ext i
  simp

private lemma titsUnit_mulVec_cartan (i j : typeF4RootPairing_base.support) :
    (titsUnit (K := K) i : Matrix Coordinate Coordinate K) *ᵥ Pi.single (Sum.inl j) 1 =
      Pi.single (Sum.inl j) 1 -
        (|typeF4RootPairing_base.cartanMatrix i j| : ℤ) •
          (Pi.single (Sum.inl i) (1 : K)) := by
  have h := congrArg (fun v : Coordinate → ℤ => (Int.castRingHom K) ∘ v)
    (titsLift_mulVec_u (P := typeF4RootPairing) i j)
  simpa only [cast_mulVec, cast_sub, cast_smul, u, cast_single, titsUnit_val,
    Int.cast_smul_eq_zsmul] using h

private lemma titsUnit_mulVec_root [CharP K 2]
    (i : typeF4RootPairing_base.support) (r : typeF4Roots) :
    (titsUnit (K := K) i : Matrix Coordinate Coordinate K) *ᵥ Pi.single (Sum.inr r) 1 =
      Pi.single (Sum.inr (typeF4RootPairing.reflectionPerm i r)) 1 := by
  have h := congrArg (fun v : Coordinate → ℤ => (Int.castRingHom K) ∘ v)
    (titsLift_mulVec_v (P := typeF4RootPairing) i r)
  simpa only [cast_mulVec, cast_smul, v, cast_single, titsUnit_val,
    Int.cast_pow, Int.cast_neg, Int.cast_one, CharTwo.neg_eq, one_pow, one_smul] using h

/-- In characteristic two, a simple Tits lift commutes with opposition. -/
lemma omegaUnit_commute_titsUnit [CharP K 2] (i : typeF4RootPairing_base.support) :
    Commute (omegaUnit (K := K)) (titsUnit i) := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  rintro (j | r)
  · change ((omegaUnit (K := K) : Matrix Coordinate Coordinate K) * (titsUnit (K := K) i : Matrix Coordinate Coordinate K)) *ᵥ _ =
      ((titsUnit (K := K) i : Matrix Coordinate Coordinate K) * (omegaUnit (K := K) : Matrix Coordinate Coordinate K)) *ᵥ _
    simp only [← Matrix.mulVec_mulVec, titsUnit_mulVec_cartan, Matrix.mulVec_sub,
      Matrix.mulVec_smul, omegaUnit_mulVec_cartan]
  · let := typeF4RootPairing.indexNeg
    change ((omegaUnit (K := K) : Matrix Coordinate Coordinate K) * (titsUnit (K := K) i : Matrix Coordinate Coordinate K)) *ᵥ _ =
      ((titsUnit (K := K) i : Matrix Coordinate Coordinate K) * (omegaUnit (K := K) : Matrix Coordinate Coordinate K)) *ᵥ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, titsUnit_mulVec_root,
      omegaUnit_mulVec_root, omegaUnit_mulVec_root, titsUnit_mulVec_root]
    have hn := reflectionWord_neg (P := typeF4RootPairing) [i] r
    simpa only [reflectionWord] using congrArg (fun r : typeF4Roots =>
      (Pi.single (Sum.inr r : Coordinate) (1 : K) : Coordinate → K)) hn.symm

/-- Opposition commutes with the actual specialized Tits word. -/
lemma omegaUnit_commute_titsWordUnit [CharP K 2]
    (w : List typeF4RootPairing_base.support) :
    Commute (omegaUnit (K := K)) (titsWordUnit w) := by
  induction w with
  | nil => exact Commute.one_right _
  | cons i w ih => exact (omegaUnit_commute_titsUnit i).mul_right ih

/-- Opposition exchanges the positive and negative simple operators. -/
lemma omegaUnit_mul_eMatrix (i : typeF4RootPairing_base.support) :
    (omegaUnit (K := K) : Matrix Coordinate Coordinate K) *
      (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom K) =
    (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom K) *
      (omegaUnit (K := K) : Matrix Coordinate Coordinate K) := by
  simp only [omegaUnit_val, ← Matrix.map_mul, omegaMatrix_mul_eMatrix]

/-- The reverse simple-operator exchange. -/
lemma omegaUnit_mul_fMatrix (i : typeF4RootPairing_base.support) :
    (omegaUnit (K := K) : Matrix Coordinate Coordinate K) *
      (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom K) =
    (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom K) *
      (omegaUnit (K := K) : Matrix Coordinate Coordinate K) := by
  simp only [omegaUnit_val, ← Matrix.map_mul, omegaMatrix_mul_fMatrix]

private lemma omegaUnit_conj_rootOperator_pos [CharP K 2]
    (r : typeF4Roots) (hr : typeF4RootPairing_base.IsPos r) :
    let := typeF4RootPairing.indexNeg
    (omegaUnit (K := K) : Matrix Coordinate Coordinate K) *
      (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).map
        (Int.castRingHom K) * (omegaUnit (K := K) : Matrix Coordinate Coordinate K) =
      (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)).map
        (Int.castRingHom K) := by
  let := typeF4RootPairing.indexNeg
  let w := (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word
  let i := (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).simple
  let O : Matrix Coordinate Coordinate K := omegaUnit (K := K)
  let T : Matrix Coordinate Coordinate K := titsWordUnit (K := K) w
  let U : Matrix Coordinate Coordinate K := ↑(titsWordUnit (K := K) w)⁻¹
  let E := (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom K)
  let F := (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom K)
  have hT : O * T = T * O := congrArg Units.val (omegaUnit_commute_titsWordUnit w).eq
  have hU : O * U = U * O :=
    congrArg Units.val (omegaUnit_commute_titsWordUnit w).inv_right.eq
  have hE : O * E = F * O := omegaUnit_mul_eMatrix i
  have hOO : O * O = 1 := omegaUnit_mul_self
  change O * (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).map
    (Int.castRingHom K) * O =
    (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)).map
      (Int.castRingHom K)
  rw [rootOperator_of_pos r hr, rootOperator_neg_of_pos r hr]
  simp only [transportedMatrix, Matrix.map_mul]
  rw [← titsWordUnit_val, ← titsWordUnit_inv_val]
  change O * (T * E * U) * O = T * F * U
  calc
    O * (T * E * U) * O = T * (O * E) * U * O := by
      simp only [← mul_assoc]
      rw [hT]
    _ = T * (F * O) * U * O := by rw [hE]
    _ = T * F * (O * U) * O := by simp only [mul_assoc]
    _ = T * F * (U * O) * O := by rw [hU]
    _ = T * F * U := by simp only [mul_assoc, hOO, mul_one]

/-- Opposition conjugates every actual routed root operator to its opposite. -/
lemma omegaUnit_conj_rootOperator [CharP K 2] (r : typeF4Roots) :
    let := typeF4RootPairing.indexNeg
    (omegaUnit (K := K) : Matrix Coordinate Coordinate K) *
      (F4Chevalley.integralOperators.rootOperator r).map (Int.castRingHom K) *
        (omegaUnit (K := K) : Matrix Coordinate Coordinate K) =
      (F4Chevalley.integralOperators.rootOperator (-r)).map (Int.castRingHom K) := by
  let := typeF4RootPairing.indexNeg
  by_cases hr : typeF4RootPairing_base.IsPos r
  · exact omegaUnit_conj_rootOperator_pos r hr
  · have hn : typeF4RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr
    have h := omegaUnit_conj_rootOperator_pos (K := K) (-r) hn
    simp only [neg_neg] at h
    change (omegaUnit (K := K) : Matrix Coordinate Coordinate K) *
      (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).map
        (Int.castRingHom K) * (omegaUnit (K := K) : Matrix Coordinate Coordinate K) = _
    rw [← h]
    simp only [← mul_assoc, omegaUnit_mul_self, one_mul]
    simp only [mul_assoc, omegaUnit_mul_self, mul_one]
    rfl

/-- The simple Cartan commutators commute with opposition in characteristic two. -/
lemma omegaUnit_commute_cartanOperator (m : ℕ) (i : typeF4RootPairing_base.support) :
    Commute (omegaUnit (K := CoefficientField m) :
      Matrix Coordinate Coordinate (CoefficientField m)) (coordinateOperator m (Sum.inl i)) := by
  let O : Matrix Coordinate Coordinate (CoefficientField m) := omegaUnit (K := CoefficientField m)
  let E := (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m))
  let F := (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m))
  have hE : O * E = F * O := omegaUnit_mul_eMatrix i
  have hF : O * F = E * O := omegaUnit_mul_fMatrix i
  change O * (E * F - F * E) = (E * F - F * E) * O
  rw [Matrix.mul_sub, ← mul_assoc, ← mul_assoc, hE, hF]
  rw [mul_assoc F, mul_assoc E, hF, hE]
  rw [Matrix.sub_mul]
  ext x y
  simp only [Matrix.sub_apply, CharTwo.sub_eq_add, mul_assoc, add_comm]

/-- The fixed adjoint map is equivariant under the actual omega involution. -/
theorem omega_equivariant (m : ℕ) :
    Equivariant (adjointMap m) (omegaUnit (K := CoefficientField m)) := by
  apply (equivariant_iff_basis (adjointMap m) _).mpr
  rintro (i | r)
  · rw [omegaUnit_mulVec_cartan, adjointMap_single]
    exact (omegaUnit_commute_cartanOperator m i).eq.symm
  · let := typeF4RootPairing.indexNeg
    rw [omegaUnit_mulVec_root, adjointMap_root_single, adjointMap_root_single]
    rw [← omegaUnit_conj_rootOperator]
    simp only [mul_assoc, omegaUnit_mul_self, mul_one]

/-- The full negative polynomial curve is the omega conjugate of the positive curve. -/
lemma negativeUnit_eq_omega_conjugate (i : typeF4RootPairing_base.support) (t : K) :
    negativeUnit i t = omegaUnit * positiveUnit i t * omegaUnit⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, omegaUnit_inv_val, positiveUnit_val, negativeUnit_val,
    positiveMatrix_formula, negativeMatrix_formula, fDividedPower, Matrix.map_mul]
  have hOO := omegaUnit_mul_self (K := K)
  rw [omegaUnit_val] at hOO
  simp only [omegaUnit_val, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, mul_one, hOO]

/-- Negative-simple equivariance follows from positive-simple equivariance for
exactly the same adjoint map. The parent assembly must discharge this premise. -/
theorem negative_simple_equivariant_of_positive (m : ℕ)
    (he : ∀ (i : typeF4RootPairing_base.support) (t : CoefficientField m),
      Equivariant (adjointMap m) (positiveUnit i t))
    (i : typeF4RootPairing_base.support) (t : CoefficientField m) :
    Equivariant (adjointMap m) (negativeUnit i t) := by
  rw [negativeUnit_eq_omega_conjugate]
  exact equivariant_conjugate (adjointMap m) _ _ (omega_equivariant m) (he i t)

end
end ReeF4.WordRelations.Faithfulness.Adjoint
