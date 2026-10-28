module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Geometry
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.RootColumns

/-!
# Cartan columns and Cartan kernel detection for the F4 operators

The actual integral Geck operators send a Cartan basis vector to the root
vector with coefficient equal to the root-coroot pairing after specialization
in characteristic two. We prove this along the defining canonical Tits routes:
integral signs disappear, and the inverse simple Tits lift on Cartan vectors
implements the reflection formula for the pairing. This works for every root.

For a vector with zero root coordinates, annihilation by the short operators
therefore gives four scalar equations from the roots e₁, e₂, e₃ and
(e₁ + e₂ + e₃ + e₄) / 2. Their explicitly evaluated pairing rows eliminate all
four Cartan coordinates. The root-coordinate hypothesis remains explicit for
the separate common-kernel assembly.

Sources: the simple Cartan and Tits formulas in `IntegralGeckConstruction`,
the canonical routes in `IntegralAllRootOperators` (Geck's integral
construction; Steinberg, *Lectures on Chevalley Groups*), and the coordinate
root datum in `F4RootPairing`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace ReeF4.WordRelations.ShortOperators
variable {K : Type*} [CommRing K]

private lemma cast_mulVec (A : Matrix Coordinate Coordinate ℤ) (v : Coordinate → ℤ) :
    (Int.castRingHom K) ∘ (A *ᵥ v) = A.map (Int.castRingHom K) *ᵥ ((Int.castRingHom K) ∘ v) := by
  ext i
  exact (Int.castRingHom K).map_mulVec A v i
private lemma cast_single (j : Coordinate) :
    (Int.castRingHom K) ∘ (Pi.single j (1 : ℤ)) = Pi.single j 1 := by
  classical
  ext i
  simp [Pi.single_apply]
private lemma cast_sub (v w : Coordinate → ℤ) :
    (Int.castRingHom K) ∘ (v - w) = (Int.castRingHom K) ∘ v - (Int.castRingHom K) ∘ w := by
  ext i
  simp
private lemma cast_smul (z : ℤ) (v : Coordinate → ℤ) :
    (Int.castRingHom K) ∘ (z • v) = (z : K) • ((Int.castRingHom K) ∘ v) := by
  ext i
  simp

private lemma pairing_reflection (i r j : typeF4Roots) :
    typeF4RootPairing.pairingIn ℤ (typeF4RootPairing.reflectionPerm i r) j =
      typeF4RootPairing.pairingIn ℤ r j - typeF4RootPairing.pairingIn ℤ r i * typeF4RootPairing.pairingIn ℤ i j := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  change algebraMap ℤ ℝ _ = algebraMap ℤ ℝ _ - algebraMap ℤ ℝ _ * algebraMap ℤ ℝ _
  simp only [typeF4RootPairing.algebraMap_pairingIn]
  simp only [RootPairing.pairing, RootPairing.root', typeF4RootPairing.root_reflectionPerm,
    typeF4RootPairing.reflection_apply_root, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]

private lemma titsLiftInv_cartan_integral (i j : typeF4RootPairing_base.support) :
    titsLiftInv (P := typeF4RootPairing) i *ᵥ u j = u j - |typeF4RootPairing_base.cartanMatrix i j| • u i := by
  classical
  have h2 : titsLift (P := typeF4RootPairing) i *ᵥ (titsLift i *ᵥ u j) = u j := by
    rw [titsLift_mulVec_u, Matrix.mulVec_sub, Matrix.mulVec_smul,
      titsLift_mulVec_u, titsLift_mulVec_u]
    norm_num only [RootPairing.Base.cartanMatrix_apply_same, abs_of_pos (by norm_num : (0 : ℤ) < 2)]
    module
  have h := congrArg (fun x => titsLiftInv (P := typeF4RootPairing) i *ᵥ x) h2
  rw [Matrix.mulVec_mulVec, titsLift_inv_mul, Matrix.one_mulVec] at h
  exact h.symm.trans (titsLift_mulVec_u i j)

variable [CharP K 2]
private lemma cast_abs (z : ℤ) : ((|z| : ℤ) : K) = (z : K) := by
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, Int.cast_neg, CharTwo.neg_eq]

private lemma titsLiftInv_cartan (i j : typeF4RootPairing_base.support) :
    (titsLiftInv (P := typeF4RootPairing) i).map (Int.castRingHom K) *ᵥ Pi.single (Sum.inl j) 1 =
      Pi.single (Sum.inl j) 1 - (typeF4RootPairing.pairingIn ℤ i j : K) • Pi.single (Sum.inl i) 1 := by
  have h := congrArg (fun v : Coordinate → ℤ => (Int.castRingHom K) ∘ v)
    (titsLiftInv_cartan_integral i j)
  simpa only [cast_mulVec, cast_sub, cast_smul, u, cast_single, cast_abs,
    RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def] using h

private lemma titsLift_root (i : typeF4RootPairing_base.support) (r : typeF4Roots) :
    (titsLift (P := typeF4RootPairing) i).map (Int.castRingHom K) *ᵥ Pi.single (Sum.inr r) 1 =
      Pi.single (Sum.inr (typeF4RootPairing.reflectionPerm i r)) 1 := by
  have h := congrArg (fun v : Coordinate → ℤ => (Int.castRingHom K) ∘ v)
    (titsLift_mulVec_v (P := typeF4RootPairing) i r)
  simpa only [cast_mulVec, cast_smul, v, cast_single,
    Int.cast_pow, Int.cast_neg, Int.cast_one, CharTwo.neg_eq, one_pow, one_smul] using h

private lemma transportedMatrix_cartan (A : Matrix Coordinate Coordinate ℤ) (r : typeF4Roots)
    (hA : ∀ j : typeF4RootPairing_base.support, A.map (Int.castRingHom K) *ᵥ Pi.single (Sum.inl j) 1 =
      (typeF4RootPairing.pairingIn ℤ r j : K) • Pi.single (Sum.inr r) 1)
    (w : List typeF4RootPairing_base.support) (j : typeF4RootPairing_base.support) :
    (transportedMatrix (P := typeF4RootPairing) w A).map (Int.castRingHom K) *ᵥ Pi.single (Sum.inl j) 1 =
      (typeF4RootPairing.pairingIn ℤ (reflectionWord w r) j : K) •
        Pi.single (Sum.inr (reflectionWord w r)) 1 := by
  classical
  induction w generalizing j with
  | nil => simpa [transportedMatrix, titsWord, titsWordInv, reflectionWord] using hA j
  | cons i w ih =>
    have he : transportedMatrix (P := typeF4RootPairing) (i :: w) A =
        titsLift i * transportedMatrix w A * titsLiftInv i := by
      simp only [transportedMatrix, titsWord, titsWordInv, Matrix.mul_assoc]
    rw [he]
    simp only [Matrix.map_mul, ← Matrix.mulVec_mulVec, titsLiftInv_cartan,
      Matrix.mulVec_sub, Matrix.mulVec_smul, ih, titsLift_root, smul_smul]
    rw [← sub_smul]
    congr 1
    simp only [reflectionWord, pairing_reflection, Int.cast_sub, Int.cast_mul]
    ring

private lemma eMatrix_cartan (i j : typeF4RootPairing_base.support) :
    (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom K) *ᵥ Pi.single (Sum.inl j) 1 =
      (typeF4RootPairing.pairingIn ℤ i j : K) • Pi.single (Sum.inr i.val) 1 := by
  have h := congrArg (fun v : Coordinate → ℤ => (Int.castRingHom K) ∘ v)
    (eMatrix_mulVec_u (P := typeF4RootPairing) i j)
  simpa only [cast_mulVec, cast_smul, u, v, cast_single, cast_abs,
    RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def] using h

private lemma fMatrix_cartan (i j : typeF4RootPairing_base.support) :
    let := typeF4RootPairing.indexNeg
    (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom K) *ᵥ Pi.single (Sum.inl j) 1 =
      (typeF4RootPairing.pairingIn ℤ (-i.val) j : K) • Pi.single (Sum.inr (-i.val)) 1 := by
  let := typeF4RootPairing.indexNeg
  have h := congrArg (fun v : Coordinate → ℤ => (Int.castRingHom K) ∘ v)
    (fMatrix_mulVec_u (P := typeF4RootPairing) i j)
  simpa only [cast_mulVec, cast_smul, u, v, cast_single, cast_abs,
    RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def,
    RootPairing.indexNeg_neg, typeF4RootPairing.pairingIn_reflectionPerm_self_left,
    Int.cast_neg, CharTwo.neg_eq] using h

/-- Every Cartan column of the actual root operator is the root-coroot
pairing times the corresponding root vector in characteristic two. -/
lemma rootOperator_cartanColumn (s : typeF4Roots) (j : typeF4RootPairing_base.support) :
    (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom K) *ᵥ Pi.single (Sum.inl j : Coordinate) 1 =
      (typeF4RootPairing.pairingIn ℤ s j : K) • Pi.single (Sum.inr s : Coordinate) 1 := by
  classical
  let := typeF4RootPairing.indexNeg
  change (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) s).map
    (Int.castRingHom K) *ᵥ Pi.single (Sum.inl j) 1 = _
  by_cases hp : typeF4RootPairing_base.IsPos s
  · rw [rootOperator_of_pos s hp]
    simpa only [(rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) s).target]
      using transportedMatrix_cartan _ _ (eMatrix_cartan
        (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) s).simple)
        (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) s).word j
  · have hn : typeF4RootPairing_base.IsPos (-s) :=
      (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base s).mpr hp
    have he := rootOperator_neg_of_pos (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) (-s) hn
    simp only [neg_neg] at he
    rw [he]
    have ht : reflectionWord
        (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-s)).word
        (-(rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-s)).simple.val) = s := by
      rw [reflectionWord_neg, (rootRoute (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) (-s)).target, neg_neg]
    simpa only [ht] using transportedMatrix_cartan _ _ (fMatrix_cartan
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-s)).simple)
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-s)).word j

private noncomputable def unitRoot (i : Fin 4) : typeF4Roots :=
  ⟨basisVector i, Or.inl (Or.inr ⟨i, Or.inl rfl⟩)⟩
-- The roots e₁, e₂, e₃, and (e₁ + e₂ + e₃ + e₄) / 2.
private noncomputable def detectionRoot : Fin 4 → typeF4Roots :=
  ![unitRoot 0, unitRoot 1, unitRoot 2,
    ⟨halfSignVector (fun _ => true), halfSignVector_mem_typeF4Roots _⟩]

private lemma detectionRoot_short (i : Fin 4) : IsShortRoot (detectionRoot i) := by
  have hn : dot (detectionRoot i).val (detectionRoot i).val = 1 := by
    fin_cases i <;> norm_num [detectionRoot, unitRoot, dot, basisVector,
      halfSignVector, Fin.sum_univ_four, Pi.single_apply,
      Matrix.cons_val_two, Matrix.cons_val_three]
  intro hl
  have := isLongRoot_norm (detectionRoot i) hl
  linarith

private lemma detectionRoot_pairing (i j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (detectionRoot i) (typeF4RootPairing_baseEquiv j) =
      (!![0,0,0,1; 1,0,0,-1; -1,1,0,-1; 0,0,1,-1] : Matrix (Fin 4) (Fin 4) ℤ) i j := by
  apply Int.cast_injective (α := ℝ)
  change algebraMap ℤ ℝ _ = _
  rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing,
    typeF4RootPairing_baseEquiv_val, typeF4CorootScale_simpleRoot]
  fin_cases i <;> fin_cases j <;>
    norm_num [detectionRoot, unitRoot, typeF4SimpleRootIndex_val, typeF4SimpleRoot,
      dot, basisVector, halfSignVector, Fin.sum_univ_four, Pi.single_apply,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- A vector supported on the Cartan coordinates and killed by every short
root operator is zero. Root-coordinate vanishing is an explicit premise. -/
lemma eq_zero_of_rootCoordinates_eq_zero (x : Coordinate → K)
    (hx : ∀ r : typeF4Roots, x (Sum.inr r) = 0)
    (hE : ∀ s : typeF4Roots, IsShortRoot s →
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom K) *ᵥ x = 0) : x = 0 := by
  classical
  have hp (s : typeF4Roots) (hs : IsShortRoot s) :
      ∑ j : typeF4RootPairing_base.support,
        (typeF4RootPairing.pairingIn ℤ s j : K) * x (Sum.inl j) = 0 := by
    have hz := congrFun (hE s hs) (Sum.inr s)
    have hc (j : typeF4RootPairing_base.support) :
        (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
          (Int.castRingHom K) (Sum.inr s) (Sum.inl j) =
          (typeF4RootPairing.pairingIn ℤ s j : K) := by
      have h := congrFun (rootOperator_cartanColumn (K := K) s j) (Sum.inr s)
      simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
        Pi.single_eq_same, smul_eq_mul, mul_one] using h
    simpa only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hx, mul_zero,
      Finset.sum_const_zero, add_zero, hc, Pi.zero_apply] using hz
  have hn (i : Fin 4) :
      ∑ j : Fin 4,
        (((!![0,0,0,1; 1,0,0,-1; -1,1,0,-1; 0,0,1,-1] :
          Matrix (Fin 4) (Fin 4) ℤ) i j) : K) *
          x (Sum.inl (typeF4RootPairing_baseEquiv j)) = 0 := by
    have h := hp (detectionRoot i) (detectionRoot_short i)
    rw [← typeF4RootPairing_baseEquiv.sum_comp (fun j =>
      (typeF4RootPairing.pairingIn ℤ (detectionRoot i) j : K) * x (Sum.inl j))] at h
    simpa only [detectionRoot_pairing] using h
  -- The four rows eliminate coordinates 3, 0, 1, and 2 in that order.
  have h3 := hn 0
  have h0 := hn 1
  have h1 := hn 2
  have h2 := hn 3
  norm_num [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three] at h3 h0 h1 h2
  simp only [h3, neg_zero, add_zero] at h0
  simp only [h3, h0, neg_zero, zero_add, add_zero] at h1
  simp only [h3, neg_zero, add_zero] at h2
  ext (j | r)
  · obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
    fin_cases j <;> assumption
  · exact hx r

/-- The short-root Cartan-column formula over each Ree coefficient field. -/
theorem coefficientField_rootOperator_cartanColumn (m : ℕ) (s : typeF4Roots)
    (_hs : IsShortRoot s) (j : typeF4RootPairing_base.support) :
    (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom (CoefficientField m)) *ᵥ Pi.single (Sum.inl j : Coordinate) 1 =
      (typeF4RootPairing.pairingIn ℤ s j : CoefficientField m) •
        Pi.single (Sum.inr s : Coordinate) 1 :=
  rootOperator_cartanColumn s j

/-- The short operators detect every Cartan-supported vector over the Ree field. -/
theorem coefficientField_cartanKernel (m : ℕ) (x : Coordinate → CoefficientField m)
    (hx : ∀ r : typeF4Roots, x (Sum.inr r) = 0)
    (hE : ∀ s : typeF4Roots, IsShortRoot s →
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom (CoefficientField m)) *ᵥ x = 0) : x = 0 :=
  eq_zero_of_rootCoordinates_eq_zero x hx hE

end ReeF4.WordRelations.ShortOperators
