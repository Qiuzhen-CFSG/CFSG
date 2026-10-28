module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Operators

/-!
# Injectivity of the signed F4 adjoint map

The literal signed root operators and signed Cartan commutators in `Operators`
are linearly independent over every field. Applying a vanishing combination to
each opposite root vector and reading its Cartan coordinates kills all 48 root
coefficients. The matching contribution is a Cartan vector transported by an
invertible integral Tits word, and thus remains nonzero in every characteristic.

The remaining four operators are diagonal. Their entries on the four simple
root lines give the F4 Cartan matrix, whose integral inverse recovers their
coefficients. All orientation factors have square one. In particular the
argument includes characteristic three and supplies the injectivity input to
`CoverCenter.center_eq_bot_of_adjointMap`.

Sources: the integral Geck construction and all-root bracket identities in
`IntegralGeckConstruction`, `IntegralAllRootOperators`, and
`IntegralChevalleyBrackets`; the adjoint Chevalley conventions of GLS3 §§2.2–2.6
(`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
variable (F : Type*) [Field F]
local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
private def castVec (x : Coordinate → ℤ) : Coordinate → F := (Int.castRingHom F) ∘ x

private lemma cast_mulVec (A : Matrix Coordinate Coordinate ℤ) (x : Coordinate → ℤ) :
    castVec F (A *ᵥ x) = A.map (Int.castRingHom F) *ᵥ castVec F x := by
  ext i
  exact (Int.castRingHom F).map_mulVec A x i

private lemma rootVector_eq_smul_v (r : typeF4Roots) :
    ∃ s : ℤ, s * s = 1 ∧ rootVector (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r = s • v r := by
  exact exists_rootVector_sign r

private lemma rootVector_cartan_zero (r : typeF4Roots) (i : typeF4RootPairing_base.support) :
    rootVector (P := typeF4RootPairing) (b := typeF4RootPairing_base) r (Sum.inl i) = 0 := by
  rcases rootVector_eq_smul_v r with ⟨s, hs, h⟩
  rw [h]
  simp [v]

private def CartanSupported (x : Coordinate → ℤ) : Prop :=
  ∀ r : typeF4Roots, x (Sum.inr r) = 0

private lemma cartan_supported_eq_sum {x : Coordinate → ℤ} (hx : CartanSupported x) :
    x = ∑ i : typeF4RootPairing_base.support, x (Sum.inl i) • u i := by
  ext j
  rcases j with i | r
  · simp [u, Pi.single_apply]
  · simp [u, hx r]

private lemma titsLift_preserves_cartan_supported (i : typeF4RootPairing_base.support)
    {x : Coordinate → ℤ} (hx : CartanSupported x) :
    CartanSupported (titsLift i *ᵥ x) := by
  rw [cartan_supported_eq_sum hx]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
  intro r
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [titsLift_mulVec_u]
  simp [u]

private lemma titsWord_preserves_cartan_supported (w : List typeF4RootPairing_base.support)
    {x : Coordinate → ℤ} (hx : CartanSupported x) :
    CartanSupported (titsWord w *ᵥ x) := by
  have hw : ∀ w : List typeF4RootPairing_base.support,
      CartanSupported (titsWord w *ᵥ x) := by
    intro w
    induction w with
    | nil => simpa [titsWord] using hx
    | cons i w ih =>
        rw [titsWord, ← Matrix.mulVec_mulVec]
        exact titsLift_preserves_cartan_supported i ih
  exact hw w

private lemma rootCartanVector_cartan_supported (r : typeF4Roots) :
    CartanSupported (rootCartanVector (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r) := by
  exact titsWord_preserves_cartan_supported _ (by
    intro r
    simp [u])

-- Integral Tits transport has an integral inverse, so each transported
-- Cartan vector remains nonzero after specialization to any field.
private lemma cast_rootCartanVector_ne_zero (r : typeF4Roots) :
    castVec F (rootCartanVector (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r) ≠ 0 := by
  intro hz
  let route := rootRoute (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r
  have h := congrArg (fun y : Coordinate → F =>
      (titsWordInv route.word).map (Int.castRingHom F) *ᵥ y) hz
  have hcast := cast_mulVec F (titsWordInv route.word)
    (rootCartanVector (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r)
  simp only [Matrix.mulVec_zero] at h
  rw [← hcast] at h
  change castVec F (titsWordInv route.word *ᵥ
    (titsWord route.word *ᵥ u route.simple)) = 0 at h
  rw [Matrix.mulVec_mulVec, titsWord_inv_mul, Matrix.one_mulVec] at h
  have hu : castVec F (u route.simple) ≠ 0 := by
    intro hu
    have hc := congrFun hu (Sum.inl route.simple)
    simp [castVec, u] at hc
  exact hu h

private lemma specializedRootOperator_cartan_zero_of_ne (F : Type*) [Field F]
    (s r : typeF4Roots) (hsr : s ≠ r) (i : typeF4RootPairing_base.support) :
    ((rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) s).map
      (Int.castRingHom F) *ᵥ castVec F (rootVector (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) (-r))) (Sum.inl i) = 0 := by
  let := typeF4RootPairing.indexNeg
  by_cases hadd : typeF4RootPairing.root s +
      typeF4RootPairing.root (-r) ∈ Set.range typeF4RootPairing.root
  · obtain ⟨k, hk⟩ := hadd
    obtain ⟨ε, hε, hact⟩ := rootOperator_mulVec_root_add_signed
      (P := typeF4RootPairing) (b := typeF4RootPairing_base)
      (i := s) (j := -r) (k := k) hk
    have hcast := congrArg (castVec F) hact
    rw [cast_mulVec] at hcast
    calc
      _ = castVec F ((ε * (↑(RootPairing.chainBotCoeff s (-r)) + 1) : ℤ) •
          rootVector (P := typeF4RootPairing)
            (b := typeF4RootPairing_base) k) (Sum.inl i) :=
        congrFun hcast (Sum.inl i)
      _ = 0 := by simp [castVec, Function.comp_apply, rootVector_cartan_zero]
  · have hne : (-r : typeF4Roots) ≠ -s := by
      intro h
      apply hsr
      exact neg_injective h.symm
    have hzero := rootOperator_mulVec_root_eq_zero
      (P := typeF4RootPairing) (b := typeF4RootPairing_base)
      (i := s) (j := (-r : typeF4Roots)) hne hadd
    have hcast := congrArg (castVec F) hzero
    rw [cast_mulVec] at hcast
    simpa [castVec, Function.comp_apply] using congrFun hcast (Sum.inl i)

private def cartanMatrixInt (i : typeF4RootPairing_base.support) :
    Matrix Coordinate Coordinate ℤ :=
  Matrix.fromBlocks 0 0 0
    (Matrix.diagonal fun r : typeF4Roots =>
      typeF4RootPairing.pairingIn ℤ r i)

private lemma integral_cartan_commutator (i : typeF4RootPairing_base.support) :
    (eMatrix (P := typeF4RootPairing) i * fMatrix i -
      fMatrix i * eMatrix i) = cartanMatrixInt i := by
  have hcastR : (Int.castRingHom ℝ) = algebraMap ℤ ℝ := by
    ext z
    norm_num
  have he : (eMatrix (P := typeF4RootPairing) i).map
      (Int.castRingHom ℝ) = RootPairing.GeckConstruction.e i := by
    rw [hcastR]
    exact map_eMatrix i
  have hf : (fMatrix (P := typeF4RootPairing) i).map
      (Int.castRingHom ℝ) = RootPairing.GeckConstruction.f i := by
    rw [hcastR]
    exact map_fMatrix i
  have hH : (cartanMatrixInt i).map (algebraMap ℤ ℝ) =
      RootPairing.GeckConstruction.h i := by
    ext (a | a) (b | b) <;>
      simp [cartanMatrixInt, RootPairing.GeckConstruction.h_def,
        Matrix.diagonal_apply]
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ ℝ)
  rw [hcastR] at he hf
  change (eMatrix (P := typeF4RootPairing) i * fMatrix i -
      fMatrix i * eMatrix i).map (algebraMap ℤ ℝ) =
    (cartanMatrixInt i).map (algebraMap ℤ ℝ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, he, hf, hH]
  simpa only [Ring.lie_def] using
    (RootPairing.GeckConstruction.lie_e_f_same
      (P := typeF4RootPairing) (b := typeF4RootPairing_base) i)

private lemma specialized_cartan_commutator (F : Type*) [Field F]
    (i : typeF4RootPairing_base.support) :
    ((eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom F) *
      (fMatrix i).map (Int.castRingHom F) -
      (fMatrix i).map (Int.castRingHom F) * (eMatrix i).map
        (Int.castRingHom F)) =
      (cartanMatrixInt i).map (Int.castRingHom F) := by
  have h := congrArg (fun M : Matrix Coordinate Coordinate ℤ =>
      M.map (Int.castRingHom F)) (integral_cartan_commutator i)
  simpa only [Matrix.map_sub _ (map_sub _), Matrix.map_mul] using h

private lemma specialized_cartan_commutator_cartan_zero (F : Type*) [Field F]
    (i : typeF4RootPairing_base.support) (r : typeF4Roots)
    (q : typeF4RootPairing_base.support) :
    (((eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom F) *
      (fMatrix i).map (Int.castRingHom F) -
      (fMatrix i).map (Int.castRingHom F) * (eMatrix i).map
        (Int.castRingHom F)) *ᵥ castVec F (rootVector r))
      (Sum.inl q) = 0 := by
  rw [specialized_cartan_commutator]
  simp [cartanMatrixInt, Matrix.mulVec, dotProduct]

private lemma specializedRootOperator_opposite_of_pos (F : Type*) [Field F]
    (r : typeF4Roots) (hr : typeF4RootPairing_base.IsPos r) :
    (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).map
        (Int.castRingHom F) *ᵥ castVec F
          (rootVector (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)) =
      castVec F (rootCartanVector (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) r) := by
  have h := rootOperator_mulVec_opposite_pair
    (P := typeF4RootPairing) (b := typeF4RootPairing_base) r hr |>.1
  exact congrArg (castVec F) h ▸
    (cast_mulVec F (rootOperator (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r)
      (rootVector (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) (-r))).symm

private lemma specializedRootOperator_opposite_of_neg (F : Type*) [Field F]
    (r : typeF4Roots) (hr : ¬typeF4RootPairing_base.IsPos r) :
    (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).map
        (Int.castRingHom F) *ᵥ castVec F
          (rootVector (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)) =
      castVec F (rootCartanVector (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) (-r)) := by
  have hr' : typeF4RootPairing_base.IsPos (-r) :=
    (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr
  have h := rootOperator_mulVec_opposite_pair
    (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r) hr' |>.2
  have h' : rootOperator (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r *ᵥ
      rootVector (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r) =
      rootCartanVector (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) (-r) := by
    simpa only [neg_neg] using h
  exact congrArg (castVec F) h' ▸
    (cast_mulVec F (rootOperator (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r)
      (rootVector (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) (-r))).symm

private def rootCartanWitness (r : typeF4Roots) : Coordinate → ℤ :=
  if typeF4RootPairing_base.IsPos r then
    rootCartanVector (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  else rootCartanVector (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) (-r)

private lemma rootCartanWitness_ne_zero (F : Type*) [Field F] (r : typeF4Roots) :
    castVec F (rootCartanWitness r) ≠ 0 := by
  unfold rootCartanWitness
  split
  · exact cast_rootCartanVector_ne_zero F r
  · exact cast_rootCartanVector_ne_zero F (-r)

private lemma rootCartanWitness_root_zero (F : Type*) [Field F]
    (r s : typeF4Roots) :
    castVec F (rootCartanWitness r) (Sum.inr s) = 0 := by
  unfold rootCartanWitness
  split
  · simpa [castVec, Function.comp_apply] using
      congrArg (Int.castRingHom F) (rootCartanVector_cartan_supported r s)
  · simpa [castVec, Function.comp_apply] using
      congrArg (Int.castRingHom F) (rootCartanVector_cartan_supported (-r) s)

private lemma adjointMap_mulVec (F : Type*) [Field F] (v : Coordinate → F)
    (x : Coordinate → F) :
    adjointMap F v *ᵥ x =
      ∑ j, v j • (coordinateOperator F j *ᵥ x) := by
  change (∑ j, v j • coordinateOperator F j) *ᵥ x = _
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]

private lemma coordinateOperator_cartan_row (F : Type*) [Field F]
    (r : typeF4Roots) (q : typeF4RootPairing_base.support) :
    ∀ j : Coordinate,
      (coordinateOperator F j *ᵥ castVec F
        (rootVector (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)))
        (Sum.inl q) =
      if j = Sum.inr r then
        (rootOperatorOrientation r : F) •
          castVec F (rootCartanWitness r) (Sum.inl q)
      else 0 := by
  intro j
  rcases j with i | s
  · simp only [coordinateOperator]
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [specialized_cartan_commutator_cartan_zero F i (-r) q]
    simp
  · by_cases hsr : s = r
    · subst s
      simp only [coordinateOperator, specializedRootOperator]
      simp only [Matrix.smul_mulVec, Pi.smul_apply]
      by_cases hr : typeF4RootPairing_base.IsPos r
      · rw [specializedRootOperator_opposite_of_pos F r hr]
        simp [rootCartanWitness, hr]
      · rw [specializedRootOperator_opposite_of_neg F r hr]
        simp [rootCartanWitness, hr]
    · simp only [coordinateOperator, specializedRootOperator]
      simp only [Matrix.smul_mulVec, Pi.smul_apply]
      rw [specializedRootOperator_cartan_zero_of_ne F s r hsr q]
      simp [hsr]

-- On the opposite root line, only the matching root operator contributes
-- to the Cartan coordinates; its transported Cartan vector is primitive.
private lemma root_coefficient_eq_zero (F : Type*) [Field F]
    (v : Coordinate → F) (hzero : adjointMap F v = 0)
    (r : typeF4Roots) : v (Sum.inr r) = 0 := by
  let x := castVec F (rootVector (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) (-r))
  have hq (q : typeF4RootPairing_base.support) :
      ((v (Sum.inr r) * (rootOperatorOrientation r : F)) •
        castVec F (rootCartanWitness r) (Sum.inl q)) = 0 := by
    have h := congrFun (congrArg (fun A : Matrix Coordinate Coordinate F =>
      A *ᵥ x) hzero) (Sum.inl q)
    rw [Matrix.zero_mulVec] at h
    rw [adjointMap_mulVec] at h
    simp only [Finset.sum_apply, Pi.smul_apply] at h
    have hterm (j : Coordinate) :
        v j • (coordinateOperator F j *ᵥ x) (Sum.inl q) =
          if j = Sum.inr r then
            (v (Sum.inr r) * (rootOperatorOrientation r : F)) •
              castVec F (rootCartanWitness r) (Sum.inl q)
          else 0 := by
      rw [coordinateOperator_cartan_row F r q j]
      by_cases hj : j = Sum.inr r
      · subst j
        simp only [if_pos, smul_eq_mul]
        ring
      · simp [hj]
    simp_rw [hterm] at h
    simpa [smul_smul, mul_assoc] using h
  have hw : castVec F (rootCartanWitness r) ≠ 0 :=
    rootCartanWitness_ne_zero F r
  have hq0 : ∃ q : typeF4RootPairing_base.support,
      castVec F (rootCartanWitness r) (Sum.inl q) ≠ 0 := by
    by_contra hall
    apply hw
    funext j
    rcases j with q | s
    · by_contra hq'
      exact hall ⟨q, hq'⟩
    · exact rootCartanWitness_root_zero F r s
  obtain ⟨q, hq0⟩ := hq0
  have hz := hq q
  have hscalar : v (Sum.inr r) * (rootOperatorOrientation r : F) = 0 := by
    exact (smul_eq_zero.mp hz).resolve_right hq0
  have hor2 : (rootOperatorOrientation r : F) *
      (rootOperatorOrientation r : F) = 1 := by
    have h := congrArg (Int.castRingHom F) (rootOperatorOrientation_sq r)
    simpa only [map_mul, map_one, Int.coe_castRingHom] using h
  have hor : (rootOperatorOrientation r : F) ≠ 0 := by
    intro hor
    rw [hor] at hor2
    have h01 : (0 : F) = 1 := by simpa only [zero_mul] using hor2
    exact zero_ne_one h01
  exact (mul_eq_zero.mp hscalar).resolve_right hor

private lemma adjointMap_eq_cartan_sum (F : Type*) [Field F]
    (v : Coordinate → F) (hroot : ∀ r : typeF4Roots, v (Sum.inr r) = 0) :
    adjointMap F v =
      ∑ i : typeF4RootPairing_base.support,
        (-(simpleOperatorOrientation (b := typeF4RootPairing_base) i : F) *
          v (Sum.inl i)) • (cartanMatrixInt i).map (Int.castRingHom F) := by
  change (∑ j, v j • coordinateOperator F j) = _
  rw [Fintype.sum_sum_type]
  simp only [coordinateOperator]
  simp_rw [hroot]
  simp only [zero_smul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [specialized_cartan_commutator, smul_smul, mul_comm]

private lemma cartan_coefficient_equation (F : Type*) [Field F]
    (v : Coordinate → F) (hroot : ∀ r : typeF4Roots, v (Sum.inr r) = 0)
    (hzero : adjointMap F v = 0)
    (j : typeF4RootPairing_base.support) :
    ∑ i : typeF4RootPairing_base.support,
      (-(simpleOperatorOrientation (b := typeF4RootPairing_base) i : F) *
        v (Sum.inl i)) *
        (typeF4RootPairing_base.cartanMatrix j i : F) = 0 := by
  rw [adjointMap_eq_cartan_sum F v hroot] at hzero
  have h := congrArg (fun A : Matrix Coordinate Coordinate F =>
    A (Sum.inr (j : typeF4Roots)) (Sum.inr (j : typeF4Roots))) hzero
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply,
    cartanMatrixInt, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply_eq,
    Matrix.zero_apply, RootPairing.Base.cartanMatrixIn_def, Int.coe_castRingHom] using h

-- The rows of the integral inverse of the F4 Cartan matrix recover all
-- four coefficients, with no division by the characteristic.
private lemma f4_cartan_system_eq_zero (F : Type*) [Field F]
    (d : typeF4RootPairing_base.support → F)
    (h : ∀ j : typeF4RootPairing_base.support,
      ∑ i : typeF4RootPairing_base.support,
        d i * (typeF4RootPairing_base.cartanMatrix j i : F) = 0) :
    ∀ i, d i = 0 := by
  let x : Fin 4 → F := fun i => d (typeF4RootPairing_baseEquiv i)
  have hx (j : Fin 4) :
      ∑ i : Fin 4, x i * (typeF4CartanMatrix j i : F) = 0 := by
    have hh := h (typeF4RootPairing_baseEquiv j)
    rw [← typeF4RootPairing_baseEquiv.sum_comp] at hh
    simpa only [typeF4RootPairing_base_cartan_apply] using hh
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  simp [typeF4CartanMatrix, Fin.sum_univ_succ] at h0 h1 h2 h3
  intro i
  obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  change x j = 0
  fin_cases j
  · change x 0 = 0
    linear_combination 2 * h0 + 3 * h1 + 4 * h2 + 2 * h3
  · change x 1 = 0
    linear_combination 3 * h0 + 6 * h1 + 8 * h2 + 4 * h3
  · change x 2 = 0
    linear_combination 2 * h0 + 4 * h1 + 6 * h2 + 3 * h3
  · change x 3 = 0
    linear_combination h0 + 2 * h1 + 3 * h2 + 2 * h3

/-- The fixed signed F4 adjoint map is injective over every field.
In particular, this supplies the injectivity premise of
`center_eq_bot_of_adjointMap` for finite fields of odd characteristic. -/
theorem adjointMap_injective (F : Type*) [Field F] :
    Function.Injective (adjointMap F) := by
  intro v w hvw
  let z : Coordinate → F := v - w
  have hzero : adjointMap F z = 0 := by
    dsimp [z]
    rw [map_sub, hvw, sub_self]
  have hroot : ∀ r : typeF4Roots, z (Sum.inr r) = 0 := by
    intro r
    exact root_coefficient_eq_zero F z hzero r
  let d : typeF4RootPairing_base.support → F := fun i =>
    -(simpleOperatorOrientation (b := typeF4RootPairing_base) i : F) *
      z (Sum.inl i)
  have hdEq : ∀ j : typeF4RootPairing_base.support,
      ∑ i : typeF4RootPairing_base.support,
        d i * (typeF4RootPairing_base.cartanMatrix j i : F) = 0 := by
    intro j
    simpa [d] using cartan_coefficient_equation F z hroot hzero j
  have hd : ∀ i : typeF4RootPairing_base.support, d i = 0 :=
    f4_cartan_system_eq_zero F d hdEq
  have hzcartan : ∀ i : typeF4RootPairing_base.support, z (Sum.inl i) = 0 := by
    intro i
    have hdi := hd i
    have hsign : (simpleOperatorOrientation
        (b := typeF4RootPairing_base) i : F) ≠ 0 := by
      have hs := congrArg (Int.castRingHom F)
        (simpleOperatorOrientation_sq (b := typeF4RootPairing_base) i)
      simp only [map_mul, map_one, Int.coe_castRingHom] at hs
      intro h
      rw [h] at hs
      exact zero_ne_one (by simpa only [zero_mul] using hs)
    apply (mul_eq_zero.mp (show
      (-(simpleOperatorOrientation (b := typeF4RootPairing_base) i : F)) *
          z (Sum.inl i) = 0 by simpa [d] using hdi)).resolve_left
    intro hneg
    apply hsign
    exact neg_eq_zero.mp hneg
  have hz : z = 0 := by
    funext j
    rcases j with i | r
    · exact hzcartan i
    · exact hroot r
  exact sub_eq_zero.mp hz


end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
