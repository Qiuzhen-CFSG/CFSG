module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Actions
public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections.Coordinates
public import Theory.ElementaryAbelian.Basic
public import Theory.FieldTheory.BinaryTorusTwoPower

/-!
# Coefficients of outer involutions and the elementary outer index

A coefficient action which is an F-linear congruence fixes F. Fixing the
symmetric Hermitian matrices then forces the congruence matrix to be a
norm-one scalar, and an arbitrary off-diagonal entry detects its coefficient.
Thus semilinear congruence expressions have unique field coefficients.

Under `NormalizerCoverage` this defines a homomorphism on the literal binary
normalizer, with kernel the full GL₃ congruence image. Raising a congruence to
`2^(2*n)-1` gives an SL₃ action, so this kernel contributes no outer involution.
This retains the fixed-field scalars and inner-diagonal matrices. The full
quotient by the SL₃ image is never assumed cyclic.

An outer involution consequently has coefficient σ. For an elementary
subgroup A, the coefficient kernel is exactly A ∩ L and its image lies in
{1, σ}; the first isomorphism theorem bounds the literal relative index by two.
The first conclusion supplies the matrix input for involution descent; the
second supplies the outer-index premise of the rank assembly in `OuterRank`.
Normalizer coverage and the remaining fusion and centralizer arguments belong
to their separate assembly owners.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, standing
hypotheses on printed p.377, H.4.2 setup and H.4.4(6), printed pp.380–381;
the inner-diagonal factor is visible in H.4.6(3), printed p.382.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.OuterRank.Coefficients
open FieldSections
variable (n : ℕ) [NeZero n]

private def entry (z : E n) : Space n :=
  ⟨Matrix.single 0 1 z + Matrix.single 1 0 (sigma n z), by
    ext a b
    simp only [adjoint, Matrix.map_apply, Matrix.transpose_apply, Matrix.add_apply,
      Matrix.single_apply, map_add, @and_comm ((0 : Fin 3) = b) ((1 : Fin 3) = a),
      @and_comm ((1 : Fin 3) = b) ((0 : Fin 3) = a)]
    split_ifs <;> simp only [map_zero, sigma_involutive n z, add_zero, zero_add, add_comm]⟩

private theorem coefficient_injective : Function.Injective (coefficient n) := by
  intro τ υ h
  ext z
  have he := congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => (e (entry n z)).val 0 1) h
  simpa [coefficient_apply, entry, Matrix.single_apply] using he

private theorem coefficient_one : coefficient n 1 = 1 := by
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  ext a b
  rfl

private theorem coefficient_mul (τ υ : E n ≃+* E n) :
    coefficient n (τ * υ) = coefficient n τ * coefficient n υ := by
  apply LinearEquiv.ext
  intro X
  rfl

/-- A coefficient action which is a linear congruence has trivial coefficient. -/
theorem coefficient_eq_one_of_mem_congruenceImage (τ : E n ≃+* E n)
    (hτ : coefficient n τ ∈ congruenceImage n) : τ = 1 := by
  obtain ⟨g, hg⟩ := hτ
  have he (X : Space n) : g.val * X.val * adjoint n g.val = X.val.map τ :=
    congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => (e X).val) hg
  let D := diagonalUnit n 0
  have hD : D.val.map τ = D.val := by
    ext a b
    simp [D, diagonalUnit, Matrix.single_apply, apply_ite]
  have hfix (c : F n) : τ c.val = c.val := by
    have hc := he (c • D)
    have hm : (c • D).val.map τ = τ c.val • D.val := by
      ext a b
      change τ (c.val * D.val a b) = τ c.val * D.val a b
      rw [map_mul]
      exact congrArg (fun z => τ c.val * z) (congrArg (fun B : Mat n => B a b) hD)
    change g.val * (c.val • D.val) * adjoint n g.val = _ at hc
    rw [hm, Matrix.mul_smul, Matrix.smul_mul, he, hD] at hc
    have hc00 := congrArg (fun B : Mat n => B 0 0) hc
    simpa [D, diagonalUnit, Matrix.single_apply] using hc00.symm
  have hsym (X : Space n) (hX : X.val.transpose = X.val) :
      g.val * X.val * adjoint n g.val = X.val := by
    rw [he]
    ext a b
    exact hfix ⟨X.val a b, fieldFixed_entry n
      ⟨X, (mem_fieldFixed n X).mpr (Subtype.ext hX)⟩ a b⟩
  obtain ⟨c, hc, hnorm⟩ := eq_scalar_of_fixes_symmetric n g.val hsym
  apply coefficient_injective n
  rw [coefficient_one, ← hg]
  exact (mem_binaryCongruence_ker_iff n g).mpr ⟨c, hc, hnorm⟩

private theorem coefficient_congruence (τ : E n ≃+* E n)
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) :
    coefficient n τ * binaryCongruence n g =
      binaryCongruence n (Matrix.GeneralLinearGroup.map τ.toRingHom g) * coefficient n τ := by
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change (g.val * X.val * adjoint n g.val).map τ =
    (g.val.map τ) * X.val.map τ * adjoint n (g.val.map τ)
  rw [Matrix.map_mul, Matrix.map_mul, adjoint_map]

/-- Multiplication of the literal semilinear congruence operators. -/
theorem semilinearCongruence_mul (g h : Matrix.GeneralLinearGroup (Fin 3) (E n))
    (τ υ : E n ≃+* E n) :
    semilinearCongruence n g τ * semilinearCongruence n h υ =
      semilinearCongruence n (g * Matrix.GeneralLinearGroup.map τ.toRingHom h) (τ * υ) := by
  simp only [semilinearCongruence, map_mul, coefficient_mul]
  rw [mul_assoc, ← mul_assoc (coefficient n τ), coefficient_congruence]
  simp only [mul_assoc]

/-- The field automorphism in a congruence expression is unique. -/
theorem semilinearCongruence_coefficient_unique
    (g h : Matrix.GeneralLinearGroup (Fin 3) (E n)) (τ υ : E n ≃+* E n)
    (he : semilinearCongruence n g τ = semilinearCongruence n h υ) : τ = υ := by
  have hc : coefficient n (τ * υ⁻¹) = binaryCongruence n (g⁻¹ * h) := by
    rw [coefficient_mul]
    have hi : coefficient n υ⁻¹ = (coefficient n υ)⁻¹ := (coefficient_symm n υ).symm
    rw [hi, map_mul, map_inv]
    change binaryCongruence n g * coefficient n τ = binaryCongruence n h * coefficient n υ at he
    calc
      _ = (binaryCongruence n g)⁻¹ *
          (binaryCongruence n g * coefficient n τ) * (coefficient n υ)⁻¹ := by simp
      _ = (binaryCongruence n g)⁻¹ * binaryCongruence n h := by rw [he]; simp [mul_assoc]
  have hz := coefficient_eq_one_of_mem_congruenceImage n (τ * υ⁻¹) ⟨g⁻¹ * h, hc.symm⟩
  exact mul_inv_eq_one.mp hz

/-- The congruence quotient is killed by the odd order of the coefficient units.
This retains both the scalar and inner-diagonal factors. -/
theorem congruence_pow_mem_binaryImage
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) :
    binaryCongruence n g ^ (2 ^ (2 * n) - 1) ∈ binaryImage n := by
  let := Fintype.ofFinite (E n)
  let m := 2 ^ (2 * n) - 1
  have hd : (g.val ^ m).det = 1 := by
    rw [Matrix.det_pow]
    have h := FiniteField.pow_card_sub_one_eq_one g.val.det g.det_ne_zero
    simpa only [← Nat.card_eq_fintype_card, card_E, m] using h
  let a : Cover n := ⟨g.val ^ m, hd⟩
  refine ⟨a, ?_⟩
  rw [← binaryCongruence_toGL, ← map_pow]
  congr 1
  apply Units.ext
  rfl

/-- An involutory element of the entire linear congruence image is already inner. -/
theorem mem_binaryImage_of_mem_congruenceImage_of_sq_eq_one
    (e : Space n ≃ₗ[ZMod 2] Space n) (he : e ∈ congruenceImage n) (h2 : e ^ 2 = 1) :
    e ∈ binaryImage n := by
  obtain ⟨g, rfl⟩ := he
  have hm : (2 ^ (2 * n) - 1) % 2 = 1 := by
    have hn : 2 * n ≠ 0 := Nat.mul_ne_zero (by decide) (NeZero.ne n)
    have hp : 0 < 2 ^ (2 * n) := by positivity
    have heven : 2 ^ (2 * n) % 2 = 0 := by simp [Nat.pow_mod, hn]
    omega
  have hp : binaryCongruence n g ^ (2 ^ (2 * n) - 1) = binaryCongruence n g := by
    simpa only [pow_one] using pow_eq_pow_of_modEq (show Nat.ModEq 2 (2 ^ (2 * n) - 1) 1 from hm) h2
  exact hp ▸ congruence_pow_mem_binaryImage n g

private theorem exists_coefficient (hCoverage : NormalizerCoverage n) (e : binaryNormalizer n) :
    ∃ τ : E n ≃+* E n, ∃ g : Matrix.GeneralLinearGroup (Fin 3) (E n),
      e.val = semilinearCongruence n g τ := by
  obtain ⟨g, τ, he⟩ := hCoverage e.val e.property
  refine ⟨τ, g, ?_⟩
  apply LinearEquiv.ext
  intro X
  exact Subtype.ext (he X)

private def coefficientValue (hCoverage : NormalizerCoverage n) (e : binaryNormalizer n) :
    E n ≃+* E n := Classical.choose (exists_coefficient n hCoverage e)

private theorem coefficientValue_spec (hCoverage : NormalizerCoverage n) (e : binaryNormalizer n) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 3) (E n),
      e.val = semilinearCongruence n g (coefficientValue n hCoverage e) :=
  Classical.choose_spec (exists_coefficient n hCoverage e)

/-- The uniquely determined field coefficient of an element of the literal normalizer. -/
def normalizerCoefficient (hCoverage : NormalizerCoverage n) :
    binaryNormalizer n →* (E n ≃+* E n) where
  toFun := coefficientValue n hCoverage
  map_one' := by
    obtain ⟨g, hg⟩ := coefficientValue_spec n hCoverage 1
    apply semilinearCongruence_coefficient_unique n g 1
    simpa [semilinearCongruence, coefficient_one] using hg.symm
  map_mul' e f := by
    obtain ⟨g, hg⟩ := coefficientValue_spec n hCoverage e
    obtain ⟨h, hh⟩ := coefficientValue_spec n hCoverage f
    obtain ⟨k, hk⟩ := coefficientValue_spec n hCoverage (e * f)
    apply semilinearCongruence_coefficient_unique n k
      (g * Matrix.GeneralLinearGroup.map (coefficientValue n hCoverage e).toRingHom h)
    rw [← semilinearCongruence_mul, ← hg, ← hh]
    exact hk.symm

/-- Every normalizer element has an expression with its canonical coefficient. -/
theorem normalizerCoefficient_spec (hCoverage : NormalizerCoverage n) (e : binaryNormalizer n) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 3) (E n),
      e.val = semilinearCongruence n g (normalizerCoefficient n hCoverage e) :=
  coefficientValue_spec n hCoverage e

/-- The kernel retains all GL₃ congruences, including the odd outer factors. -/
theorem normalizerCoefficient_eq_one_iff (hCoverage : NormalizerCoverage n)
    (e : binaryNormalizer n) :
    normalizerCoefficient n hCoverage e = 1 ↔ e.val ∈ congruenceImage n := by
  obtain ⟨g, hg⟩ := normalizerCoefficient_spec n hCoverage e
  constructor
  · intro he
    refine ⟨g, ?_⟩
    simpa [he, semilinearCongruence, coefficient_one] using hg.symm
  · rintro ⟨h, hh⟩
    apply semilinearCongruence_coefficient_unique n g h
    simpa [semilinearCongruence, coefficient_one] using hg.symm.trans hh.symm

/-- A coefficient of order dividing two is identity or the prescribed quadratic Frobenius. -/
theorem coefficient_sq_eq_one (τ : E n ≃+* E n) (hτ : τ ^ 2 = 1) :
    τ = 1 ∨ τ = sigma n := by
  by_cases hne : τ = 1
  · exact Or.inl hne
  right
  obtain ⟨m, _, hm, h⟩ :=
    FiniteField.BinaryTorusTwoPower.involution_eq_half_frobenius (card_E n) τ hτ hne
  have hmn : m = n := by omega
  ext x
  change τ x = iterateFrobeniusEquiv (E n) 2 n x
  rw [h, hmn]
  simp only [iterateFrobeniusEquiv_def]

/-- An outer normalizer involution has exactly the quadratic coefficient.
This is the matrix input for semilinear descent. -/
theorem outer_involution_expression (hCoverage : NormalizerCoverage n)
    (i : Space n ≃ₗ[ZMod 2] Space n) (hiN : i ∈ binaryNormalizer n)
    (hi2 : orderOf i = 2) (hiL : i ∉ binaryImage n) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 3) (E n), ∀ X : Space n,
      (i X).val = g.val * X.val.map (sigma n) * adjoint n g.val := by
  let e : binaryNormalizer n := ⟨i, hiN⟩
  have hi : i ^ 2 = 1 := by simpa only [hi2] using pow_orderOf_eq_one i
  have he : e ^ 2 = 1 := Subtype.ext hi
  have ht : normalizerCoefficient n hCoverage e ^ 2 = 1 := by
    rw [← map_pow, he, map_one]
  have hts : normalizerCoefficient n hCoverage e = sigma n := by
    rcases coefficient_sq_eq_one n _ ht with h | h
    · exact False.elim (hiL (mem_binaryImage_of_mem_congruenceImage_of_sq_eq_one n i
        ((normalizerCoefficient_eq_one_iff n hCoverage e).mp h) hi))
    · exact h
  obtain ⟨g, hg⟩ := normalizerCoefficient_spec n hCoverage e
  rw [hts] at hg
  exact ⟨g, fun X => congrArg (fun a : Space n ≃ₗ[ZMod 2] Space n => (a X).val) hg⟩

/-- The elementary outer index is the literal index in A of A ∩ L. -/
theorem elementary_relIndex_le_two (hCoverage : NormalizerCoverage n)
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hA : IsElementaryAbelian 2 A)
    (hAN : A ≤ binaryNormalizer n) : (binaryImage n).relIndex A ≤ 2 := by
  classical
  let := hA
  let f : A →* (E n ≃+* E n) :=
    (normalizerCoefficient n hCoverage).comp (Subgroup.inclusion hAN)
  have hker : (binaryImage n).subgroupOf A = f.ker := by
    ext a
    change a.val ∈ binaryImage n ↔
      normalizerCoefficient n hCoverage ⟨a.val, hAN a.property⟩ = 1
    rw [normalizerCoefficient_eq_one_iff]
    exact ⟨fun h => binaryImage_le_congruenceImage n h, fun h =>
      mem_binaryImage_of_mem_congruenceImage_of_sq_eq_one n a.val h
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) a.val a.property)⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker]
  let s : Finset (E n ≃+* E n) := {1, sigma n}
  have hs (x : f.range) : x.val ∈ s := by
    obtain ⟨a, ha⟩ := x.property
    have h2 : a ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) a.val a.property)
    have hfx : x.val ^ 2 = 1 := by rw [← ha, ← map_pow, h2, map_one]
    simpa only [s, Finset.mem_insert, Finset.mem_singleton] using coefficient_sq_eq_one n x.val hfx
  let j : f.range → ↥s := fun x => ⟨x.val, hs x⟩
  have hj : Function.Injective j := fun x y h =>
    Subtype.ext (congrArg (fun z : ↥s => z.val) h)
  refine (Nat.card_le_card_of_injective j hj).trans ?_
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    (Finset.card_le_two (a := (1 : E n ≃+* E n)) (b := sigma n))

end Representation.HermitianTensorThree.ImageOuter.OuterRank.Coefficients
