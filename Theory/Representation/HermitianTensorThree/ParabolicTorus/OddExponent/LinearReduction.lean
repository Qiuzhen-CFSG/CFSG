module

public import Theory.Representation.HermitianTensorThree.ParabolicTorus.OddExponent.Inputs
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank.Coefficients
public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections.Pointwise

/-!
# Odd fixed-field linear normalizers are odd GL₃ congruences

The canonical coefficient homomorphism detects the field automorphism in a
semilinear congruence. Fixed-field linearity makes that coefficient fix F;
in the quadratic extension it has order dividing two. Odd order therefore
makes it trivial.

The congruence kernel consists of norm-one scalar matrices. A power landing
in this kernel is killed by the odd order of Eˣ, so every GL₃ lift of an odd
congruence has odd order. This keeps the actual central kernel throughout.
The application to both parabolic types and all conjugates is in the parent
`OddExponent` module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.2 setup,
printed p.380, and Proposition 8.2.3, printed pp.715–716.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ParabolicTorus.OddExponent
open ImageOuter ImageOuter.FieldSections ImageOuter.OuterRank.Coefficients
variable (n : ℕ) [NeZero n]

/-- Linearity of the actual operator over F forces its semilinear coefficient
to fix F pointwise. -/
theorem coefficient_fixes_of_isFixedFieldLinear (e : BinaryAut n)
    (he : IsFixedFieldLinear n e)
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (τ : E n ≃+* E n)
    (hexpr : e = semilinearCongruence n g τ) :
    ∀ c : F n, τ c.val = c.val := by
  intro c
  let D := diagonalUnit n 0
  have h := he c D
  rw [hexpr] at h
  change congruence n g (coefficient n τ (c • D)) =
    c • congruence n g (coefficient n τ D) at h
  rw [← map_smul] at h
  have hc := (congruence n g).injective h
  have hc00 := congrArg (fun X : Space n => X.val 0 0) hc
  simpa [coefficient_apply, D, diagonalUnit, Matrix.single_apply,
    Subfield.smul_def] using hc00

/-- An odd fixed-field linear element of the full binary normalizer is an
actual GL₃ congruence. -/
theorem mem_congruenceImage_of_odd_of_isFixedFieldLinear (e : BinaryAut n)
    (heN : e ∈ binaryNormalizer n) (ho : Odd (orderOf e))
    (he : IsFixedFieldLinear n e) : e ∈ congruenceImage n := by
  let a : binaryNormalizer n := ⟨e, heN⟩
  let f := normalizerCoefficient n (normalizerCoverage n)
  obtain ⟨g, hg⟩ := normalizerCoefficient_spec n (normalizerCoverage n) a
  have ht : ∀ c : F n, f a c.val = c.val :=
    coefficient_fixes_of_isFixedFieldLinear n e he g (f a) hg
  have h2 : f a ^ 2 = 1 := by
    rcases coefficient_eq_one_or_sigma n (f a) ht with h | h
    · rw [h, one_pow]
    · rw [h]
      ext z
      exact sigma_involutive n z
  have hod : Odd (orderOf (f a)) := ho.of_dvd_nat (by
    have ha : orderOf a = orderOf e := (Subgroup.orderOf_coe a).symm
    exact ha ▸ orderOf_map_dvd f a)
  have hone : f a = 1 := by
    apply orderOf_eq_one_iff.mp
    have hd := orderOf_dvd_of_pow_eq_one h2
    have : orderOf (f a) ∣ 1 := (Nat.coprime_two_right.mpr hod).dvd_of_dvd_mul_right
      (show orderOf (f a) ∣ 1 * 2 by simpa using hd)
    exact Nat.dvd_one.mp this
  exact (normalizerCoefficient_eq_one_iff n (normalizerCoverage n) a).mp hone

/-- The norm-one scalar kernel has odd exponent, so an odd congruence cannot
have a lift of even order. -/
theorem odd_orderOf_of_odd_binaryCongruence (g : Matrix.GeneralLinearGroup (Fin 3) (E n))
    (ho : Odd (orderOf (binaryCongruence n g))) : Odd (orderOf g) := by
  let m := orderOf (binaryCongruence n g)
  have hker : g ^ m ∈ (binaryCongruence n).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact pow_orderOf_eq_one _
  obtain ⟨c, hc, hnorm⟩ := (mem_binaryCongruence_ker_iff n (g ^ m)).mp hker
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hnorm
  let r := 2 ^ (2 * n) - 1
  have hcr : c ^ r = 1 := by
    let := Fintype.ofFinite (E n)
    simpa only [r, ← Nat.card_eq_fintype_card, card_E] using
      FiniteField.pow_card_sub_one_eq_one c hc0
  have hpow : g ^ (m * r) = 1 := by
    rw [pow_mul]
    apply Units.ext
    change (g ^ m).val ^ r = 1
    rw [hc, ← map_pow, hcr, map_one]
  have hrodd : Odd r := by
    apply Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide)) _ (by decide)
    exact even_iff_two_dvd.mpr (dvd_pow_self 2
      (Nat.mul_ne_zero (by decide) (NeZero.ne n)))
  exact (ho.mul hrodd).of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)

end Representation.HermitianTensorThree.ParabolicTorus.OddExponent
