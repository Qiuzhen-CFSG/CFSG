module

public import Stellmacher.Recognition.FongWreathedInducingFunctions
public import Stellmacher.Recognition.FongWreathedInducingData
public import Stellmacher.Recognition.FongWreathedActualInducingData
public import Theory.Character.InductionSpecialSupport
public import Stellmacher.Recognition.FongWreathedSpecialSupport

/-!
# Actual induced generalized characters in Fong's wreathed calculation

Given the explicit normalizer data, the linear characters descend to H/U,
with the prescribed values on F and X. Their virtual combinations are
supported on the odd F cosets. Unique normal forms F^i X^j u reduce the
three local scalar products to sixteen terms, giving 4, 4, and 0.
The support is exactly the set on which the first function has value four,
and is closed under conjugation in H.

The explicit normalizer witness and the special-support transporter theorem
discharge all inputs for every height-two wreathed Sylow presentation.
Frobenius reciprocity transfers the Gram products to the ambient induced
functions, and induction agrees with each local function on the support.
Both induced functions vanish at the identity and the central involution.
The stronger local result therefore applies in particular under Fong's
original simplicity and solvable involution-centralizer hypotheses.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), 65–76, printed p. 72. The page image writes
the second function as (alpha - alpha^3)(1 + beta); `thetaTwo_conj_formula`
identifies this with the conjugate formula.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Stellmacher.Recognition.FongWreathedInduction
attribute [local instance] Fintype.ofFinite
namespace InducingData
variable {G : Type*} [Group G] (d : InducingData G)

instance : d.U.Normal := d.normal_U

def quotientAlpha : d.H ⧸ d.U →* ℂ :=
  QuotientGroup.lift d.U d.alpha (by
    intro u hu
    exact d.alpha_U ⟨u, hu⟩)

def quotientBeta : d.H ⧸ d.U →* ℂ :=
  QuotientGroup.lift d.U d.beta (by
    intro u hu
    exact d.beta_U ⟨u, hu⟩)

@[simp] theorem quotientAlpha_mk (h : d.H) :
    d.quotientAlpha (QuotientGroup.mk' d.U h) = d.alpha h := rfl
@[simp] theorem quotientBeta_mk (h : d.H) :
    d.quotientBeta (QuotientGroup.mk' d.U h) = d.beta h := rfl

theorem thetaOne_normalForm (i : Fin 8) (j : Fin 2) (u : d.U) :
    thetaOne d.alpha d.beta (d.f ^ i.val * d.x ^ j.val * u.val) =
      (1 - (Complex.I ^ i.val) ^ 2) * (1 + (-1 : ℂ) ^ j.val) := by
  rw [thetaOne_apply]
  simp only [map_mul, map_pow, d.alpha_f, d.alpha_x, d.alpha_U,
    d.beta_f, d.beta_x, d.beta_U, one_pow, mul_one, one_mul]

theorem thetaTwo_normalForm (i : Fin 8) (j : Fin 2) (u : d.U) :
    thetaTwo d.alpha d.beta (d.f ^ i.val * d.x ^ j.val * u.val) =
      (Complex.I ^ i.val - (Complex.I ^ i.val) ^ 3) * (1 + (-1 : ℂ) ^ j.val) := by
  rw [thetaTwo_apply]
  simp only [map_mul, map_pow, d.alpha_f, d.alpha_x, d.alpha_U,
    d.beta_f, d.beta_x, d.beta_U, one_pow, mul_one, one_mul]

theorem alpha_four (h : d.H) : d.alpha h ^ 4 = 1 := by
  obtain ⟨⟨i, j, u⟩, rfl⟩ := d.normal_form.surjective h
  simp only [map_mul, map_pow, d.alpha_f, d.alpha_x, d.alpha_U, one_pow, mul_one]
  rw [← pow_mul, Nat.mul_comm, pow_mul, Complex.I_pow_four, one_pow]

theorem beta_two (h : d.H) : d.beta h ^ 2 = 1 := by
  obtain ⟨⟨i, j, u⟩, rfl⟩ := d.normal_form.surjective h
  simp only [map_mul, map_pow, d.beta_f, d.beta_x, d.beta_U, one_pow, mul_one, one_mul]
  fin_cases j <;> norm_num

theorem thetaOne_supported : supportedOn (thetaOne d.alpha d.beta) d.support := by
  intro h hh
  obtain ⟨⟨i, j, u⟩, rfl⟩ := d.normal_form.surjective h
  rw [thetaOne_normalForm]
  by_cases hi : Odd i.val
  · have hj : j ≠ 0 := by
      intro hj
      apply hh
      refine ⟨i, hi, u, ?_⟩
      simp [hj]
    fin_cases j
    · exact (hj rfl).elim
    · norm_num
  · have hs : (Complex.I ^ i.val) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, Complex.I_sq,
        (Nat.not_odd_iff_even.mp hi).neg_one_pow]
    rw [hs, sub_self, zero_mul]

theorem thetaTwo_supported : supportedOn (thetaTwo d.alpha d.beta) d.support := by
  intro h hh
  obtain ⟨⟨i, j, u⟩, rfl⟩ := d.normal_form.surjective h
  rw [thetaTwo_normalForm]
  by_cases hi : Odd i.val
  · have hj : j ≠ 0 := by
      intro hj
      apply hh
      refine ⟨i, hi, u, ?_⟩
      simp [hj]
    fin_cases j
    · exact (hj rfl).elim
    · norm_num
  · have hs : (Complex.I ^ i.val) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, Complex.I_sq,
        (Nat.not_odd_iff_even.mp hi).neg_one_pow]
    rw [pow_succ, hs, one_mul, sub_self, zero_mul]

@[simp] theorem quotientAlpha_f : d.quotientAlpha (QuotientGroup.mk' d.U d.f) = Complex.I :=
  d.alpha_f

@[simp] theorem quotientAlpha_x : d.quotientAlpha (QuotientGroup.mk' d.U d.x) = 1 :=
  d.alpha_x

@[simp] theorem quotientBeta_f : d.quotientBeta (QuotientGroup.mk' d.U d.f) = 1 :=
  d.beta_f

@[simp] theorem quotientBeta_x : d.quotientBeta (QuotientGroup.mk' d.U d.x) = -1 :=
  d.beta_x

theorem thetaOne_on_support (h : d.H) (hh : h ∈ d.support) :
    thetaOne d.alpha d.beta h = 4 := by
  obtain ⟨i, hi, u, rfl⟩ := hh
  rw [thetaOne_apply]
  simp only [map_mul, map_pow, d.alpha_f, d.alpha_U,
    d.beta_f, d.beta_U, one_pow, mul_one]
  have hs : (Complex.I ^ i.val) ^ 2 = -1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, Complex.I_sq, hi.neg_one_pow]
  rw [hs]
  norm_num

theorem thetaOne_eq_four_iff (h : d.H) :
    thetaOne d.alpha d.beta h = 4 ↔ h ∈ d.support := by
  constructor
  · intro he
    by_contra hn
    have hz := d.thetaOne_supported h hn
    rw [he] at hz
    norm_num at hz
  · exact d.thetaOne_on_support h

theorem thetaOne_inflated (h : d.H) :
    thetaOne d.alpha d.beta h =
      thetaOne d.quotientAlpha d.quotientBeta (QuotientGroup.mk' d.U h) := rfl

theorem thetaTwo_inflated (h : d.H) :
    thetaTwo d.alpha d.beta h =
      thetaTwo d.quotientAlpha d.quotientBeta (QuotientGroup.mk' d.U h) := rfl

variable [Finite G]

theorem quotientAlpha_linear : IsLinearCharacter (d.quotientAlpha : d.H ⧸ d.U → ℂ) :=
  BenderGlauberman.isLinearCharacter_of_hom d.quotientAlpha.toHomUnits

theorem quotientBeta_linear : IsLinearCharacter (d.quotientBeta : d.H ⧸ d.U → ℂ) :=
  BenderGlauberman.isLinearCharacter_of_hom d.quotientBeta.toHomUnits

omit [Finite G] in
theorem card_H : Nat.card d.H = 16 * Nat.card d.U := by
  have hc := Nat.card_congr (Equiv.ofBijective _ d.normal_form)
  simp only [Nat.card_prod, Nat.card_fin] at hc
  omega

theorem sum_normalForm (φ : d.H → ℂ) :
    ∑ h : d.H, φ h = ∑ i : Fin 8, ∑ j : Fin 2, ∑ u : d.U,
      φ (d.f ^ i.val * d.x ^ j.val * u.val) := by
  rw [← (Equiv.ofBijective _ d.normal_form).sum_comp φ]
  exact Fintype.sum_prod_type _ |>.trans (by
    apply Finset.sum_congr rfl
    intro i _
    exact Fintype.sum_prod_type _)

theorem scalarProduct_one_one :
    scalarProduct d.H (thetaOne d.alpha d.beta) (thetaOne d.alpha d.beta) = 4 := by
  unfold scalarProduct
  rw [d.card_H, d.sum_normalForm]
  simp_rw [d.thetaOne_normalForm]
  simp only [Finset.sum_const, nsmul_eq_mul]
  norm_num [Fin.sum_univ_succ, pow_succ, Complex.I_mul_I]
  have hu : (Fintype.card d.U : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring_nf

theorem scalarProduct_two_two :
    scalarProduct d.H (thetaTwo d.alpha d.beta) (thetaTwo d.alpha d.beta) = 4 := by
  unfold scalarProduct
  rw [d.card_H, d.sum_normalForm]
  simp_rw [d.thetaTwo_normalForm]
  simp only [Finset.sum_const, nsmul_eq_mul]
  norm_num [Fin.sum_univ_succ, pow_succ, Complex.I_mul_I]
  have hu : (Fintype.card d.U : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring_nf
  norm_num [Complex.I_sq]

theorem scalarProduct_one_two :
    scalarProduct d.H (thetaOne d.alpha d.beta) (thetaTwo d.alpha d.beta) = 0 := by
  unfold scalarProduct
  rw [d.sum_normalForm]
  simp_rw [d.thetaOne_normalForm, d.thetaTwo_normalForm]
  simp only [Finset.sum_const, nsmul_eq_mul]
  norm_num [Fin.sum_univ_succ, pow_succ, Complex.I_mul_I]
  ring

theorem support_conj (h y : d.H) (hh : h ∈ d.support) :
    y * h * y⁻¹ ∈ d.support := by
  apply (d.thetaOne_eq_four_iff _).mp
  rw [BenderGlauberman.isClassFunction_of_isGeneralizedCharacter
    (thetaOne_generalized d.alpha d.beta) h y]
  exact d.thetaOne_on_support h hh

/-- Induction preserves scalar products for functions on the special support. -/
theorem scalarProduct_induced (hs : d.HasSpecialSupport)
    (φ ψ : ClassFunction d.H) (hψ : IsClassFunction ψ)
    (hφs : supportedOn φ d.support) (hψs : supportedOn ψ d.support) :
    scalarProduct G (inducedClassFunction d.H φ) (inducedClassFunction d.H ψ) =
      scalarProduct d.H φ ψ :=
  scalarProduct_inducedClassFunction_of_specialSupport d.H d.support hs φ ψ hψ hφs hψs

/-- The first ambient induced function has norm four. -/
theorem scalarProduct_induced_one_one (hs : d.HasSpecialSupport) :
    scalarProduct G (inducedOne d.H d.alpha d.beta) (inducedOne d.H d.alpha d.beta) = 4 := by
  rw [inducedOne, d.scalarProduct_induced hs _ _
    (BenderGlauberman.isClassFunction_of_isGeneralizedCharacter
      (thetaOne_generalized d.alpha d.beta)) d.thetaOne_supported d.thetaOne_supported]
  exact d.scalarProduct_one_one

/-- The second ambient induced function has norm four. -/
theorem scalarProduct_induced_two_two (hs : d.HasSpecialSupport) :
    scalarProduct G (inducedTwo d.H d.alpha d.beta) (inducedTwo d.H d.alpha d.beta) = 4 := by
  rw [inducedTwo, d.scalarProduct_induced hs _ _
    (BenderGlauberman.isClassFunction_of_isGeneralizedCharacter
      (thetaTwo_generalized d.alpha d.beta)) d.thetaTwo_supported d.thetaTwo_supported]
  exact d.scalarProduct_two_two

/-- The two ambient induced functions are orthogonal. -/
theorem scalarProduct_induced_one_two (hs : d.HasSpecialSupport) :
    scalarProduct G (inducedOne d.H d.alpha d.beta) (inducedTwo d.H d.alpha d.beta) = 0 := by
  rw [inducedOne, inducedTwo, d.scalarProduct_induced hs _ _
    (BenderGlauberman.isClassFunction_of_isGeneralizedCharacter
      (thetaTwo_generalized d.alpha d.beta)) d.thetaOne_supported d.thetaTwo_supported]
  exact d.scalarProduct_one_two

/-- Both induced functions vanish at the chosen central Sylow involution. -/
theorem induced_at_J (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2) :
    inducedOne d.H d.alpha d.beta ((FongWreathedIntrinsic.J P : S) : G) = 0 ∧
    inducedTwo d.H d.alpha d.beta ((FongWreathedIntrinsic.J P : S) : G) = 0 := by
  have hj : ((FongWreathedIntrinsic.J P : S) : G) ^ 2 = 1 := by
    have hlocal : FongWreathedIntrinsic.J P ^ 2 = 1 := by
      simpa only [FongWreathedIntrinsic.J_orderOf] using
        pow_orderOf_eq_one (FongWreathedIntrinsic.J P)
    exact_mod_cast hlocal
  exact ⟨inducedOne_eq_zero_of_sq d.H d.alpha d.beta _ hj,
    inducedTwo_eq_zero_of_sq d.H d.alpha d.beta _ hj⟩

/-- The conditional ambient generalized-character and Gram data for Fong's
exceptional-function construction, including both required vanishing values. -/
theorem induced_gram_data (hs : d.HasSpecialSupport)
    (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2) :
    IsGeneralizedCharacter (inducedOne d.H d.alpha d.beta) ∧
    IsGeneralizedCharacter (inducedTwo d.H d.alpha d.beta) ∧
    scalarProduct G (inducedOne d.H d.alpha d.beta) (inducedOne d.H d.alpha d.beta) = 4 ∧
    scalarProduct G (inducedTwo d.H d.alpha d.beta) (inducedTwo d.H d.alpha d.beta) = 4 ∧
    scalarProduct G (inducedOne d.H d.alpha d.beta) (inducedTwo d.H d.alpha d.beta) = 0 ∧
    inducedOne d.H d.alpha d.beta 1 = 0 ∧
    inducedTwo d.H d.alpha d.beta 1 = 0 ∧
    inducedOne d.H d.alpha d.beta ((FongWreathedIntrinsic.J P : S) : G) = 0 ∧
    inducedTwo d.H d.alpha d.beta ((FongWreathedIntrinsic.J P : S) : G) = 0 :=
  ⟨inducedOne_generalized d.H d.alpha d.beta,
    inducedTwo_generalized d.H d.alpha d.beta,
    d.scalarProduct_induced_one_one hs, d.scalarProduct_induced_two_two hs,
    d.scalarProduct_induced_one_two hs, inducedOne_one d.H d.alpha d.beta,
    inducedTwo_one d.H d.alpha d.beta, d.induced_at_J S P⟩


omit [Finite G] in
/-- The second local function is four times alpha on the support. -/
theorem thetaTwo_on_support (h : d.H) (hh : h ∈ d.support) :
    thetaTwo d.alpha d.beta h = 4 * d.alpha h := by
  obtain ⟨i, hi, u, rfl⟩ := hh
  rw [thetaTwo_apply]
  simp only [map_mul, map_pow, d.alpha_f, d.alpha_U,
    d.beta_f, d.beta_U, one_pow, mul_one]
  have hs : (Complex.I ^ i.val) ^ 2 = -1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, Complex.I_sq, hi.neg_one_pow]
  rw [pow_succ, hs]
  ring

/-- Induction preserves the value four of the first local function. -/
theorem inducedOne_on_support (hs : d.HasSpecialSupport)
    (h : d.H) (hh : h ∈ d.support) : inducedOne d.H d.alpha d.beta h = 4 := by
  exact (inducedClassFunction_eq_on_specialSupport d.H d.support hs _
    (BenderGlauberman.isClassFunction_of_isGeneralizedCharacter
      (thetaOne_generalized d.alpha d.beta)) d.thetaOne_supported h hh).trans
    (d.thetaOne_on_support h hh)

/-- Induction preserves the second local function on the special support. -/
theorem inducedTwo_on_support (hs : d.HasSpecialSupport)
    (h : d.H) (hh : h ∈ d.support) :
    inducedTwo d.H d.alpha d.beta h = 4 * d.alpha h := by
  exact (inducedClassFunction_eq_on_specialSupport d.H d.support hs _
    (BenderGlauberman.isClassFunction_of_isGeneralizedCharacter
      (thetaTwo_generalized d.alpha d.beta)) d.thetaTwo_supported h hh).trans
    (d.thetaTwo_on_support h hh)

/-- The union of ambient conjugacy classes meeting the odd F cosets. -/
def ambientSupport : Set G := {g | ∃ h : d.H, h ∈ d.support ∧ IsConj (h : G) g}

/-- Induction of a supported function vanishes off the ambient conjugacy closure. -/
theorem induced_supported {φ : ClassFunction d.H} (hφ : supportedOn φ d.support) :
    supportedOn (inducedClassFunction d.H φ) d.ambientSupport := by
  classical
  intro g hg
  unfold inducedClassFunction
  have hz : ∀ x : G, (if h : x⁻¹ * g * x ∈ d.H then φ ⟨_, h⟩ else 0) = 0 := by
    intro x
    split
    · next hx =>
      apply hφ
      intro hh
      apply hg
      refine ⟨⟨_, hx⟩, hh, isConj_iff.mpr ⟨x, ?_⟩⟩
      change x * (x⁻¹ * g * x) * x⁻¹ = g
      group
    · rfl
  simp only [hz, Finset.sum_const_zero, mul_zero]

/-- The first induced function is supported on the ambient special classes. -/
theorem inducedOne_supported :
    supportedOn (inducedOne d.H d.alpha d.beta) d.ambientSupport :=
  d.induced_supported d.thetaOne_supported

/-- The second induced function is supported on the ambient special classes. -/
theorem inducedTwo_supported :
    supportedOn (inducedTwo d.H d.alpha d.beta) d.ambientSupport :=
  d.induced_supported d.thetaTwo_supported

/-- The first induced function has value four throughout its ambient support. -/
theorem inducedOne_eq_four_on_ambientSupport (hs : d.HasSpecialSupport)
    (g : G) (hg : g ∈ d.ambientSupport) : inducedOne d.H d.alpha d.beta g = 4 := by
  obtain ⟨h, hh, hc⟩ := hg
  obtain ⟨x, hx⟩ := isConj_iff.mp hc
  rw [← hx, BenderGlauberman.isClassFunction_of_isGeneralizedCharacter
    (inducedOne_generalized d.H d.alpha d.beta)]
  exact d.inducedOne_on_support hs h hh

/-- The first induced function has only the values four and zero. -/
theorem inducedOne_eq_four_or_zero (hs : d.HasSpecialSupport) (g : G) :
    inducedOne d.H d.alpha d.beta g = 4 ∨ inducedOne d.H d.alpha d.beta g = 0 := by
  by_cases hg : g ∈ d.ambientSupport
  · exact Or.inl (d.inducedOne_eq_four_on_ambientSupport hs g hg)
  · exact Or.inr (d.inducedOne_supported g hg)

/-- The first induced function is integer-valued, for the rationality argument. -/
theorem inducedOne_integerValued (hs : d.HasSpecialSupport) (g : G) :
    ∃ z : ℤ, inducedOne d.H d.alpha d.beta g = (z : ℂ) := by
  rcases d.inducedOne_eq_four_or_zero hs g with h | h
  · exact ⟨4, h⟩
  · exact ⟨0, by simpa only [Int.cast_zero] using h⟩

/-- The explicit induced values on the odd F cosets, used in constituent extraction. -/
theorem induced_on_odd_coset (hs : d.HasSpecialSupport)
    (i : Fin 8) (hi : Odd i.val) (u : d.U) :
    inducedOne d.H d.alpha d.beta ((d.f : G) ^ i.val * (u.val : G)) = 4 ∧
    inducedTwo d.H d.alpha d.beta ((d.f : G) ^ i.val * (u.val : G)) =
      4 * Complex.I ^ i.val := by
  have hh : d.f ^ i.val * u.val ∈ d.support := ⟨i, hi, u, rfl⟩
  constructor
  · exact d.inducedOne_on_support hs (d.f ^ i.val * u.val) hh
  · have h := d.inducedTwo_on_support hs (d.f ^ i.val * u.val) hh
    rw [map_mul, map_pow, d.alpha_f, d.alpha_U, mul_one] at h
    exact h


end InducingData

variable {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)

/-- The constructed actual normalizer data satisfies the special-support hypothesis. -/
theorem actualInducingData_hasSpecialSupport :
    (actualInducingData S P).HasSpecialSupport :=
  (actualInducingData S P).hasSpecialSupport_of_isActual S P
    (actualInducingData_isActual S P)

/-- The first actual generalized character induced from the prescribed normalizer. -/
noncomputable def actualInducedOne : ClassFunction G :=
  let d := actualInducingData S P
  inducedOne d.H d.alpha d.beta

/-- The second actual generalized character induced from the prescribed normalizer. -/
noncomputable def actualInducedTwo : ClassFunction G :=
  let d := actualInducingData S P
  inducedTwo d.H d.alpha d.beta

/-- Actual generalized characters with Gram entries 4, 4, 0 and vanishing at 1 and J.
No supplied inducing-data or support witness remains in the hypotheses. -/
theorem actual_induced_gram_data :
    IsGeneralizedCharacter (actualInducedOne S P) ∧
    IsGeneralizedCharacter (actualInducedTwo S P) ∧
    scalarProduct G (actualInducedOne S P) (actualInducedOne S P) = 4 ∧
    scalarProduct G (actualInducedTwo S P) (actualInducedTwo S P) = 4 ∧
    scalarProduct G (actualInducedOne S P) (actualInducedTwo S P) = 0 ∧
    actualInducedOne S P 1 = 0 ∧ actualInducedTwo S P 1 = 0 ∧
    actualInducedOne S P ((FongWreathedIntrinsic.J P : S) : G) = 0 ∧
    actualInducedTwo S P ((FongWreathedIntrinsic.J P : S) : G) = 0 :=
  (actualInducingData S P).induced_gram_data
    (actualInducingData_hasSpecialSupport S P) S P

/-- The actual induced functions have values 4 and 4 Iⁱ on every odd F coset. -/
theorem actual_induced_on_odd_coset (i : Fin 8) (hi : Odd i.val)
    (u : (actualInducingData S P).U) :
    actualInducedOne S P (((FongWreathedIntrinsic.F P : S) : G) ^ i.val * (u.val : G)) = 4 ∧
    actualInducedTwo S P (((FongWreathedIntrinsic.F P : S) : G) ^ i.val * (u.val : G)) =
      4 * Complex.I ^ i.val := by
  simpa only [actualInducedOne, actualInducedTwo, (actualInducingData_isActual S P).2.1] using
    (actualInducingData S P).induced_on_odd_coset
      (actualInducingData_hasSpecialSupport S P) i hi u

/-- The actual induced functions take the values 4 and 4 I at the prescribed F. -/
theorem actual_induced_at_F :
    actualInducedOne S P ((FongWreathedIntrinsic.F P : S) : G) = 4 ∧
    actualInducedTwo S P ((FongWreathedIntrinsic.F P : S) : G) = 4 * Complex.I := by
  simpa only [Fin.val_one, pow_one, OneMemClass.coe_one, mul_one] using
    actual_induced_on_odd_coset S P (1 : Fin 8) (by decide) 1

/-- The actual first induced function is integer-valued on the ambient group. -/
theorem actualInducedOne_integerValued (g : G) :
    ∃ z : ℤ, actualInducedOne S P g = (z : ℂ) :=
  (actualInducingData S P).inducedOne_integerValued
    (actualInducingData_hasSpecialSupport S P) g


end Stellmacher.Recognition.FongWreathedInduction
