module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.ScalarMarking
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.FieldSimp

/-!
# Cubic norm and the triality source coefficient

Starting with one finite source field and its specified q-power automorphism,
construct the compatible scalar marking; its fixed-field marking is the
restriction of the same field equivalence. Torus covariance forces the unknown
coefficient in Fong--Seitz II (9.29)(ii) to have the shape (9.32). The polarization
identity (9.33) then forces its constant to be one, proving (9.34).

The normalization works uniformly at q=2: an additive cubic norm would be an
injective field homomorphism from q³ elements into q elements. This avoids a
separate enumeration of the two irreducible cubics over F₂. Surjectivity of the
torus character N(t)/t² is proved using square roots in the same source field.

These are coefficient calculations, not reconstruction of the source field,
its module actions, or its root groups. The source producer must prove the
covariance and polarization premises from those actions and commutators.
Source: Fong--Seitz, Groups with a (B,N)-Pair of Rank 2, II, pp.219--220,
equations (9.29)--(9.34).
-/

@[expose] public noncomputable section
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
variable {F : Type*} [Field F]
variable {n : ℕ} {hn : 0 < n} {σ : F ≃+* F}

/-- Mark the given field and the given power automorphism simultaneously. -/
def scalarMarking [Finite F] (hcard : Nat.card F = (2 ^ n)^3)
    (hσ : ∀ x, σ x = x ^ (2 ^ n)) : ScalarMarking (binaryParameters n hn) σ := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (ExtensionField (binaryParameters n hn)) := Fintype.ofFinite _
  let e : F ≃+* ExtensionField (binaryParameters n hn) := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans (card_extensionField (binaryParameters n hn)).symm)
  exact ⟨e, fun x => by rw [hσ, map_pow, fieldFrobenius_apply]; rfl⟩

variable (e : ScalarMarking (binaryParameters n hn) σ)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)

@[simp] theorem norm_zero : e.norm 0 = 0 := by
  apply Subtype.ext
  simp [ScalarMarking.norm]

@[simp] theorem norm_one : e.norm 1 = 1 := by
  apply Subtype.ext
  simp [ScalarMarking.norm]

@[simp] theorem norm_mul (x y : F) : e.norm (x*y) = e.norm x * e.norm y := by
  apply Subtype.ext
  simp only [ScalarMarking.norm, map_mul, Subfield.coe_mul]
  ring

@[simp] theorem norm_fixed (x : K) : e.norm x.val = x^3 := by
  apply Subtype.ext
  simp only [ScalarMarking.norm, show σ x.val = x.val from x.property, SubmonoidClass.coe_pow]
  ring

variable [CharP F 2]

@[simp] theorem trace_fixed (x : K) : e.trace x.val = x := by
  apply Subtype.ext
  simp only [ScalarMarking.trace, show σ x.val = x.val from x.property,
    CharTwo.add_self_eq_zero, zero_add]

/-- The six cross terms of cubic norm are the two source trace terms. -/
theorem norm_polarization (x y : F) :
    e.norm (x+y) + e.norm x + e.norm y =
      e.trace (x * σ x * σ (σ y)) + e.trace (x * σ y * σ (σ y)) := by
  apply Subtype.ext
  simp only [ScalarMarking.norm, ScalarMarking.trace, Subfield.coe_add, map_add, map_mul, e.cubic]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

/-- Norm cannot be additive from the proper cubic field to its fixed subfield.
This includes the field of eight elements. -/
theorem exists_norm_cross_nonzero [Finite F] :
    ∃ x y : F, e.norm (x+y) + e.norm x + e.norm y ≠ 0 := by
  by_contra h
  push Not at h
  let N : F →+* K := {
    toFun := e.norm
    map_one' := norm_one e
    map_mul' := norm_mul e
    map_zero' := norm_zero e
    map_add' := fun x y => by
      have he := h x y
      rw [add_assoc, CharTwo.add_eq_zero] at he
      exact he }
  have hc := Nat.card_le_card_of_injective N N.injective
  rw [Nat.card_congr e.extension.toEquiv, Nat.card_congr e.fixed.toEquiv,
    card_extensionField, card_fixedField] at hc
  have hq := (binaryParameters n hn).q_ge_two
  exact (not_lt_of_ge hc) (lt_self_pow₀ (by omega) (by decide : 1 < 3))

/-- Fong--Seitz (9.33) forces the constant to one, also when q=2. -/
theorem coefficient_one [Finite F] (c : K)
    (hc : ∀ x y : F, (e.norm (x+y) + e.norm x + e.norm y) * c =
      e.trace (x * σ x * σ (σ y)) + e.trace (x * σ y * σ (σ y))) : c = 1 := by
  obtain ⟨x, y, hxy⟩ := exists_norm_cross_nonzero e
  apply mul_left_cancel₀ hxy
  simpa only [mul_one, norm_polarization e] using hc x y

omit [CharP F 2] in
/-- The cubic norm has no nonzero zero. -/
theorem norm_ne_zero {x : F} (hx : x ≠ 0) : e.norm x ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  change x * σ x * σ (σ x) = 0 at h'
  exact mul_ne_zero (mul_ne_zero hx ((map_ne_zero σ).mpr hx))
    ((map_ne_zero σ).mpr ((map_ne_zero σ).mpr hx)) h'

omit [CharP F 2] in
@[simp] theorem norm_inv (x : F) : e.norm x⁻¹ = (e.norm x)⁻¹ := by
  apply Subtype.ext
  simp only [ScalarMarking.norm, map_inv₀, Subfield.coe_inv, mul_inv]

omit [CharP F 2] in
@[simp] theorem norm_div (x y : F) : e.norm (x/y) = e.norm x / e.norm y := by
  simp only [div_eq_mul_inv, norm_mul, norm_inv]

omit [CharP F 2] in
@[simp] theorem norm_square (x : F) : e.norm (x^2) = (e.norm x)^2 := by
  simp only [pow_two, norm_mul]

/-- The source torus character N(t)/t² is onto the nonzero cubic scalars.
A square root constructs its inverse, avoiding a separate exponent-coprimality calculation. -/
theorem exists_norm_div_square [Finite F] (a : F) (ha : a ≠ 0) :
    ∃ μ : F, μ ≠ 0 ∧ (e.norm μ).val / μ^2 = a ∧ e.norm μ = e.norm a := by
  obtain ⟨μ, hμ⟩ := (frobeniusEquiv F 2).surjective ((e.norm a).val / a)
  change μ^2 = (e.norm a).val / a at hμ
  have hNa := norm_ne_zero e ha
  have hNaF : (e.norm a).val ≠ 0 := fun h => hNa (Subtype.ext h)
  have hμ0 : μ ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide)] at hμ
    exact (div_ne_zero hNaF ha) hμ.symm
  have hNμ : e.norm μ = e.norm a := by
    apply frobenius_inj K 2
    change (e.norm μ)^2 = (e.norm a)^2
    have h := congrArg e.norm hμ
    rw [norm_square, norm_div, norm_fixed] at h
    rw [h]
    field_simp
  refine ⟨μ, hμ0, ?_, hNμ⟩
  rw [hNμ, hμ]
  field_simp

/-- The torus covariance printed immediately before (9.32). -/
def CoefficientCovariance (g : F → K → K) : Prop :=
  ∀ (l : K) (μ : F), l ≠ 0 → μ ≠ 0 → ∀ (a : F) (b : K),
    g (l.val / μ^2 * a) (l⁻¹^2 * e.norm μ * b) = l⁻¹ * g a b

/-- The full source torus covariance forces the shape in (9.32). -/
theorem coefficient_shape [Finite F] (g : F → K → K)
    (hg : CoefficientCovariance e g)
    (hzero_left : ∀ b, g 0 b = 0) (hzero_right : ∀ a, g a 0 = 0)
    (a : F) (b : K) : g a b = e.norm a * b^2 * g 1 1 := by
  by_cases ha : a = 0
  · simp [ha, hzero_left]
  by_cases hb : b = 0
  · simp [hb, hzero_right]
  have hbase (t : K) (ht : t ≠ 0) : g 1 t = t^2 * g 1 1 := by
    have htF : t.val ≠ 0 := fun h => ht (Subtype.ext h)
    have h := hg (t⁻¹^2) t.val⁻¹ (pow_ne_zero 2 (inv_ne_zero ht)) (inv_ne_zero htF) 1 1
    have hfirst : ((t⁻¹^2).val / (t.val⁻¹)^2 * (1 : F)) = 1 := by
      simp only [Subfield.coe_inv, SubmonoidClass.coe_pow, mul_one]
      exact div_self (pow_ne_zero 2 (inv_ne_zero htF))
    have hsecond : (t⁻¹^2)⁻¹^2 * e.norm t.val⁻¹ * 1 = t := by
      rw [norm_inv, norm_fixed]
      field_simp
    rw [hfirst, hsecond] at h
    simpa only [inv_pow, inv_inv] using h
  obtain ⟨μ, hμ0, hμa, hNμ⟩ := exists_norm_div_square e a ha
  have hNa := norm_ne_zero e ha
  have h := hg (e.norm μ) μ (norm_ne_zero e hμ0) hμ0 1 (e.norm a * b)
  have hsecond : (e.norm μ)⁻¹^2 * e.norm μ * (e.norm a * b) = b := by
    rw [hNμ]
    field_simp
  rw [hμa, mul_one, hsecond, hNμ, hbase _ (mul_ne_zero hNa hb)] at h
  rw [h]
  field_simp

/-- Equations (9.31) and (9.33) determine every coefficient in (9.34). -/
theorem coefficient_eq_norm [Finite F] (g : F → K → K)
    (hg : CoefficientCovariance e g)
    (hzero_left : ∀ b, g 0 b = 0) (hzero_right : ∀ a, g a 0 = 0)
    (hpolar : ∀ x y : F, (e.norm (x+y) + e.norm x + e.norm y) * g 1 1 =
      e.trace (x * σ x * σ (σ y)) + e.trace (x * σ y * σ (σ y)))
    (a : F) (b : K) : g a b = e.norm a * b^2 := by
  rw [coefficient_shape e g hg hzero_left hzero_right, coefficient_one e (g 1 1) hpolar,
    mul_one]

omit [CharP F 2] in
/-- Move the source Frobenius shift across the trace pairing. -/
theorem trace_shift (x y : F) : e.trace (x * σ y) = e.trace (σ (σ x) * y) := by
  apply Subtype.ext
  simp only [ScalarMarking.trace, map_mul, e.cubic]
  ring

omit [CharP F 2] in
/-- The two cyclic forms of the source short-short coefficient agree. -/
theorem trace_short_short (x y : F) :
    e.trace (σ x * σ (σ x) * y) = e.trace (x * σ x * σ (σ y)) := by
  apply Subtype.ext
  simp only [ScalarMarking.trace, map_mul, e.cubic]
  ring

/-- Reversing the two middle short factors contributes exactly the highest-root coefficient. -/
theorem trace_mixed_correction (x : F) (t : K) :
    e.trace (σ (σ (x*t.val)) * (x*σ x*t.val)) = e.norm x * t^2 := by
  have hf : σ t.val = t.val := t.property
  have he : σ (σ (x*t.val)) * (x*σ x*t.val) = (e.norm x * t^2).val := by
    simp only [ScalarMarking.norm, Subfield.coe_mul, SubmonoidClass.coe_pow, map_mul, hf]
    ring
  rw [he, trace_fixed]
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
