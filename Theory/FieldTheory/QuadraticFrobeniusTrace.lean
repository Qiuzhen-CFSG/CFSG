module

public import Theory.FieldTheory.QuadraticFrobeniusFixed
public import Mathlib.Algebra.CharP.Two

/-!
# Binary quadratic trace coordinates

For the actual half-degree Frobenius on GF(2^(2n)), with n positive, the
fixed field and the kernel of x ↦ x + x^(2^n) both have order q = 2^n.
Every fixed-field value has a trace fiber of order q. We give the affine
parametrization, including its coordinate formulas, as well as cardinalities.

In characteristic two the trace kernel is the fixed field. A nonfixed element
u gives the trace-one element u / (u + σ(u)); multiplication by this element
provides a section over the fixed field. Translation then parametrizes each
fiber. The existing fixed-field cardinality theorem proves nontriviality of
the quadratic Frobenius, including q = 2.

These are the finite-field coordinates used for the antidiagonal unitary-four
model in Aschbacher--Smith, F.1.11–12, printed pp.262–264 of
`refs/quasithin.pdf`. They are independent of the group-theoretic assertions
of those results. The namespace `InvolutiveTrace` also applies to other
characteristic-two fields with a specified nontrivial involution.
-/

@[expose] public noncomputable section
namespace InvolutiveTrace
variable {F : Type*} [Field F] (σ : F ≃+* F)

/-- The quadratic trace, with values in the ambient field. -/
def trace : F →+ F := AddMonoidHom.id F + σ.toAddMonoidHom

@[simp] theorem trace_apply (x : F) : trace σ x = x + σ x := rfl

theorem trace_fixed (hσ : Function.Involutive σ) (x : F) :
    σ (trace σ x) = trace σ x := by
  rw [trace_apply, map_add, hσ x, add_comm]

variable [CharP F 2]

theorem trace_eq_zero_iff (x : F) : trace σ x = 0 ↔ σ x = x := by
  rw [trace_apply, CharTwo.add_eq_zero, eq_comm]

/-- In characteristic two, trace zero means fixed by the involution. -/
theorem ker_eq_fixed : (trace σ).ker = (FixedBy.subfield F σ).toAddSubgroup := by
  ext x
  exact trace_eq_zero_iff σ x

/-- Translation by a specified solution parametrizes a trace fiber. -/
def fiberEquivFixed (b z : F) (hz : trace σ z = b) :
    {x : F // trace σ x = b} ≃ FixedBy.subfield F σ where
  toFun x := ⟨x.val + z, by
    change σ (x.val + z) = x.val + z
    apply (trace_eq_zero_iff σ _).mp
    rw [map_add, x.property, hz, CharTwo.add_self_eq_zero]⟩
  invFun t := ⟨t.val + z, by
    rw [map_add, (trace_eq_zero_iff σ _).mpr t.property, zero_add, hz]⟩
  left_inv x := by
    apply Subtype.ext
    exact (add_assoc x.val z z).trans (by rw [CharTwo.add_self_eq_zero, add_zero])
  right_inv t := by
    apply Subtype.ext
    exact (add_assoc t.val z z).trans (by rw [CharTwo.add_self_eq_zero, add_zero])

@[simp] theorem fiberEquivFixed_apply (b z : F) (hz : trace σ z = b)
    (x : {x : F // trace σ x = b}) :
    (fiberEquivFixed σ b z hz x).val = x.val + z := rfl

@[simp] theorem fiberEquivFixed_symm_apply (b z : F) (hz : trace σ z = b)
    (t : FixedBy.subfield F σ) :
    ((fiberEquivFixed σ b z hz).symm t).val = t.val + z := rfl

theorem fiber_card_of_solution (b z : F) (hz : trace σ z = b) :
    Nat.card {x : F // trace σ x = b} = Nat.card (FixedBy.subfield F σ) :=
  Nat.card_congr (fiberEquivFixed σ b z hz)

theorem exists_trace_one (hσ : Function.Involutive σ) (hne : ∃ x, σ x ≠ x) :
    ∃ z, trace σ z = 1 := by
  obtain ⟨x, hx⟩ := hne
  have ht : trace σ x ≠ 0 := fun h => hx ((trace_eq_zero_iff σ x).mp h)
  refine ⟨x / trace σ x, ?_⟩
  rw [trace_apply, map_div₀, trace_fixed σ hσ, ← add_div]
  exact div_self ht

theorem exists_trace (hσ : Function.Involutive σ) (hne : ∃ x, σ x ≠ x)
    (b : F) (hb : σ b = b) : ∃ z, trace σ z = b := by
  obtain ⟨u, hu⟩ := exists_trace_one σ hσ hne
  refine ⟨b * u, ?_⟩
  rw [trace_apply, map_mul, hb, ← mul_add, ← trace_apply, hu, mul_one]

/-- The image of the trace is exactly the fixed field. -/
theorem exists_trace_iff (hσ : Function.Involutive σ) (hne : ∃ x, σ x ≠ x)
    (b : F) : (∃ z, trace σ z = b) ↔ σ b = b := by
  constructor
  · rintro ⟨z, rfl⟩
    exact trace_fixed σ hσ z
  · exact exists_trace σ hσ hne b

/-- The trace regarded as an additive map onto its actual fixed subfield. -/
def traceToFixed (hσ : Function.Involutive σ) : F →+ FixedBy.subfield F σ :=
  (trace σ).codRestrict (FixedBy.subfield F σ).toAddSubgroup (trace_fixed σ hσ)

theorem traceToFixed_surjective (hσ : Function.Involutive σ)
    (hne : ∃ x, σ x ≠ x) : Function.Surjective (traceToFixed σ hσ) := by
  intro b
  obtain ⟨z, hz⟩ := exists_trace σ hσ hne b.val b.property
  exact ⟨z, Subtype.ext hz⟩

/-- A trace-one element, obtained from a nonfixed element. -/
def traceOne (hσ : Function.Involutive σ) (hne : ∃ x, σ x ≠ x) : F :=
  Classical.choose (exists_trace_one σ hσ hne)

theorem trace_traceOne (hσ : Function.Involutive σ) (hne : ∃ x, σ x ≠ x) :
    trace σ (traceOne σ hσ hne) = 1 :=
  Classical.choose_spec (exists_trace_one σ hσ hne)

/-- A chosen solution for a fixed-field trace value. -/
def sectionValue (hσ : Function.Involutive σ) (hne : ∃ x, σ x ≠ x)
    (b : FixedBy.subfield F σ) : F := b.val * traceOne σ hσ hne

theorem trace_sectionValue (hσ : Function.Involutive σ) (hne : ∃ x, σ x ≠ x)
    (b : FixedBy.subfield F σ) : trace σ (sectionValue σ hσ hne b) = b.val := by
  have hb : σ b.val = b.val := b.property
  rw [sectionValue, trace_apply, map_mul, hb, ← mul_add, ← trace_apply,
    trace_traceOne, mul_one]

/-- Affine coordinates on every fixed-field trace fiber, with no solution premise. -/
def fiberEquiv (hσ : Function.Involutive σ) (hne : ∃ x, σ x ≠ x)
    (b : FixedBy.subfield F σ) :
    {x : F // trace σ x = b.val} ≃ FixedBy.subfield F σ :=
  fiberEquivFixed σ b.val (sectionValue σ hσ hne b) (trace_sectionValue σ hσ hne b)

@[simp] theorem fiberEquiv_symm_apply (hσ : Function.Involutive σ)
    (hne : ∃ x, σ x ≠ x) (b t : FixedBy.subfield F σ) :
    ((fiberEquiv σ hσ hne b).symm t).val = t.val + sectionValue σ hσ hne b := rfl

theorem fiber_card (hσ : Function.Involutive σ) (hne : ∃ x, σ x ≠ x)
    (b : F) (hb : σ b = b) :
    Nat.card {x : F // trace σ x = b} = Nat.card (FixedBy.subfield F σ) := by
  obtain ⟨z, hz⟩ := exists_trace σ hσ hne b hb
  exact fiber_card_of_solution σ b z hz
end InvolutiveTrace

namespace GaloisField.BinaryQuadratic
/-- The matrix field has order q²; the unitary parameter is q = 2^n. -/
abbrev MatrixField (n : ℕ) := GaloisField 2 (2 * n)

/-- The specified Hermitian conjugation, rather than a chosen abstract involution. -/
def conj (n : ℕ) : MatrixField n ≃+* MatrixField n :=
  iterateFrobeniusEquiv (MatrixField n) 2 n

@[simp] theorem conj_apply (n : ℕ) (x : MatrixField n) :
    conj n x = x ^ (2 ^ n) := rfl

abbrev FixedField (n : ℕ) := FixedBy.subfield (MatrixField n) (conj n)

theorem matrixField_card (n : ℕ) (hn : n ≠ 0) :
    Nat.card (MatrixField n) = (2 ^ n) ^ 2 := by
  rw [GaloisField.card 2 (2 * n) (by omega), Nat.mul_comm 2 n, pow_mul]

theorem fixedField_card (n : ℕ) (hn : n ≠ 0) :
    Nat.card (FixedField n) = 2 ^ n :=
  GaloisField.card_fixedBy_quadraticFrobenius 2 n hn

theorem conj_involutive (n : ℕ) (hn : n ≠ 0) :
    Function.Involutive (conj n) := by
  intro x
  rw [conj_apply, conj_apply, ← pow_mul, ← pow_two, ← matrixField_card n hn]
  let := Fintype.ofFinite (MatrixField n)
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem conj_nontrivial (n : ℕ) (hn : n ≠ 0) :
    ∃ x : MatrixField n, conj n x ≠ x := by
  by_contra! h
  let e : FixedField n ≃ MatrixField n :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, h x⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have hc := Nat.card_congr e
  rw [fixedField_card n hn, matrixField_card n hn] at hc
  have hq : 1 < 2 ^ n := Nat.one_lt_pow hn (by omega)
  nlinarith

abbrev trace (n : ℕ) : MatrixField n →+ MatrixField n := InvolutiveTrace.trace (conj n)

@[simp] theorem trace_apply (n : ℕ) (x : MatrixField n) :
    trace n x = x + x ^ (2 ^ n) := rfl

theorem exists_trace_iff (n : ℕ) (hn : n ≠ 0) (b : MatrixField n) :
    (∃ x, trace n x = b) ↔ conj n b = b :=
  InvolutiveTrace.exists_trace_iff (conj n) (conj_involutive n hn) (conj_nontrivial n hn) b

/-- The affine parametrization of the literal quadratic Frobenius trace fiber. -/
def traceFiberEquiv (n : ℕ) (hn : n ≠ 0) (b : FixedField n) :
    {x : MatrixField n // trace n x = b.val} ≃ FixedField n :=
  InvolutiveTrace.fiberEquiv (conj n) (conj_involutive n hn) (conj_nontrivial n hn) b

theorem traceKernel_card (n : ℕ) (hn : n ≠ 0) :
    Nat.card (trace n).ker = 2 ^ n := by
  rw [InvolutiveTrace.ker_eq_fixed]
  exact fixedField_card n hn

theorem traceFiber_card (n : ℕ) (hn : n ≠ 0) (b : MatrixField n)
    (hb : conj n b = b) : Nat.card {x : MatrixField n // trace n x = b} = 2 ^ n := by
  rw [InvolutiveTrace.fiber_card (conj n) (conj_involutive n hn) (conj_nontrivial n hn) b hb]
  exact fixedField_card n hn
end GaloisField.BinaryQuadratic
