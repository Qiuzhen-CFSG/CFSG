module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Tactic
/-!
# Products of Laurent polynomials with a unique highest monomial

An additive integer height detects a unique highest weight of coefficient
one. A product has that same property: equality of heights forces both
factors to attain their individual maximum, and the unique-product
coefficient formula gives coefficient one. The result extends to powers
and finite products and does not depend on the characteristic.

Source: the fundamental-orbit-sum triangular argument, Steinberg (1963), §3.9.
-/

open scoped BigOperators Pointwise
public section
namespace Theory.MonoidAlgebraHighestTerm
variable {F L : Type*} [Field F] [CommGroup L]

/-- A unique highest monomial with coefficient one. -/
@[expose] def LeadingAt (d : L → ℤ) (p : MonoidAlgebra F L) (a : L) : Prop :=
  p.coeff a = 1 ∧ (∀ x ∈ p.coeff.support, d x ≤ d a) ∧
    ∀ x ∈ p.coeff.support, d x = d a → x = a

lemma LeadingAt.mul {d : L → ℤ} (hd : ∀ a b, d (a * b) = d a + d b)
    {p q : MonoidAlgebra F L} {a b : L}
    (hp : LeadingAt d p a) (hq : LeadingAt d q b) : LeadingAt d (p * q) (a * b) := by
  classical
  have hu : UniqueMul p.coeff.support q.coeff.support a b := by
    intro x y hx hy hxy
    have hxd := hp.2.1 x hx
    have hyd := hq.2.1 y hy
    have hh : d x + d y = d a + d b := by rw [← hd, hxy, hd]
    exact ⟨hp.2.2 x hx (by omega), hq.2.2 y hy (by omega)⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [MonoidAlgebra.coeff_mul_mul_of_uniqueMul hu, hp.1, hq.1, one_mul]
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp
      (MonoidAlgebra.support_coeff_mul_subset p q hz)
    rw [hd, hd]
    exact add_le_add (hp.2.1 x hx) (hq.2.1 y hy)
  · intro z hz he
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp
      (MonoidAlgebra.support_coeff_mul_subset p q hz)
    have hxd := hp.2.1 x hx
    have hyd := hq.2.1 y hy
    rw [hd, hd] at he
    rw [hp.2.2 x hx (by omega), hq.2.2 y hy (by omega)]

lemma leadingAt_one (d : L → ℤ) : LeadingAt d (1 : MonoidAlgebra F L) 1 := by
  classical
  refine ⟨by simp, ?_, ?_⟩
  · intro x hx
    have he : x = 1 := by simpa using hx
    simp [he]
  · intro x hx _
    simpa using hx

lemma LeadingAt.pow {d : L → ℤ} (hd : ∀ a b, d (a * b) = d a + d b)
    {p : MonoidAlgebra F L} {a : L} (hp : LeadingAt d p a) (n : ℕ) :
    LeadingAt d (p ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using leadingAt_one d
  | succ n ih => simpa only [pow_succ] using ih.mul hd hp

lemma LeadingAt.finset_prod {d : L → ℤ} (hd : ∀ a b, d (a * b) = d a + d b)
    {I : Type*} (s : Finset I) (p : I → MonoidAlgebra F L) (a : I → L)
    (hp : ∀ i ∈ s, LeadingAt d (p i) (a i)) :
    LeadingAt d (∏ i ∈ s, p i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using leadingAt_one d
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    apply (hp i (Finset.mem_insert_self _ _)).mul hd
    exact ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
end Theory.MonoidAlgebraHighestTerm
