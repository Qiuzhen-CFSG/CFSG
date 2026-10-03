module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

/-!
# Involutions and right conjugation

An involution is a nonidentity element with square one. Right conjugation
preserves this predicate and conjugation by an involution is involutive.
The proofs are elementary group identities. Extracted from the Peterfalvi
Appendix III interfaces in `BenderSuzuki/PFAppendixIII/Basic.lean`, retaining
the existing public names and the shared prime-two instance.
-/

namespace BenderSuzuki.PFAppendixIII

/-- Local instance for the prime `2`, shared by Suzuki two-group coordinates and matrix models. -/
public instance instFactNatPrimeTwo : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- An involution is a nonidentity element whose square is one. -/
@[expose]
public def IsInvolution {G : Type*} [Group G] (x : G) : Prop :=
  x ≠ 1 ∧ x ^ 2 = 1

public theorem IsInvolution.ne_one {G : Type*} [Group G] {x : G} (hx : IsInvolution x)
    : x ≠ 1 :=
  hx.1

/-- A strongly real element is a product of two involutions. -/
@[expose]
public def IsStronglyReal {G : Type*} [Group G] (x : G) : Prop :=
  ∃ u v : G, IsInvolution u ∧ IsInvolution v ∧ x = u * v

public theorem IsInvolution.sq_eq_one {G : Type*} [Group G] {x : G} (hx : IsInvolution x)
    : x ^ 2 = 1 :=
  hx.2

public theorem IsInvolution.inv_eq_self {G : Type*} [Group G] {x : G}
    (hx : IsInvolution x)
    : x⁻¹ = x := by
  have hxx : x * x = 1 := by simpa [pow_two] using hx.sq_eq_one
  calc
    x⁻¹ = x⁻¹ * 1 := by simp
    _ = x⁻¹ * (x * x) := by rw [hxx]
    _ = x := by simp

/-- The set of involutions of a group. -/
@[expose]
public def involutions (G : Type*) [Group G] : Set G :=
  {x : G | IsInvolution x}

/-- The right-conjugate of an element, matching the Peterfalvi convention `x^g = g⁻¹ x g`. -/
@[expose]
public def rightConjugateElem {G : Type*} [Group G] (x g : G) : G :=
  g⁻¹ * x * g

public theorem isInvolution_rightConjugateElem {G : Type*} [Group G] {x g : G}
    (hx : IsInvolution x)
    : IsInvolution (rightConjugateElem x g) := by
  constructor
  · intro h
    apply hx.ne_one
    calc
      x = g * rightConjugateElem x g * g⁻¹ := by
        simp [rightConjugateElem, mul_assoc]
      _ = 1 := by simp [h]
  · calc
      (rightConjugateElem x g) ^ 2 = g⁻¹ * (x ^ 2) * g := by
        simp [rightConjugateElem, pow_two, mul_assoc]
      _ = 1 := by simp [hx.sq_eq_one]

public theorem rightConjugateElem_rightConjugateElem {G : Type*} [Group G] {a t : G}
    (htinv : t⁻¹ = t)
    : rightConjugateElem (rightConjugateElem a t) t = a := by
  have ht2 : t * t = 1 := by
    calc
      t * t = t⁻¹ * t := by rw [htinv]
      _ = 1 := inv_mul_cancel t
  calc
    rightConjugateElem (rightConjugateElem a t) t = t * t * a * t * t := by
      rw [rightConjugateElem, rightConjugateElem, htinv]
      group
    _ = a := by
      rw [ht2]
      simp only [one_mul]
      rw [mul_assoc, ht2, mul_one]

public theorem rightConjugateElem_involutive_of_isInvolution {G : Type*} [Group G] {t : G}
    (ht : IsInvolution t)
    : Function.Involutive (fun x : G => rightConjugateElem x t) := by
  intro x
  have htinv : t⁻¹ = t := ht.inv_eq_self
  have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
  calc
    rightConjugateElem (rightConjugateElem x t) t = t * (t * x) := by
      simp [rightConjugateElem, htinv, htt, mul_assoc]
    _ = (t * t) * x := by rw [mul_assoc]
    _ = x := by simp [htt]

end BenderSuzuki.PFAppendixIII
