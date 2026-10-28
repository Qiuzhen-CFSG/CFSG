module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Parity

/-!
# Cyclic norms onto a fixed subgroup of exponent two

For a finite-period automorphism of an abelian group, multiply one full orbit.
The resulting homomorphism is invariant under the automorphism and takes values
in its fixed subgroup. If the period is odd and that subgroup has exponent two,
the norm restricts to the identity there.

This supplies the elementary averaging step for the direct perfect-double-cover
argument associated to GLS4, Chapter 4, Lemma 2.8(c). No complement theorem or
assumption that the whole abelian group has exponent two is needed.
-/

open scoped BigOperators
namespace MulAut
variable {C : Type*} [CommGroup C]

public noncomputable def cyclicNorm (a : MulAut C) (r : ℕ) : C →* C :=
  ∏ i ∈ Finset.range r, (a ^ i).toMonoidHom

public theorem cyclicNorm_apply (a : MulAut C) (r : ℕ) (x : C) :
    cyclicNorm a r x = ∏ i ∈ Finset.range r, (a ^ i) x := by
  simp [cyclicNorm]

private theorem cyclicNorm_shift (a : MulAut C) (r : ℕ) (x : C) :
    cyclicNorm a r (a x) * x = (a ^ r) x * cyclicNorm a r x := by
  induction r with
  | zero => simp [cyclicNorm]
  | succ r ih =>
    simp only [cyclicNorm_apply, Finset.prod_range_succ] at ih ⊢
    have he : (a ^ r) (a x) = (a ^ (r + 1)) x := by rw [pow_succ]; rfl
    rw [he]
    calc
      (∏ i ∈ Finset.range r, (a ^ i) (a x)) * (a ^ (r + 1)) x * x =
          ((∏ i ∈ Finset.range r, (a ^ i) (a x)) * x) * (a ^ (r + 1)) x := by ac_rfl
      _ = _ := by rw [ih]; ac_rfl

public theorem cyclicNorm_invariant (a : MulAut C) {r : ℕ} (hr : a ^ r = 1) (x : C) :
    cyclicNorm a r (a x) = cyclicNorm a r x := by
  apply mul_right_cancel (b := x)
  simpa only [hr, MulAut.one_apply, mul_comm] using cyclicNorm_shift a r x

public theorem cyclicNorm_fixed (a : MulAut C) {r : ℕ} (hr : a ^ r = 1) (x : C) :
    a (cyclicNorm a r x) = cyclicNorm a r x := by
  rw [cyclicNorm_apply, map_prod]
  have he (i : ℕ) : a ((a ^ i) x) = (a ^ i) (a x) :=
    congrArg (fun b : MulAut C => b x) (Commute.self_pow a i).eq
  simp_rw [he]
  simpa only [cyclicNorm_apply] using cyclicNorm_invariant a hr x

public theorem cyclicNorm_of_fixed (a : MulAut C) (r : ℕ) (x : C) (hx : a x = x) :
    cyclicNorm a r x = x ^ r := by
  have hi (i : ℕ) : (a ^ i) x = x := by
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ']; change a ((a ^ i) x) = x; rw [ih, hx]
  simp [cyclicNorm_apply, hi]

public theorem exists_cyclicNorm_retraction (a : MulAut C) {r : ℕ}
    (hr : a ^ r = 1) (hodd : Odd r) (A : Subgroup C)
    (hfixed : ∀ x, a x = x ↔ x ∈ A)
    (hsq : ∀ x ∈ A, x ^ 2 = 1) :
    ∃ n : C →* A, (∀ x : A, n x = x) ∧ (∀ x, n (a x) = n x) := by
  let n := (cyclicNorm a r).codRestrict A
    (fun x => (hfixed _).mp (cyclicNorm_fixed a hr x))
  refine ⟨n, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    change cyclicNorm a r x = x
    rw [cyclicNorm_of_fixed a r x ((hfixed x).mpr x.property)]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_add, pow_mul, hsq x x.property, one_pow, pow_one, one_mul]
  · intro x
    apply Subtype.ext
    exact cyclicNorm_invariant a hr x
end MulAut
