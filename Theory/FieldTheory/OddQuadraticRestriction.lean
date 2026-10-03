module
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Tactic

/-!
# Injective restriction of odd quadratic-field automorphisms

An odd-order subgroup A of the actual automorphism group of GF(p^(2n)),
with n nonzero, restricts injectively to the fixed field of q-Frobenius.
For any supplied equivalence of that fixed field with GF(p^n), this module
constructs the transported homomorphism and records its exact compatibility
with the original automorphisms on fixed-field elements. The prime p need
not be odd.

Every field automorphism commutes with Frobenius, so it and its inverse
preserve the given fixed subfield. Restriction followed by the supplied
field equivalence therefore defines a group homomorphism. Its kernel embeds
into the automorphisms of the original field over the fixed field. The
finite-field cardinalities give extension degree two, so this kernel has
order at most two. Its order divides the odd order of A, hence is one.

This is the faithful coefficient restriction used in the equivariant
SU2–SL2 identification for ABG II.3 Proposition 3, article page 27.
The fixed subfield, its inclusion, and the supplied field equivalence are
retained throughout; no substitute automorphism representation is used.
-/

namespace GaloisField

public theorem exists_injective_odd_quadratic_restriction
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (A : Subgroup (GaloisField p (2 * n) ≃+* GaloisField p (2 * n)))
    (hA : Odd (Nat.card A))
    (b : (FixedBy.subfield (GaloisField p (2 * n))
      (iterateFrobeniusEquiv (GaloisField p (2 * n)) p n)) ≃+* GaloisField p n) :
    ∃ r : A →* (GaloisField p n ≃+* GaloisField p n), Function.Injective r ∧
      ∀ (σ : A) (x : FixedBy.subfield (GaloisField p (2 * n))
        (iterateFrobeniusEquiv (GaloisField p (2 * n)) p n)),
        σ.val x.val = (b.symm (r σ (b x))).val := by
  classical
  let E := GaloisField p (2 * n)
  let K := FixedBy.subfield E (iterateFrobeniusEquiv E p n)
  have hstable (σ : E ≃+* E) (x : K) : σ x.val ∈ K := by
    change (σ x.val) ^ (p ^ n) = σ x.val
    rw [← map_pow]
    exact congrArg σ x.property
  let res (σ : E ≃+* E) : K ≃+* K := {
    toFun x := ⟨σ x.val, hstable σ x⟩
    invFun x := ⟨σ.symm x.val, hstable σ.symm x⟩
    left_inv x := Subtype.ext (σ.symm_apply_apply x.val)
    right_inv x := Subtype.ext (σ.apply_symm_apply x.val)
    map_mul' x y := Subtype.ext (map_mul σ x.val y.val)
    map_add' x y := Subtype.ext (map_add σ x.val y.val) }
  let r : A →* (GaloisField p n ≃+* GaloisField p n) := {
    toFun σ := (b.symm.trans (res σ.val)).trans b
    map_one' := by ext x; simp [res]
    map_mul' σ τ := by ext x; simp [res] }
  have hr (σ : A) (x : K) : σ.val x.val = (b.symm (r σ (b x))).val := by
    simp [r, res]
  have hkfixed (σ : r.ker) (x : K) : σ.val.val x.val = x.val := by
    rw [hr σ.val x, show r σ.val = 1 from σ.property]
    simp
  let hker : r.ker → (E ≃ₐ[K] E) := fun σ =>
    AlgEquiv.ofRingEquiv (f := σ.val.val) (hkfixed σ)
  have hkerinj : Function.Injective hker := by
    intro σ τ h
    apply Subtype.ext
    apply Subtype.ext
    apply RingEquiv.ext
    intro x
    exact congrArg (fun e : E ≃ₐ[K] E => e x) h
  have hKcard : Nat.card K = p ^ n :=
    (Nat.card_congr b.toEquiv).trans (GaloisField.card p n hn)
  have hEcard : Nat.card E = (p ^ n) ^ 2 := by
    rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero (by decide) hn), ← pow_mul,
      Nat.mul_comm n 2]
  have hdegree : Module.finrank K E = 2 := by
    have hcard := Module.natCard_eq_pow_finrank (K := K) (V := E)
    rw [hKcard, hEcard] at hcard
    exact (pow_right_inj₀ (pow_pos (Fact.out : p.Prime).pos n)
      (Nat.one_lt_pow hn (Fact.out : p.Prime).one_lt).ne').mp hcard.symm
  have hkerle : Nat.card r.ker ≤ 2 := by
    calc
      Nat.card r.ker ≤ Nat.card (E ≃ₐ[K] E) := Nat.card_le_card_of_injective hker hkerinj
      _ ≤ Module.finrank K E := by
        simpa only [Nat.card_eq_fintype_card] using (AlgEquiv.card_le (F := K) (K := E))
      _ = 2 := hdegree
  have hkerodd : Odd (Nat.card r.ker) := hA.of_dvd_nat r.ker.card_subgroup_dvd_card
  have hkerone : Nat.card r.ker = 1 := by
    obtain ⟨k, hk⟩ := hkerodd
    omega
  exact ⟨r, (r.ker_eq_bot_iff).mp (Subgroup.eq_bot_of_card_eq _ hkerone), hr⟩

end GaloisField
