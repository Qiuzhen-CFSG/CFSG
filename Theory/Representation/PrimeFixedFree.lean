module

public import Theory.GroupTheory.PrimeCyclicCoverage
public import Mathlib.RepresentationTheory.Basic

/-!
# Fixed-point-freeness from a cyclic Sylow subgroup

If p² does not divide the order of a finite group, every element of order p
is conjugate to a generator of one fixed cyclic subgroup of order p. A
representation with zero fixed space on one such element therefore has zero
fixed space on all of them. The proof transfers fixed vectors through powers
and conjugation and works over any commutative ring.

The concrete consumer is the HSG1-f2r20B0 degree-twenty action: its checked
word `ab` suffices for all order-eleven elements after carrier comparison.
-/

public section
namespace Representation

variable {R G V : Type*} [CommRing R] [Group G] [Finite G]
  [AddCommGroup V] [Module R V] (ρ : Representation R G V)

omit [Finite G] in
private theorem fixed_pow {g : G} {v : V} (hv : ρ g v = v) (n : ℕ) :
    ρ (g ^ n) v = v := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, map_mul, Module.End.mul_apply, hv, ih]

/-- One zero fixed space controls all elements of prime order when the
corresponding Sylow subgroups have prime order. -/
theorem prime_fixedFree_of_one {p : ℕ} (hp : p.Prime)
    (hsq : ¬ p ^ 2 ∣ Nat.card G) {x : G} (hx : orderOf x = p)
    (hfree : LinearMap.ker (ρ x - 1) = ⊥)
    (g : G) (hg : orderOf g = p) : LinearMap.ker (ρ g - 1) = ⊥ := by
  obtain ⟨k, c, hc⟩ :=
    PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd hp hsq hx hg
  have hk : ¬ p ∣ k := by
    intro hpk
    have hxk : x ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp (hx ▸ hpk)
    have hg1 : g = 1 := by simpa only [hxk, mul_one, mul_inv_cancel] using hc
    exact hp.ne_one (by simpa only [hg1, orderOf_one] using hg.symm)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (x := x) (hx ▸ (hp.coprime_iff_not_dvd.mpr hk).symm)
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hgv : ρ g v = v := by simpa only [LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero] using hv
  have hkv : ρ (x ^ k) (ρ c⁻¹ v) = ρ c⁻¹ v := by
    have h := congrArg (ρ c⁻¹) hgv
    rw [hc, map_mul, map_mul] at h
    simpa only [Module.End.mul_apply, inv_self_apply] using h
  have hxv : ρ x (ρ c⁻¹ v) = ρ c⁻¹ v := by
    simpa only [hm] using fixed_pow ρ hkv m
  have hz : ρ c⁻¹ v = 0 := LinearMap.ker_eq_bot'.mp hfree _ (by
    simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using hxv)
  have h := congrArg (ρ c) hz
  simpa only [self_inv_apply, map_zero] using h

end Representation
