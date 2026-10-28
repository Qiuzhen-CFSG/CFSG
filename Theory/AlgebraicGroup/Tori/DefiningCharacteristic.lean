module

public import Theory.AlgebraicGroup.Tori.Basic
public import Mathlib.Algebra.CharP.Reduced

/-!
# No defining-characteristic torsion in a torus

In characteristic `p`, the only torus point killed by a power of `p` is the
identity. In diagonal coordinates this is injectivity of iterated Frobenius
on the ground field. No algebraicity over a finite field is needed.

This supplies the torus step in GLS3, Theorem 2.3.4(c),(d): a homomorphism
from a p-group to the torus part of a Borel has trivial image.
-/

namespace Theory.AlgebraicGroup

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]

/-- A torus has no nonidentity point of p-power order in characteristic p. -/
public theorem IsTorus.eq_one_of_pow_prime_pow_eq_one
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T)
    (t : Variety.Point T) (n : ℕ) (ht : t ^ (p ^ n) = 1) : t = 1 := by
  obtain ⟨d, ⟨e⟩⟩ := hT
  apply e.toMulEquiv.symm.injective
  apply (dPointEquiv d).injective
  have ht' : e.toMulEquiv.symm t ^ (p ^ n) = 1 := by
    simpa only [map_pow, map_one] using congrArg e.toMulEquiv.symm ht
  have hc := congrArg (dPointEquiv d) ht'
  rw [dPointEquiv_pow, dPointEquiv_one] at hc
  rw [map_one, dPointEquiv_one]
  funext i
  apply Units.ext
  apply iterateFrobenius_inj k p n
  simpa only [iterateFrobenius_def, Units.val_pow_eq_pow_val, Units.val_one,
    Pi.pow_apply, Pi.one_apply, one_pow] using congrArg Units.val (congrFun hc i)

/-- The same torsion statement in the ambient point group, with the literal
closed-subgroup inclusion. -/
public theorem IsSubtorus.eq_one_of_mem_of_pow_prime_pow_eq_one
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (hT : IsSubtorus T) {x : Variety.Point K} (hx : x ∈ T.toSubgroup)
    (n : ℕ) (hpow : x ^ (p ^ n) = 1) : x = 1 := by
  have hxrange : x ∈ Set.range T.inclusion.onPoints := by
    rw [T.range_inclusion]
    exact hx
  obtain ⟨t, rfl⟩ := hxrange
  have ht : t ^ (p ^ n) = 1 := T.inclusion_injective (by
    simpa only [map_pow, map_one] using hpow)
  rw [hT.eq_one_of_pow_prime_pow_eq_one t n ht, map_one]

end Theory.AlgebraicGroup
