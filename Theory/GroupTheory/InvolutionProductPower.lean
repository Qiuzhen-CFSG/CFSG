module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Powers of products of involutions

A tenth-power relation identifies the two fifth powers in a dihedral word,
and conjugation transports the relevant reflection centralizer. Separately,
if an involution normalizes a subgroup of exponent dividing four, its product
with an element of that subgroup has eighth power one. A conjugacy identity
between fourth powers transfers this bound to a second product.

These are algebraic reductions for Parrott's VI(i); the source's local word
identities remain explicit premises and must be proved by the application.
Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§6, printed p.684, Verification of VI(i).
-/

namespace Theory.GroupTheory.InvolutionProductPower

variable {G : Type*} [Group G]

private theorem inv_of_square {x : G} (hx : x ^ 2 = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)

/-- A tenth-power relation makes the two fifth powers equal. -/
public theorem fifth_powers_eq_of_tenth_power
    (r s : G) (hr : r ^ 2 = 1) (hs : s ^ 2 = 1)
    (h10 : (r * s) ^ 10 = 1) :
    (s * r) ^ 5 = (r * s) ^ 5 := by
  have hhalf : ((r * s) ^ 5)⁻¹ = (r * s) ^ 5 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_add] using h10
  have hreverse : s * r = (r * s)⁻¹ := by
    rw [mul_inv_rev, inv_of_square hr, inv_of_square hs]
  rw [hreverse, inv_pow, hhalf]

/-- Conjugation by s converts the source's reflection r(sr)^3 into ir,
where i=(rs)^5. -/
public theorem reflection_transport_of_tenth_power
    (r s : G) (hr : r ^ 2 = 1) (hs : s ^ 2 = 1)
    (h10 : (r * s) ^ 10 = 1) :
    s * (r * (s * r) ^ 3) * s = (r * s) ^ 5 * r := by
  calc
    s * (r * (s * r) ^ 3) * s = (s * r) ^ 4 * s := by group
    _ = (s * r) ^ 5 * r := by
      rw [pow_succ (s * r) 4]
      simp only [mul_assoc, ← pow_two, hr, mul_one]
    _ = (r * s) ^ 5 * r := by
      rw [fifth_powers_eq_of_tenth_power r s hr hs h10]

/-- The source commutation puts sDs in the centralizer of ir. -/
public theorem conjugated_word_mem_centralizer_of_tenth_power
    (r s D : G) (hr : r ^ 2 = 1) (hs : s ^ 2 = 1)
    (h10 : (r * s) ^ 10 = 1)
    (hD : Commute D (r * (s * r) ^ 3)) :
    s * D * s ∈ Subgroup.centralizer ({(r * s) ^ 5 * r} : Set G) := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hh := hD.map (MulAut.conj s)
  change Commute (s * D * s⁻¹) (s * (r * (s * r) ^ 3) * s⁻¹) at hh
  simpa only [inv_of_square hs, reflection_transport_of_tenth_power r s hr hs h10]
    using hh.eq

/-- The product yr has eighth power one when r belongs to a normalized
subgroup of exponent dividing four and y is an involution. -/
public theorem product_eighth_power_of_fourth_power_subgroup
    (K : Subgroup G) (r y : G) (hrK : r ∈ K) (hy : y ^ 2 = 1)
    (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hK : ∀ k : G, k ∈ K → k ^ 4 = 1) :
    (y * r) ^ 8 = 1 := by
  have hconj : y * r * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hyK r).mp hrK
  have htwo : (y * r) ^ 2 ∈ K := by
    have hm := K.mul_mem hconj hrK
    simpa only [pow_two, inv_of_square hy, mul_assoc] using hm
  have hh := hK ((y * r) ^ 2) htwo
  simpa only [← pow_mul] using hh

/-- Squaring (*) transfers the eighth-power bound. This is the final
deduction in the order-ten branch; (*) itself is not proved here. -/
public theorem eighth_power_of_fourth_power_identity
    (K : Subgroup G) (r s y A : G) (hrK : r ∈ K) (hy : y ^ 2 = 1)
    (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hK : ∀ k : G, k ∈ K → k ^ 4 = 1)
    (hword : (y * r) ^ 4 = A * (s * r) ^ 4 * A⁻¹) :
    (s * r) ^ 8 = 1 := by
  have h8 := product_eighth_power_of_fourth_power_subgroup K r y hrK hy hyK hK
  have hh := congrArg (fun g : G => g ^ 2) hword
  rw [← pow_mul, conj_pow, ← pow_mul] at hh
  have hc : A * (s * r) ^ 8 * A⁻¹ = 1 := by
    exact hh.symm.trans h8
  calc
    (s * r) ^ 8 = A⁻¹ * (A * (s * r) ^ 8 * A⁻¹) * A := by group
    _ = 1 := by rw [hc]; group

end Theory.GroupTheory.InvolutionProductPower
