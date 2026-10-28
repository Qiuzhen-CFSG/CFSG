module

public import Theory.GroupTheory.CentralExtensionPartialInversion

/-!
# A swapping normalizer in a central extension

If an inner automorphism exchanges two commuting elements, the commutator
of any two lifts in a central extension equals its inverse. If the first
base element has odd order, its order also annihilates this commutator.
Thus the lifts commute. This supplies the abelian-preimage input to central
Sylow transfer for the split tori in the actual octonion G₂ model.

This elementary normalizer argument is used in the covering calculation
underlying Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and GLS III §6.1.
The concrete application is `G2.MultiplierOrdinary.OddSplitTorus`.
-/

public section

open scoped commutatorElement
open Subgroup

namespace CentralExtension

/-- Swapping a commuting pair of odd order makes arbitrary lifts commute
in every central extension. No finiteness or perfectness is needed here. -/
theorem commute_lifts_of_swap
    {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (x y r : G) {n : ℕ}
    (hn : n.Coprime 2) (hx : x ^ n = 1) (hxy : Commute x y)
    (hrx : r * x * r⁻¹ = y) (hry : r * y * r⁻¹ = x)
    (a b : E) (ha : f a = x) (hb : f b = y) : Commute a b := by
  have hc : ⁅a, b⁆ ∈ center E := hk (by
    rw [MonoidHom.mem_ker, map_commutatorElement, ha, hb]
    exact hxy.commutator_eq)
  have hconj (t : E) : t * ⁅a, b⁆ * t⁻¹ = ⁅a, b⁆ := by
    rw [mem_center_iff.mp hc t, mul_inv_cancel_right]
  obtain ⟨s, hs⟩ := hf r
  have he : ⁅a, b⁆ = ⁅b, a⁆ := by
    rw [← hconj s, conjugate_commutatorElement]
    apply commutator_eq_of_image_eq f hk
    · simp only [map_mul, map_inv, hs, ha, hrx, hb]
    · simp only [map_mul, map_inv, hs, hb, hry, ha]
  have hi : ⁅a, b⁆ = ⁅a, b⁆⁻¹ := he.trans (commutatorElement_inv a b).symm
  have htwo : ⁅a, b⁆ ^ 2 = 1 := by
    rw [pow_two, hi, inv_mul_eq_one]
    exact hi
  have hpow (k : ℕ) : ⁅a ^ k, b⁆ = ⁅a, b⁆ ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, commutatorElement_mul_left_eq_conj_mul, hconj, ih, pow_succ']
  have hncomm : ⁅a, b⁆ ^ n = 1 := by
    rw [← hpow]
    apply Commute.commutator_eq
    exact (mem_center_iff.mp (hk (by
      rw [MonoidHom.mem_ker, map_pow, ha, hx])) b).symm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hn
    (orderOf_dvd_of_pow_eq_one hncomm) (orderOf_dvd_of_pow_eq_one htwo))

end CentralExtension

end
