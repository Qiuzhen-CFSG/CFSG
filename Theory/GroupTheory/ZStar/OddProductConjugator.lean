module

public import Theory.GroupTheory.ZStar.OddCommutators

/-!
# A controlled conjugator for two involutions

Two involutions whose product has odd order are conjugate by a power of
their product. Every element centralizing both involutions centralizes this
chosen conjugator. No finiteness assumption on the ambient group is needed.

This is Glauberman's Lemma 1, *Central elements in core-free groups*,
J. Algebra 4 (1966), pp.404-405, as implemented in the historical
`public/lean-eval/glauberman_zStar` branch's `OddCommutators` module. It
supplies the controlled replacement used in the later character argument.
Writing the product order as 2a+1, choose its (a+1)-st power. The dihedral
conjugation identity doubles the exponent, giving the required reflection;
the centralizer assertion follows because the conjugator is a product power.
-/

namespace Glauberman.ZStar

open BenderSuzuki.PFAppendixIII

/-- Odd-order products give a conjugator centralized by every common centralizer. -/
public theorem exists_conjugator_of_involutions_mul_odd
    {G : Type*} [Group G] {u t : G}
    (hu : IsInvolution u) (ht : IsInvolution t)
    (hodd : Odd (orderOf (u * t))) :
    ∃ y : G, y * t * y⁻¹ = u ∧
      ∀ r : G, Commute r u → Commute r t → Commute r y := by
  obtain ⟨a, ha⟩ := hodd
  have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
  have hsem : SemiconjBy t (u * t)⁻¹ (u * t) := by
    change t * (u * t)⁻¹ = (u * t) * t
    rw [mul_inv_rev, ht.inv_eq_self, hu.inv_eq_self]
    rw [← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
  refine ⟨(u * t) ^ (a + 1), ?_, ?_⟩
  · have hexp : (a + 1) + (a + 1) = orderOf (u * t) + 1 := by omega
    calc
      (u * t) ^ (a + 1) * t * ((u * t) ^ (a + 1))⁻¹ =
          (u * t) ^ (a + 1) * ((u * t) ^ (a + 1) * t) := by
        rw [← inv_pow, mul_assoc, (hsem.pow_right (a + 1)).eq]
      _ = (u * t) ^ (orderOf (u * t) + 1) * t := by
        rw [← mul_assoc, ← pow_add, hexp]
      _ = u := by rw [pow_succ, pow_orderOf_eq_one, one_mul, mul_assoc, htt, mul_one]
  · intro r hru hrt
    exact (hru.mul_right hrt).pow_right (a + 1)

end Glauberman.ZStar
