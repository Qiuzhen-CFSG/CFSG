module
public import Theory.GroupAction.ComponentRankAction.PrimeClosure

/-!
# Prime actors with bounded outer exponent

A normal subgroup of full p-rank and p-prime center has p-prime
centralizer. If a power coprime to p makes every automorphism inner,
an element of order p has inner action and is absorbed by that subgroup.
This is the ordinary-component rank argument before any model-specific
outer exponent calculation.

Source: Aschbacher–Smith A.3.18, printed pp.51–53; original 4.3.12(2), p.617.
-/

public section
open Subgroup
noncomputable section
namespace Theory.GroupAction.ComponentRankAction
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
/-- Full rank absorbs a prime actor when the outer exponent is prime to p. -/
theorem prime_actor_mem_of_full_rank_of_inner_power (B : Subgroup G) [B.Normal]
    (hz : Nat.Coprime p (Nat.card (center B)))
    (hr : 2 ≤ primeRank p B) (hG : primeRank p G ≤ 2)
    {m : ℕ} (hcop : Nat.Coprime p m)
    (hpower : ∀ a : MulAut B, a ^ m ∈ MulAut.innerSubgroup B)
    (x : G) (hx : orderOf x = p) : x ∈ B := by
  let f : G →* MulAut B := MulAut.conjNormal
  have hk : Nat.Coprime p (Nat.card f.ker) := by
    rw [show f.ker = centralizer (B : Set G) from MulAut.conjNormal_ker_eq_centralizer B]
    exact centralizer_coprime B hz hr hG
  apply prime_element_mem_of_image_mem f hk B x hx
  let q := QuotientGroup.mk' (MulAut.innerSubgroup B)
  have hi : f x ∈ MulAut.innerSubgroup B := by
    apply (QuotientGroup.eq_one_iff _).mp
    have hp : q (f x) ^ p = 1 := by
      rw [← map_pow, ← map_pow, ← hx, pow_orderOf_eq_one, map_one, map_one]
    have hm : q (f x) ^ m = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hpower (f x))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hp) (orderOf_dvd_of_pow_eq_one hm))
  obtain ⟨b, hb⟩ := hi
  exact mem_map.mpr ⟨b, b.property, MulAut.conjNormal_val.trans hb⟩
end Theory.GroupAction.ComponentRankAction
