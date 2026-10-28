module

public import Mathlib.GroupTheory.PGroup

/-!
# Centers of nonabelian groups of prime-cube order

A nonabelian group of order `p³` has center of order `p`. The center of a
nontrivial finite p-group is nontrivial; a center of order `p²` would have
cyclic quotient and force commutativity, as would a center of order `p³`.

This extracts the prime-cube argument used in
`Stellmacher.SectionOne.SLThreeFourClassification` for use in Suzuki's local
structure argument (Suzuki, J. Algebra 2 (1965), Sections III–IV).
-/

namespace Subgroup

/-- A noncommutative group of prime-cube order has center of prime order. -/
public theorem card_center_eq_prime_of_card_eq_prime_cube
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card G = p ^ 3) (hncomm : ¬ IsMulCommutative G) :
    Nat.card (center G) = p := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hkpos, hcenter⟩ :=
    IsPGroup.card_center_eq_prime_pow hcard (by decide : 0 < 3)
  have hk_le : k ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
    apply Nat.le_of_dvd (pow_pos hp.pos 3)
    simpa [hcenter, hcard] using card_subgroup_dvd_card (center G)
  have hk : k = 1 := by
    have hcases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · rfl
    · exfalso
      have hindex : (center G).index = p := by
        have hmul := (center G).card_mul_index
        rw [hcenter, hcard] at hmul
        exact Nat.mul_left_cancel (pow_pos hp.pos 2) (by
          simpa only [pow_succ] using hmul)
      have hquotCard : Nat.card (G ⧸ center G) = p := by
        rw [← index_eq_card]
        exact hindex
      let _ : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card hquotCard
      exact hncomm (isMulCommutative_of_isCyclic_quotient_center_self G)
    · exfalso
      have hcenterTop : center G = ⊤ := by
        apply (card_eq_iff_eq_top (center G)).mp
        rw [hcenter, hcard]
      exact hncomm (center_eq_top_iff.mp hcenterTop)
  simpa [hk] using hcenter

end Subgroup
