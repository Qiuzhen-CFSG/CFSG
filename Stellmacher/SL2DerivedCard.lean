module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products
public import Mathlib.GroupTheory.IndexNormal

/-!
# The derived subgroup of SL₂(2)

For any finite group isomorphic to `SL₂(2)`, its actual derived subgroup
has order three. This supplies the canonical odd factor for the selected
SL₂ coordinate containers used in Stellmacher (4.6) and (6.3).

The established SL₂ facts give order six and trivial center. A Sylow
three-subgroup has order three and index two, hence is normal. Its quotient
has prime order two and is therefore abelian, so the derived subgroup lies
in the Sylow subgroup. The derived subgroup cannot be trivial, since that
would make the whole
group central. Its order is thus the nontrivial divisor of three.

This is a source-neutral consequence of the existing `IsSL2Two` interface,
using `isSL2Two_card` and `center_eq_bot_of_isSL2Two` from the Section One
SL₂ assembly. It identifies the actual derived subgroup without selecting
an arbitrary order-three subgroup or requiring one-seven action data.
-/

namespace Stellmacher

/-- The derived subgroup of a finite `SL₂(2)` group has order three. -/
public theorem isSL2Two_commutator_card
    {G : Type*} [Group G] [Finite G] (hG : IsSL2Two G) :
    Nat.card (commutator G) = 3 := by
  have hcard : Nat.card G = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hG
  let _ : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let T : Sylow 3 G := default
  have hTcard : Nat.card T = 3 := by
    rw [T.card_eq_multiplicity, hcard]
    have hf : Nat.factorization 6 3 = 1 := by
      change Nat.factorization (2 * 3) 3 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    rw [hf]
    norm_num
  have hTindex : (T : Subgroup G).index = 2 := by
    have hm := (T : Subgroup G).card_mul_index
    rw [hTcard, hcard] at hm
    omega
  let _ : (T : Subgroup G).Normal := Subgroup.normal_of_index_eq_two hTindex
  have hquot : Nat.card (G ⧸ (T : Subgroup G)) = 2 := hTindex
  have hle : commutator G ≤ (T : Subgroup G) := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    exact (isCyclic_of_prime_card hquot).isMulCommutative
  have hne : commutator G ≠ ⊥ := by
    rw [ne_eq, commutator_eq_bot_iff_center_eq_top,
      SectionOne.RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two hG]
    exact bot_ne_top
  have hdvd : Nat.card (commutator G) ∣ 3 := by
    rw [← hTcard]
    exact Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hone | hthree
  · exact (hne (Subgroup.card_eq_one.mp hone)).elim
  · exact hthree

end Stellmacher
