module
public import Theory.GroupTheory.FusionInvariantTransfer
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.IntervalCases

/-!
# Thompson transfer for involutions

Let `S` be a Sylow two-subgroup of a finite group with no normal subgroup
of index two. Every involution of `S` has an ambient conjugate in the kernel
of each character from `S` to a group of order two, and therefore in every
index-two subgroup of `S`.

If an involution has no such conjugate, every conjugate in `S` of any of its
powers has the same character value as the original power. Reducing the
exponent modulo two proves this assertion. Mathlib's orbit-product formula
then evaluates transfer as the character value raised to the Sylow index.
This index is odd, so transfer is nontrivial. Its kernel would be a normal
subgroup of index two, a contradiction. The subgroup wrapper uses the
quotient character of an index-two subgroup.

This is the no-normal-index-two consequence of Thompson's Transfer Lemma,
Kurzweil--Stellmacher, `The Theory of Finite Groups`, Lemma 12.1.1,
printed pp.338--339 (`refs/original/kurzweil.pdf`). The source uses the sign
of the coset permutation; here the equivalent transfer argument reuses the
same orbit-product API as `Theory.GroupTheory.OrderFourTransfer`.
-/

namespace Sylow

/-- Every involution has an ambient conjugate killed by an order-two character,
provided the ambient group has no normal subgroup of index two. -/
public theorem exists_isConj_ker_of_order_two
    {G A : Type*} [Group G] [CommGroup A] [Finite G] [Finite A]
    (S : Sylow 2 G)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (character : S →* A) (hcard : Nat.card A = 2)
    (element : S) (horder : orderOf element = 2) :
    ∃ other : S, IsConj (element : G) (other : G) ∧ character other = 1 := by
  classical
  by_contra! hnot
  have hnontrivial : character element ≠ 1 := hnot element (IsConj.refl _)
  have heq (left right : A) (hleft : left ≠ 1) (hright : right ≠ 1) : left = right := by
    obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
    exact (hunique left hleft).trans (hunique right hright).symm
  have hrespect (power : ℕ) (other : S)
      (hconj : IsConj (((element ^ power) : S) : G) (other : G)) :
      character other = character (element ^ power) := by
    have hreduce : element ^ power = element ^ (power % 2) := by
      simpa only [horder] using (pow_mod_orderOf element power).symm
    rw [hreduce] at hconj ⊢
    have hbound : power % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize hremainder : power % 2 = remainder at hconj ⊢ hbound
    interval_cases remainder
    · have hother : other = 1 := Subtype.coe_injective
        (isConj_one_right.mp (by simpa using hconj))
      simp [hother]
    · simp only [pow_one] at hconj ⊢
      exact heq _ _ (hnot other hconj) hnontrivial
  have htransfer :=
    character.transfer_apply_eq_pow_of_conjugate_powers element hrespect
  have hindex : character.transfer.ker.index = 1 := by
    have hdiv : character.transfer.ker.index ∣ 2 := by
      rw [Subgroup.index_ker]
      have hdiv := Subgroup.card_subgroup_dvd_card character.transfer.range
      rwa [hcard] at hdiv
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdiv with hone | htwo
    · exact hone
    · exact (hno _ inferInstance htwo).elim
  have htrivial : character.transfer (element : G) = 1 := by
    change (element : G) ∈ character.transfer.ker
    rw [Subgroup.index_eq_one.mp hindex]
    trivial
  have hodd : (S : Subgroup G).index % 2 = 1 := by
    have h := S.not_dvd_index
    omega
  have hpower : character element ^ (S : Subgroup G).index = character element := by
    have h := pow_mod_natCard (character element) (S : Subgroup G).index
    simpa only [hcard, hodd, pow_one] using h.symm
  exact hnontrivial (hpower.symm.trans (htransfer.symm.trans htrivial))

/-- Every involution has an ambient conjugate in each index-two subgroup of the
chosen Sylow subgroup, if the ambient group has no normal subgroup of index two. -/
public theorem exists_isConj_mem_of_index_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (U : Subgroup S) (hU : U.index = 2)
    (element : S) (horder : orderOf element = 2) :
    ∃ other : S, IsConj (element : G) (other : G) ∧ other ∈ U := by
  let : U.Normal := U.normal_of_index_eq_two hU
  have hcard : Nat.card (S ⧸ U) = 2 := hU
  let : IsCyclic (S ⧸ U) := isCyclic_of_prime_card hcard
  let : CommGroup (S ⧸ U) := IsCyclic.commGroup
  obtain ⟨other, hconj, hker⟩ :=
    S.exists_isConj_ker_of_order_two hno (QuotientGroup.mk' U) hcard element horder
  exact ⟨other, hconj, (QuotientGroup.eq_one_iff (N := U) (x := other)).mp hker⟩

end Sylow
