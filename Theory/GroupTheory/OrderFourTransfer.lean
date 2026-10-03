module
public import Theory.GroupTheory.FusionInvariantTransfer
public import Mathlib.Tactic.IntervalCases

/-!
# Order-four fusion detected by transfer

Let `S` be a Sylow two-subgroup of a finite group with no normal subgroup
of index two. If a homomorphism from `S` to a group of order two kills
every element whose square is one, every element of order four in `S`
has an ambient conjugate in the homomorphism's kernel.

Assume an order-four element has no such conjugate. Its powers with even
exponent, and all their conjugates in `S`, are killed. For odd exponents,
the powers are the element or its inverse, and all their conjugates have
the unique nonidentity image in the group of order two. The orbit-product
formula for transfer therefore evaluates transfer on this element as its
image raised to the odd Sylow index, which is nonidentity. But the kernel
of any homomorphism from the ambient group to a group of order two has
index one or two, and the latter is excluded. This is a contradiction.

This direct transfer argument isolates the ambient ingredient of
Alperin--Brauer--Gorenstein, Chapter II, Section 1, Proposition 1(i),
printed pp.10--11 of `refs/files/alperin-brauer-gorenstein.pdf`, where
absence of normal index two forces order-four fusion for a semidihedral
Sylow subgroup. The statement here needs no semidihedral presentation,
automizer index, or classification hypothesis. Its application only needs
the elementary character with dihedral kernel inside that presentation.
-/

namespace Sylow

/-- An order-four element has an ambient conjugate killed by any order-two
character that kills every Sylow element whose square is one. -/
public theorem exists_isConj_ker_of_order_four
    {G A : Type*} [Group G] [CommGroup A] [Finite G] [Finite A]
    (S : Sylow 2 G)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (character : S →* A) (hcard : Nat.card A = 2)
    (hinvol : ∀ other : S, other ^ 2 = 1 → character other = 1)
    (element : S) (horder : orderOf element = 4) :
    ∃ other : S, IsConj (element : G) (other : G) ∧ character other = 1 := by
  classical
  by_contra! hnot
  have hnontrivial : character element ≠ 1 := hnot element (IsConj.refl _)
  have heq (left right : A) (hleft : left ≠ 1) (hright : right ≠ 1) : left = right := by
    obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
    exact (hunique left hleft).trans (hunique right hright).symm
  have hsquare (value : A) : value ^ 2 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hfour : element ^ 4 = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one _
  have hthree : element ^ 3 = element⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using hfour
  have hrespect (power : ℕ) (other : S)
      (hconj : IsConj (((element ^ power) : S) : G) (other : G)) :
      character other = character (element ^ power) := by
    have hreduce : element ^ power = element ^ (power % 4) := by
      simpa only [horder] using (pow_mod_orderOf element power).symm
    rw [hreduce] at hconj ⊢
    have hbound : power % 4 < 4 := Nat.mod_lt _ (by decide)
    generalize hremainder : power % 4 = remainder at hconj ⊢ hbound
    interval_cases remainder
    · have hother : other = 1 := Subtype.coe_injective
        (isConj_one_right.mp (by simpa using hconj))
      simp [hother]
    · simp only [pow_one] at hconj ⊢
      exact heq _ _ (hnot other hconj) hnontrivial
    · have hothersquare : other ^ 2 = 1 := by
        apply Subtype.coe_injective
        have h := hconj.pow 2
        have hsource : (((element ^ 2) ^ 2 : S) : G) = 1 := by
          simp only [← pow_mul, show 2 * 2 = 4 by decide, hfour, Subgroup.coe_one]
        exact isConj_one_right.mp (by simpa only [← Subgroup.coe_pow, hsource] using h)
      rw [hinvol other hothersquare, map_pow, hsquare]
    · rw [hthree] at hconj ⊢
      have hinverse : IsConj (element : G) ((other⁻¹ : S) : G) := by
        obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp hconj
        apply isConj_iff.mpr
        refine ⟨conjugator, ?_⟩
        have hinv := congrArg Inv.inv hconjugator
        simpa [mul_assoc] using hinv
      have hother : character other ≠ 1 := by
        intro hzero
        apply hnot other⁻¹ hinverse
        simp [hzero]
      exact heq _ _ hother (by simpa using hnontrivial)
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

end Sylow
