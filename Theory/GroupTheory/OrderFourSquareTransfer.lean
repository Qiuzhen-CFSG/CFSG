module
public import Theory.GroupTheory.FusionInvariantTransfer
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.IntervalCases
/-!
# Transfer of an order-four class to its square

Let Q have index two in a Sylow two-subgroup. If an ambient order-four
class avoids Q, then the class of its square meets the complement of Q,
provided the ambient group has no normal subgroup of index two.
The quotient character is constant on every conjugate power if this square
class also avoids the complement. Transfer then gives a nontrivial ambient
binary character, a contradiction.

Source: Aschbacher--Smith A.1.37, applied in 2.4.29, printed p.546.
-/
public section
namespace Sylow

/-- When an order-four class avoids an index-two Sylow subgroup, its square
has an ambient conjugate outside that subgroup. -/
public theorem exists_isConj_square_outside_of_order_four
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (Q : Subgroup S) (hindex : Q.index=2)
    (element : S) (horder : orderOf element=4)
    (houtside : ∀ other : S, IsConj (element:G) (other:G) → other∉Q) :
    ∃ other : S, IsConj (((element^2):S):G) (other:G) ∧ other∉Q := by
  classical
  by_contra! hnot
  let : Q.Normal := Q.normal_of_index_eq_two hindex
  let A := S ⧸ Q
  have hcard : Nat.card A=2 := hindex
  let : IsCyclic A := isCyclic_of_prime_card hcard
  let : CommGroup A := IsCyclic.commGroup
  let character := QuotientGroup.mk' Q
  have hnontrivial (other:S) (hh:IsConj (element:G) (other:G)) : character other≠1 := by
    intro h
    exact houtside other hh ((QuotientGroup.eq_one_iff other).mp h)
  have hnon := hnontrivial element (IsConj.refl _)
  have heq (left right : A) (hleft : left ≠ 1) (hright : right ≠ 1) : left = right := by
    obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
    exact (hunique left hleft).trans (hunique right hright).symm
  have hsquare (value : A) : value ^ 2 = 1 := by
    have hc : value ^ Nat.card A = 1 := pow_card_eq_one'
    simpa only [hcard] using hc
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
      exact heq _ _ (hnontrivial other hconj) hnon
    · rw [show character other=1 from (QuotientGroup.eq_one_iff other).mpr (hnot other hconj),
        map_pow,hsquare]
    · rw [hthree] at hconj ⊢
      have hinverse : IsConj (element : G) ((other⁻¹ : S) : G) := by
        obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp hconj
        apply isConj_iff.mpr
        refine ⟨conjugator, ?_⟩
        have hinv := congrArg Inv.inv hconjugator
        simpa [mul_assoc] using hinv
      have hother : character other ≠ 1 := by
        intro hzero
        exact hnontrivial other⁻¹ hinverse (by simp [hzero])
      exact heq _ _ hother (by simpa using hnon)
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
    change character element ^ ((S : Subgroup G).index % Nat.card A)=
      character element ^ (S : Subgroup G).index at h
    simpa only [hcard, hodd, pow_one] using h.symm
  exact hnon (hpower.symm.trans (htransfer.symm.trans htrivial))

end Sylow
