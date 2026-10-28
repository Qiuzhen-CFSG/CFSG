module

public import Theory.GroupTheory.FusionInvariantTransfer
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.IntervalCases

/-!
# Involution fusion into kernels of cyclic Sylow quotients

In a finite nonabelian simple group, every involution of a Sylow two-subgroup
has a conjugate in the kernel of every homomorphism to a finite cyclic group.
If there were no such conjugate, uniqueness of the involution in the cyclic
image would make the character constant on all conjugates of all powers of
that involution. The transfer orbit formula then gives a nonidentity value,
since the Sylow index is odd. Simplicity and noncommutativity force every
homomorphism to the abelian target to be trivial, a contradiction.

This proves the transfer consequence needed in both endings of
Aschbacher–Smith 16.4.6, combined manuscript of 1 March 2004, printed p.1186.
In particular, the cyclic-four quotient is retained; it need not be replaced
by an index-two quotient that kills the distinguished involution.
-/

namespace Sylow

/-- Generalized involution transfer for a cyclic character of a Sylow subgroup. -/
public theorem exists_isConj_ker_of_cyclic_of_simple
    {G A : Type*} [Group G] [CommGroup A] [Finite G] [Finite A]
    [IsSimpleGroup G] [IsCyclic A] (hnonab : ¬ IsMulCommutative G)
    (S : Sylow 2 G) (character : S →* A)
    (element : S) (horder : orderOf element = 2) :
    ∃ other : S, IsConj (element : G) (other : G) ∧ character other = 1 := by
  classical
  by_contra! hnot
  have hnontrivial : character element ≠ 1 := hnot element (IsConj.refl _)
  have hcharOrder : orderOf (character element) = 2 :=
    orderOf_eq_prime (by
      simpa only [horder, map_pow, map_one] using
        (congrArg character (pow_orderOf_eq_one element))) hnontrivial
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
      have hotherOrder : orderOf other = 2 := by
        obtain ⟨a, ha⟩ := isConj_iff.mp hconj
        have he : MulAut.conj a (element : G) = other := ha
        rw [← Subgroup.orderOf_coe, ← he, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, horder]
      exact IsCyclic.eq_of_orderOf_eq_two
        (orderOf_eq_prime (by
          simpa only [hotherOrder, map_pow, map_one] using
            (congrArg character (pow_orderOf_eq_one other)))
          (hnot other hconj)) hcharOrder
  have htransfer := character.transfer_apply_eq_pow_of_conjugate_powers element hrespect
  have hker : character.transfer.ker = ⊤ := by
    rcases (inferInstance : character.transfer.ker.Normal).eq_bot_or_eq_top with hbot | htop
    · let : CommGroup G := character.transfer.commGroupOfInjective
        ((MonoidHom.ker_eq_bot_iff _).mp hbot)
      exact (hnonab inferInstance).elim
    · exact htop
  have hzero : character.transfer (element : G) = 1 := by
    change (element : G) ∈ character.transfer.ker
    rw [hker]
    trivial
  have hodd : (S : Subgroup G).index % 2 = 1 := by
    have h := S.not_dvd_index
    omega
  have hpower : character element ^ (S : Subgroup G).index = character element := by
    simpa only [hcharOrder, hodd, pow_one] using
      (pow_mod_orderOf (character element) (S : Subgroup G).index).symm
  exact hnontrivial (hpower.symm.trans (htransfer.symm.trans hzero))

/-- Every involution has a conjugate in each normal subgroup of its Sylow group
whose quotient is cyclic, in a nonabelian simple ambient group. -/
public theorem exists_isConj_mem_of_cyclic_quotient_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ¬ IsMulCommutative G)
    (S : Sylow 2 G) (D : Subgroup S) [D.Normal] [IsCyclic (S ⧸ D)]
    (element : S) (horder : orderOf element = 2) :
    ∃ other : S, IsConj (element : G) (other : G) ∧ other ∈ D := by
  let : CommGroup (S ⧸ D) := IsCyclic.commGroup
  obtain ⟨other, hconj, hker⟩ :=
    S.exists_isConj_ker_of_cyclic_of_simple hnonab (QuotientGroup.mk' D) element horder
  exact ⟨other, hconj, (QuotientGroup.eq_one_iff (N := D) (x := other)).mp hker⟩

end Sylow
