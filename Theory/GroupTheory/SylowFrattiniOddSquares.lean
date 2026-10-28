module
public import Theory.GroupTheory.SylowOuterRadicalFreeSections
public import Theory.GroupTheory.PerfectPairOrder

/-!
# Odd prime squares in automorphisms of a small two-group

With at most five Frattini generators, the odd part of the automorphism
order divides 3²·5·7·31. The Burnside basis kernel is a two-group, so no
odd prime other than three has its square dividing that order.
Source application: Aschbacher--Smith 4.4.10, printed p.621.
-/

public section
open Subgroup
namespace IsPGroup
variable {Q : Type*} [Group Q] [Finite Q]

theorem not_odd_prime_square_dvd_card_mulAut_of_frattini_card_le_thirtytwo
    (hQ : IsPGroup 2 Q) (hbound : Nat.card (Q ⧸ frattini Q) ≤ 32)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) :
    ¬ p ^ 2 ∣ Nat.card (MulAut Q) := by
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  obtain ⟨n,hn⟩ := (hQ.to_quotient (frattini Q)).exists_card_eq
  have hn5 : n ≤ 5 := by
    have hh : 2 ^ n ≤ 2 ^ 5 := by rw [←hn]; exact hbound
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  have hAut : Nat.card (MulAut (Q ⧸ frattini Q)) ∣ 2^10 * 3^2 * (5*7*31) := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  let f := quotientAut (frattini Q)
  have hcount : Nat.card f.ker * Nat.card f.range = Nat.card (MulAut Q) := by
    rw [←index_ker]
    exact f.ker.card_mul_index
  obtain ⟨k,hk⟩ := (isPGroup_quotientAut_frattini_kernel hQ).exists_card_eq
  have h2 : Nat.Coprime p 2 := ho.coprime_two_right
  have h3 : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr
    (fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
  have hcop : Nat.Coprime (p^2) (Nat.card f.ker) := by
    rw [hk]
    exact (h2.pow_left 2).pow_right k
  intro hd
  rw [←hcount] at hd
  have he := (hcop.dvd_of_dvd_mul_left hd).trans
    (f.range.card_subgroup_dvd_card.trans hAut)
  have hc : Nat.Coprime (p^2) (2^10 * 3^2) :=
    ((h2.pow_right 10).mul_right (h3.pow_right 2)).pow_left 2
  have hs : Squarefree (5*7*31 : ℕ) := by
    apply (Nat.squarefree_mul (by decide : Nat.Coprime (5*7) 31)).mpr
    refine ⟨?_, (Nat.prime_iff.mp (by decide : Nat.Prime 31)).squarefree⟩
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 5 7)).mpr
      ⟨(Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree,
        (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree⟩
  exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp)
    (by simpa only [pow_two] using hc.dvd_of_dvd_mul_left he)

end IsPGroup
