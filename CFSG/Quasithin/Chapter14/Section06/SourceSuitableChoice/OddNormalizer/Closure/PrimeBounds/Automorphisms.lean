module
public import CFSG.Quasithin.ChapterA.Section01.RankActions.AutomorphismQuotient

/-!
# Automorphism primes of the small odd cores

The proved A.1.25 representation of Aut(P) has a p-group kernel and image
in GL₂(p). For p=3 or 5 the literal general-linear orders are 48 and 480,
so only two, three and (for p=5) five divide the automorphism order.
The trivial p-group is included.

Source: Aschbacher--Smith 14.6.14, first paragraph, printed p.1032,
using A.1.25(2), printed p.25.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
variable {P : Type*} [Group P] [Finite P]

/-- The prime support of the actual automorphism group of a small-rank odd core. -/
theorem small_rank_odd_automorphism_primes
    {p q : ℕ} (hp : p = 3 ∨ p = 5) (hP : IsPGroup p P)
    (hr : primeRank p P ≤ 2) (hq : q.Prime)
    (hd : q ∣ Nat.card (MulAut P)) : q = 2 ∨ q = 3 ∨ (p = 5 ∧ q = 5) := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> decide
  have ho : Odd p := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hpp⟩
  obtain ⟨f,hf⟩ := ChapterA.RankActions.smallRankAutomorphismRepresentation p ho P hP hr
  have hc : Nat.card f.ker * Nat.card f.range = Nat.card (MulAut P) := by
    rw [← index_ker]
    exact f.ker.card_mul_index
  rw [←hc] at hd
  rcases hq.dvd_mul.mp hd with hk | hi
  · obtain ⟨n,hn⟩ := hf.exists_card_eq
    rw [hn] at hk
    have he : q = p := Nat.prime_eq_prime_of_dvd_pow hq hpp hk
    rcases hp with rfl | rfl
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr ⟨rfl,he⟩)
  · have hlin := hi.trans f.range.card_subgroup_dvd_card
    rcases hp with rfl | rfl
    · have hnum : q ∣ 2 ^ 4 * 3 := by
        rw [Matrix.card_GL_field] at hlin
        norm_num [Fin.prod_univ_two] at hlin ⊢
        exact hlin
      rcases hq.dvd_mul.mp hnum with htwo | hthree
      · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two htwo)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hthree))
    · have hnum : q ∣ (2 ^ 5 * 3) * 5 := by
        rw [Matrix.card_GL_field] at hlin
        norm_num [Fin.prod_univ_two] at hlin ⊢
        exact hlin
      rcases hq.dvd_mul.mp hnum with hh | hfive
      · rcases hq.dvd_mul.mp hh with htwo | hthree
        · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two htwo)
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hthree))
      · exact Or.inr (Or.inr ⟨rfl,(Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hfive⟩)
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
