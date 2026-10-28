module

public import Theory.Quasithin.NormalTwoRank
public import Theory.GroupTheory.Amalgam.RankTwo
public import CFSG.Quasithin.ChapterA.Section02.EvenLie

/-!
# The unitary field-size deduction in F.1.12

The rank obstruction in a `U₅(q)` parabolic is indexed by prime divisors of
`(q + 1) / gcd(q + 1, 5)`. Every such divisor is odd when `q` is even. A
nontrivial normal 2-subgroup of the actual parabolic therefore lets
quasithinness rule out these divisors, forcing `q = 4`.

The group-theoretic rank calculation remains an explicit input. This module
proves its consequence, not the missing calculation or the DGS recognition
theorem. Parabolic equivalence is enough to transport this obstruction.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Proposition F.1.12, final paragraph of the proof, printed p. 264; compare the
arithmetic restriction in Lemma A.2.18.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook

/-- The odd-prime version of the unitary parabolic arithmetic restriction. -/
theorem unitary_field_size_eq_four_of_odd_parabolic_rank
    {P : Type*} [Group P] {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q)
    (hparabolic : ∀ p : ℕ, p.Prime →
      p ∣ (q + 1) / Nat.gcd (q + 1) 5 → 3 ≤ primeRank p P)
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p P ≤ 2) : q = 4 := by
  have hquot : (q + 1) / Nat.gcd (q + 1) 5 = 1 :=
    Nat.eq_one_iff_not_exists_prime_dvd.mpr (by
      intro p hp hpdvd
      have hdiv : p ∣ q + 1 := hpdvd.trans
        (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (q + 1) 5))
      have hodd : Odd p := by
        rcases hp.eq_two_or_odd with htwo | hodd
        · subst p
          obtain ⟨k, hk⟩ := hq
          obtain ⟨m, hm⟩ := hdiv
          omega
        · exact Nat.odd_iff.mpr hodd
      exact (Nat.not_succ_le_self 2)
        ((hparabolic p hp hpdvd).trans (hrank p hp hodd)))
  apply ChapterA.Section02.EvenLie.unitary_five_field_size_eq_four hq hq2
  calc
    q + 1 = (q + 1) / Nat.gcd (q + 1) 5 * Nat.gcd (q + 1) 5 :=
      (Nat.div_mul_cancel (Nat.gcd_dvd_left (q + 1) 5)).symm
    _ = Nat.gcd (q + 1) 5 := by rw [hquot, one_mul]

/-- Quasithinness eliminates all unitary-five parameters except four once
the actual parabolic rank calculation has been established. -/
theorem unitary_field_size_eq_four_in_quasithin_completion
    {G : Type*} [Group G] [Finite G] (hG : IsQuasithin G)
    (P : Subgroup G) (Q : Subgroup P) [Q.Normal]
    (hQ : Q ≠ ⊥) (hQp : IsPGroup 2 Q) {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q)
    (hparabolic : ∀ p : ℕ, p.Prime →
      p ∣ (q + 1) / Nat.gcd (q + 1) 5 → 3 ≤ primeRank p P) : q = 4 :=
  unitary_field_size_eq_four_of_odd_parabolic_rank hq hq2 hparabolic
    (Theory.Quasithin.primeRank_subgroup_le_two_of_normal_two_subgroup
      hG P Q hQ hQp)

/-- The exclusion uses only parabolic equivalence, so also applies when
recognition supplies no compatible amalgam isomorphism. -/
theorem unitary_field_size_eq_four_of_parabolic_equiv
    {G H B R B' R' : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Group B] [Group R] [Group B'] [Group R']
    (hG : IsQuasithin G) (P : Subgroup G)
    {α : Theory.GroupTheory.RankTwoAmalgam P B R}
    {β : Theory.GroupTheory.RankTwoAmalgam H B' R'}
    (e : Theory.GroupTheory.RankTwoAmalgam.ParabolicEquiv α β)
    (Q : Subgroup P) [Q.Normal] (hQ : Q ≠ ⊥) (hQp : IsPGroup 2 Q)
    {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q)
    (hparabolic : ∀ p : ℕ, p.Prime →
      p ∣ (q + 1) / Nat.gcd (q + 1) 5 → 3 ≤ primeRank p H) : q = 4 := by
  apply unitary_field_size_eq_four_in_quasithin_completion hG P Q hQ hQp hq hq2
  intro p hp hpdvd
  rw [primeRank_congr p e.left]
  exact hparabolic p hp hpdvd

end CFSG.Quasithin.ChapterF.GreenBook
