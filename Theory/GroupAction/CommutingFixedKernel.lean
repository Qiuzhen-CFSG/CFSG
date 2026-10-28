module
public import Theory.GroupAction.PTimesQ

/-!
# A commuting fixed-space kernel is a p-group

Let `P` be a p-subgroup of the automorphism group of a finite elementary
abelian p-group `V`. If another subgroup `A` commutes with `P` and fixes the
P-fixed subgroup pointwise, then `A` is a p-group.

For every prime divisor `q` of the order of `A`, Cauchy's theorem produces
an automorphism of order `q`. If `q ≠ p`, the P × Q lemma applied to its
cyclic subgroup makes this automorphism fix all of `V`, contradicting its
prime order. Hence every prime divisor of the order of `A` is `p`.

This is the standard fixed-space kernel consequence of the P × Q lemma,
used for the center-action reduction in Stellmacher (9.1), relation (3);
see `refs/latex/stellmacher-n-group.tex`.
-/

universe u

public theorem isPGroup_of_commuting_fixes_fixed
    {p : ℕ} [Fact p.Prime]
    {V : Type u} [Group V] [Finite V] [IsElementaryAbelian p V]
    (P A : Subgroup (MulAut V)) (hP : IsPGroup p P)
    (hPA : ⁅P, A⁆ = ⊥)
    (hfix : A ≤ fixingSubgroup (MulAut V) (FixedPoints.subgroup P V : Set V)) :
    IsPGroup p A := by
  classical
  apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
  intro q hq
  obtain ⟨hqprime, hqdiv, _⟩ := Nat.mem_primeFactors.mp hq
  have hqp : q = p := by
    by_contra hne
    let : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) q hqdiv
    let Q : Subgroup (MulAut V) := Subgroup.zpowers (a : MulAut V)
    have hQA : Q ≤ A := Subgroup.zpowers_le.mpr a.property
    have hQcard : Nat.card Q = q := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha]
    have hcop : Nat.Coprime p (Nat.card Q) := by
      rw [hQcard]
      exact (Nat.coprime_primes Fact.out hqprime).mpr (Ne.symm hne)
    have hPQ : ⁅P, Q⁆ = ⊥ :=
      le_antisymm ((Subgroup.commutator_mono le_rfl hQA).trans hPA.le) bot_le
    have hQfix := p_times_q_lemma P Q hP hcop hPQ (hQA.trans hfix)
    have hafix := hQfix (Subgroup.mem_zpowers (a : MulAut V))
    rw [mem_fixingSubgroup_iff] at hafix
    have haone : a = 1 := by
      apply Subtype.ext
      ext v
      exact hafix v (Set.mem_univ v)
    have hqone : q = 1 := by simpa [haone] using ha.symm
    exact hqprime.ne_one hqone
  subst q
  exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩
