/-
Authors: OpenAI
-/

module

public import Submission.FeitThompson.BGsection5.theorem_5_6_a
import Submission.FeitThompson.PCore.PCore
import Submission.FeitThompson.PGroup.NormalSubgroups

/-! # Theorem 5.6(b) from BG Section 5 -/

public theorem theorem_5_6_b
    {G : Type*} [Group G] [Finite G] [IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    {S : Sylow p G} (hSnarrow : IsNarrowPGroup p S)
    (hplen : 3 ≤ groupRank (S : Subgroup G) → HasPLengthOne p G)
    (hp : (p = 3) ∨ ∀ q : ℕ, q.Prime → q ∣ Nat.card G → p ≤ q) :
    HasNormalPComplement p G := by
  classical
  let M : Subgroup G := pPrimeCore p G
  have hM_normal : M.Normal := by
    dsimp [M]
    infer_instance
  have hM_coprime : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hquot_odd : Odd (Nat.card (G ⧸ M)) := by
    exact odd_of_card_dvd hodd (Subgroup.card_quotient_dvd_card (s := M))
  have hquot_p : IsPGroup p (G ⧸ M) := by
    refine (IsPGroup.iff_card (p := p) (G := G ⧸ M)).2 ?_
    have hQ_pos : 0 < Nat.card (G ⧸ M) := Nat.card_pos (α := G ⧸ M)
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hQ_pos.ne' ?_⟩
    intro q hqprime hq_dvd
    haveI : Fact q.Prime := ⟨hqprime⟩
    have hq_le_p : q ≤ p :=
      theorem_5_6_a
        (G := G) (p := p) hodd hp_dvd (S := S) hSnarrow hplen (q := q) hq_dvd
    rcases hp with hp3 | hp_small
    · have hq_ne_two : q ≠ 2 := Odd.ne_two_of_dvd_nat hquot_odd hq_dvd
      have hq_eq_three : q = 3 := by
        have hq_ge_two : 2 ≤ q := hqprime.two_le
        omega
      simpa [hp3] using hq_eq_three
    · have hq_dvd_G : q ∣ Nat.card G := by
        exact dvd_trans hq_dvd (Subgroup.card_quotient_dvd_card (s := M))
      exact le_antisymm hq_le_p (hp_small q hqprime hq_dvd_G)
  exact ⟨M, hM_normal, hM_coprime, hquot_p⟩
