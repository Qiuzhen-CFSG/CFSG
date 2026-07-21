/-
Authors: OpenAI
-/

module

public import FeitThompson.BGsection5.theorem_5_6_d
import FeitThompson.BGsection4.theorem_4_18_e
import FeitThompson.PCore.PCore

/-! # Theorem 5.6(e) from BG Section 5 -/

public theorem theorem_5_6_e
    {G : Type*} [Group G] [Finite G] [IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    {S : Sylow p G} (hSnarrow : IsNarrowPGroup p S)
    (hplen : 3 ≤ groupRank (S : Subgroup G) → HasPLengthOne p G) :
    IsMulCommutative (G ⧸ Op_p'p p G) ∧ Nat.Coprime p (Nat.card (G ⧸ Op_p'p p G)) := by
  by_cases hSrank_le : groupRank (S : Subgroup G) ≤ 2
  · have hprank : primeRank p G ≤ 2 :=
      primeRank_le_two_of_sylow_groupRank_le_two (G := G) (p := p) (S := S) hSrank_le
    have hlow :=
      theorem_4_18_e (G := G) (p := p) (inferInstance : IsSolvable G) hodd hp_dvd hprank
    exact ⟨hlow.2, hlow.1⟩
  · have hSrank : 3 ≤ groupRank (S : Subgroup G) := by omega
    exact theorem_5_6_e_high_rank
      (G := G) (p := p) hodd hp_dvd (S := S) hSnarrow hSrank (hplen hSrank)
