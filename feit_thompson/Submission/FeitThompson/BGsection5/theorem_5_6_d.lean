/-
Authors: OpenAI
-/

module

public import FeitThompson.BGsection5.theorem_5_6_c
import FeitThompson.BGsection4.theorem_4_18_d
import FeitThompson.PCore.PCore
import FeitThompson.PGroup.NormalSubgroups

/-! # Theorem 5.6(d) from BG Section 5 -/

public theorem theorem_5_6_d
    {G : Type*} [Group G] [Finite G] [IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G)
    {S : Sylow p G} (hSnarrow : IsNarrowPGroup p S)
    (hplen : 3 ≤ groupRank (S : Subgroup G) → HasPLengthOne p G)
    {K : Subgroup (derivedSubgroup G)} (hcop : Nat.Coprime p (Nat.card K)) :
    K ≤ pPrimeCore p (derivedSubgroup G) := by
  by_cases hSrank_le : groupRank (S : Subgroup G) ≤ 2
  · have hprank : primeRank p G ≤ 2 :=
      primeRank_le_two_of_sylow_groupRank_le_two (G := G) (p := p) (S := S) hSrank_le
    exact theorem_4_18_d (G := G) (p := p) (inferInstance : IsSolvable G) hodd hp_dvd hprank K hcop
  · have hcomp :
        HasNormalPComplement p (derivedSubgroup G) :=
      theorem_5_6_c (G := G) (p := p) hodd hp_dvd (S := S) hSnarrow hplen
    let q : (derivedSubgroup G) →* ((derivedSubgroup G) ⧸ pPrimeCore p (derivedSubgroup G)) :=
      QuotientGroup.mk' (pPrimeCore p (derivedSubgroup G))
    have hKquot_p :
        IsPGroup p ((derivedSubgroup G) ⧸ pPrimeCore p (derivedSubgroup G)) :=
      isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
        (p := p) (H := ↥(derivedSubgroup G)) hcomp
    have hKmap_p : IsPGroup p (K.map q) := hKquot_p.to_subgroup (K.map q)
    have hKmap_cop : Nat.Coprime p (Nat.card (K.map q)) := by
      exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := K) q) hcop
    have hKmap_card_eq_one : Nat.card (K.map q) = 1 := by
      rcases hKmap_p.card_eq_or_dvd with h1 | hpdvd
      · exact h1
      · exfalso
        exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hKmap_cop) hpdvd
    have hKmap_bot : K.map q = ⊥ := Subgroup.card_eq_one.mp hKmap_card_eq_one
    have hK_le_ker : K ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (H := K) (f := q)).1 hKmap_bot
    have hqker : q.ker = pPrimeCore p (derivedSubgroup G) := by
      change MonoidHom.ker (QuotientGroup.mk' (pPrimeCore p (derivedSubgroup G))) =
        pPrimeCore p (derivedSubgroup G)
      simpa using
        (QuotientGroup.ker_mk' (G := derivedSubgroup G)
          (N := pPrimeCore p (derivedSubgroup G)))
    rw [hqker] at hK_le_ker
    exact hK_le_ker
