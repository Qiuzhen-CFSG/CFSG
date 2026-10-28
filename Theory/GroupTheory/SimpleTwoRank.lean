module
public import Theory.GroupTheory.BrauerSuzuki
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.QuasithinBasic
public import FeitThompson.FinalTheorem
/-!
# Two-rank of a nonabelian simple group

If a Sylow two-subgroup contains no elementary four-group, it is cyclic or
generalized quaternion. The cyclic case gives a normal odd complement;
Brauer–Suzuki makes the center modulo the odd core even in the quaternion
case. Both contradict nonabelian simplicity. The resulting ordinary
rank bound is the component input in Aschbacher–Smith A.2.12, pp.35–36.

The proof uses the existing constructive Brauer–Suzuki theorem and the
proved cyclic-or-quaternion classification, with no classification premise.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

theorem two_le_twoRank_of_nonabelian_simple (hna : ¬ IsMulCommutative G) :
    2 ≤ primeRank 2 G := by
  have hc : commutator G = ⊤ :=
    (inferInstance : (commutator G).Normal).eq_bot_or_eq_top.resolve_left
      (fun hb => hna ((commutator_eq_bot_iff G).mp hb))
  let : Group.IsPerfect G := ⟨hc⟩
  have heven : 2 ∣ Nat.card G := by
    by_contra ho
    exact Group.IsPerfect.not_isSolvable G
      (odd_order_theorem G (Nat.not_even_iff_odd.mp (by
        simpa only [even_iff_two_dvd] using ho)))
  have hcenter : center G = ⊥ :=
    (inferInstance : (center G).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => hna (center_eq_top_iff.mp ht))
  have hcore : pPrimeCore 2 G = ⊥ := by
    rcases (inferInstance : (pPrimeCore 2 G).Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · have ho := pPrimeCore_coprime_card (p := 2) (G := G)
      rw [hh, Nat.card_congr (topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv] at ho
      exact ((Nat.prime_two.coprime_iff_not_dvd.mp ho) heven).elim
  by_contra hr
  let Q : Sylow 2 G := Classical.choice inferInstance
  have hQg : primeRank 2 Q ≤ primeRank 2 G :=
    primeRank_le_of_injective 2 (Q : Subgroup G).subtype (Q : Subgroup G).subtype_injective
  have hQr : primeRank 2 Q ≤ 1 := by omega
  have hfour : ∀ E : Subgroup Q, IsElementaryAbelian 2 E → Nat.card E ≠ 4 := by
    intro E hE hcard
    have hb := (primeRank_le_iff_elementary_card_le Q).mp hQr E hE
    rw [hcard] at hb
    norm_num at hb
  rcases Q.isPGroup'.isCyclic_or_quaternion_of_no_elementary_four hfour with hcyc | ⟨n, hn, hquat⟩
  · obtain ⟨N, hN, hcop, hpN⟩ :=
      BenderSuzuki.External.Suzuki.V.suzuki_ch5_theorem_2_10_corollary_1
        Q ((Nat.minFac_eq_two_iff _).mpr heven) hcyc
    rcases hN.eq_bot_or_eq_top with hb | ht
    · subst N
      have hpG : IsPGroup 2 G := hpN.of_equiv (QuotientGroup.quotientBot)
      exact Group.IsPerfect.not_isNilpotent G hpG.isNilpotent
    · subst N
      rw [Nat.card_congr (topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv] at hcop
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) heven
  · have hb := even_card_center_quotient_pPrimeCore_of_quaternion_sylow Q hn hquat
    let e : G ⧸ pPrimeCore 2 G ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
    rw [Nat.card_congr (centerCongr e).toEquiv, hcenter] at hb
    norm_num at hb

end Theory.GroupTheory
