module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.PGroup.OrderNineAutomorphismPrimes

/-!
# The automorphism-prime restriction at three

A supercritical subgroup has Frattini quotient of order at most nine.
Its actual Frattini-action kernel is a three-group, so every prime-order
automorphism of order different from three keeps its order on that
quotient. Orbit counting in the small quotient leaves only order two.
This route does not assume the GL₂ quotient embedding.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.25(3), printed p.25.
-/

open Subgroup

namespace CFSG.Quasithin.ChapterA

/-- A.1.25(3): the automorphism group of every finite three-group of
three-rank at most two is a {2,3}-group, including the trivial group. -/
public theorem lemma_A_1_25_3
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (hr : primeRank 3 P ≤ 2) {q : ℕ} (hq : q.Prime)
    (hd : q ∣ Nat.card (MulAut P)) : q = 2 ∨ q = 3 := by
  cases subsingleton_or_nontrivial P with
  | inl hs =>
    let : Subsingleton P := hs
    let : Subsingleton (MulAut P) := ⟨fun a b => MulEquiv.ext (fun x => Subsingleton.elim _ _)⟩
    have hc : Nat.card (MulAut P) = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨inferInstance, inferInstance⟩
    rw [hc] at hd
    exact (hq.ne_one (Nat.dvd_one.mp hd)).elim
  | inr hn =>
    let : Nontrivial P := hn
    obtain ⟨X, hX⟩ := hP.exists_supercriticalPSubgroup (by decide : 3 ≠ 2)
    have hsmall : Nat.card (X ⧸ frattini X) ≤ 9 :=
      lemma_A_1_25_frattini_card (by decide : Odd 3) hP hr X hX
    by_cases hq3 : q = 3
    · exact Or.inr hq3
    let : Fact q.Prime := ⟨hq⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' q hd
    let : X.Characteristic := hX.characteristic
    let b := quotientAut (frattini X) (MulAut.characteristic X a)
    have hb : orderOf b = q := by
      rw [hX.orderOf_frattini_action_eq_of_coprime hP (by decide : Odd 3) a
        (by rw [ha]; exact (Nat.coprime_primes Nat.prime_three hq).mpr (Ne.symm hq3))]
      exact ha
    apply prime_dvd_mulAut_card_le_nine ((hP.to_subgroup X).to_quotient _) hsmall hq
    exact hb ▸ orderOf_dvd_natCard b

end CFSG.Quasithin.ChapterA
