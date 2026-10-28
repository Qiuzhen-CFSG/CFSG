module

public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupTheory.ElementaryEightThreeNormalizer
public import Theory.GroupTheory.ElementaryEightSevenNormalizer

/-!
# Centralizers of involutions in the automizer of an elementary eight

The automorphism group of an elementary abelian group of order eight has order
`168`. Its involution centralizers are two-groups. We prove this without
choosing a matrix model: an odd prime divisor would give a three- or
seven-subgroup whose centralizer is odd, while the involution itself supplies
an even element in that centralizer.

This is the automorphism quotient calculation used by the saturated
extraspecial-32 branch of Aschbacher's Lemma 2.8.
-/

open Subgroup

private theorem no_odd_prime_centralizer
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (a : MulAut E) (ha : orderOf a = 2)
    (p : ℕ) [Fact p.Prime] (hp : p = 3 ∨ p = 7) :
    ¬ p ∣ Nat.card (centralizer ({a} : Set (MulAut E))) := by
  intro hd
  let C := centralizer ({a} : Set (MulAut E))
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := C) p hd
  let B := zpowers (b : MulAut E)
  have hB : Nat.card B = p :=
    (Nat.card_zpowers _).trans ((Subgroup.orderOf_coe b).trans hb)
  have hBC : B ≤ C := zpowers_le.mpr b.property
  have haB : a ∈ centralizer (B : Set (MulAut E)) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hBC hx)
  have htwo : 2 ∣ Nat.card (centralizer (B : Set (MulAut E))) := by
    let t : centralizer (B : Set (MulAut E)) := ⟨a, haB⟩
    have ht : orderOf t = 2 := (Subgroup.orderOf_coe t).symm.trans ha
    simpa only [ht] using orderOf_dvd_natCard t
  rcases hp with rfl | rfl
  · exact (odd_card_centralizer_of_elementary_eight_three hE B hB).not_two_dvd_nat htwo
  · exact (odd_card_normalizer_of_elementary_eight_seven E hE B hB).not_two_dvd_nat
      (htwo.trans (card_dvd_of_le (centralizer_le_normalizer (B : Set (MulAut E)))))

/-- The centralizer of a nontrivial involution in `MulAut E` is a two-group. -/
public theorem isPGroup_centralizer_of_involution_on_elementary_eight
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (a : MulAut E) (ha : orderOf a = 2) :
    IsPGroup 2 (centralizer ({a} : Set (MulAut E))) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let C := centralizer ({a} : Set (MulAut E))
  have hd : Nat.card C ∣ 168 :=
    card_mulAut_of_elementary_eight E hE ▸ C.card_subgroup_dvd_card
  have hthree : ¬ 3 ∣ Nat.card C :=
    no_odd_prime_centralizer hE a ha 3 (Or.inl rfl)
  have hseven : ¬ 7 ∣ Nat.card C :=
    no_odd_prime_centralizer hE a ha 7 (Or.inr rfl)
  have hmem := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hdivs : (168 : ℕ).divisors =
      {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  apply IsPGroup.of_card_dvd_pow (n := 3)
  change Nat.card C ∣ 8
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · simp [h]
  · simp [h]
  · exact False.elim (hthree (by simp [h]))
  · simp [h]
  · exact False.elim (hthree (by simp [h]))
  · exact False.elim (hseven (by simp [h]))
  · simp [h]
  · exact False.elim (hthree (by simp [h]))
  · exact False.elim (hseven (by simp [h]))
  · exact False.elim (hthree (by simp [h]))
  · exact False.elim (hthree (by simp [h]))
  · exact False.elim (hseven (by simp [h]))
  · exact False.elim (hthree (by simp [h]))
  · exact False.elim (hseven (by simp [h]))
  · exact False.elim (hthree (by simp [h]))
  · exact False.elim (hthree (by simp [h]))
