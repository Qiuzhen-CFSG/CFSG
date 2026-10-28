module

public import Theory.GroupTheory.ElementaryEightSolvableCore
public import Theory.GroupTheory.ElementaryEightAutomorphismBound

/-!
# A solvable two-core-free elementary-eight automizer

An even-order solvable automorphism subgroup of an elementary eight has
order six if its two-core is trivial. The solvable two-core bound excludes
four-divisibility. Its Sylow two-subgroups therefore have order two, so the
small-automizer bound gives order at most six. Order two is excluded by the
trivial two-core.

This is the order-eight automizer calculation in Janko–Thompson,
Math. Z. 113 (1970), Lemma 3.1, printed pp.387–388.
-/
open Subgroup

/-- A solvable even elementary-eight automizer with trivial two-core has
order six. -/
public theorem card_eq_six_of_elementary_eight_automorphisms_twoCore_eq_bot {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E)) [Group.IsSolvable A]
    (hcore : pCore 2 A = ⊥) (htwo : 2 ∣ Nat.card A) : Nat.card A = 6 := by
  have hfour : ¬ 4 ∣ Nat.card A := by
    intro h
    have hh := four_le_card_pCore_of_solvable_elementary_eight_automorphisms E hE A h
    rw [hcore, card_bot] at hh
    omega
  let P : Sylow 2 A := Classical.choice inferInstance
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnlt : n < 2 := by
    by_contra! hh
    apply hfour
    apply dvd_trans ?_ P.toSubgroup.card_subgroup_dvd_card
    rw [hn]
    exact pow_dvd_pow 2 hh
  have hn1 : n = 1 := by
    have hdiv := P.dvd_card_of_dvd_card htwo
    rw [hn] at hdiv
    interval_cases n <;> norm_num at *
  have hP : Nat.card P = 2 := by rw [hn, hn1]; norm_num
  have hupper := card_le_six_of_elementary_eight_automorphisms E hE A ⟨P, hP⟩
  have hpos := Nat.card_pos (α := A)
  have hcases : Nat.card A = 2 ∨ Nat.card A = 6 := by omega
  rcases hcases with ha | ha
  · have hp : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using ha)
    have htop : (⊤ : Subgroup A) ≤ pCore 2 A :=
      le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩
    have he : (⊤ : Subgroup A) = ⊥ := le_antisymm (hcore ▸ htop) bot_le
    have hh := congrArg (fun K : Subgroup A => Nat.card K) he
    simp only [card_top, card_bot, ha] at hh
    omega
  · exact ha
