module

public import Theory.GroupTheory.ElementaryEightSolvableCore
public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# No minimal normal elementary eight in a solvable {2,3}-group

The literal conjugation image on a minimal normal elementary eight acts
irreducibly and has trivial two-core. The solvable elementary-eight automizer
bound excludes four-divisibility. Its order divides 168, so excluding seven
leaves orders one, two, three and six. The first two give trivial action;
in the latter two a normal cubic subgroup has nontrivial fixed points, since
eight is not congruent to one modulo three. Irreducibility contradicts
faithfulness in each case.

This source-neutral obstruction is used for the elementary-eight central
closure rows in the intrinsic Janko-four pair sieve. It assumes no faithful
ambient action and no classification or prescribed model subgroup.
-/

public section
noncomputable section
open Subgroup
private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A solvable automizer of an elementary eight whose order is prime to seven
cannot act irreducibly. -/
theorem not_irreducible_solvable_elementary_eight
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E)) [Group.IsSolvable A]
    (hseven : ¬ 7 ∣ Nat.card A)
    (hirr : ∀ D : Subgroup E, (∀ a : A, ∀ x : E, x ∈ D → a • x ∈ D) →
      D = ⊥ ∨ D = ⊤) : False := by
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE]; decide)
  have hcore : pCore 2 A = ⊥ := irreducible_range_two_core_eq_bot A hirr
  have hfour : ¬ 4 ∣ Nat.card A := by
    intro hh
    have hb := four_le_card_pCore_of_solvable_elementary_eight_automorphisms E hE A hh
    rw [hcore, card_bot] at hb
    omega
  have hd : Nat.card A ∣ 168 := (card_mulAut_of_elementary_eight E hE) ▸
    A.card_subgroup_dvd_card
  have hc : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 3 ∨ Nat.card A = 6 := by
    have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : 168 ≠ 0)⟩
    have hh : (168 : ℕ).divisors =
        {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by decide
    rw [hh] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  have htrivial (hc : Nat.card A = 1) : False := by
    have hAb : A = ⊥ := card_eq_one.mp hc
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 (by rw [hE]; decide)
    let D := zpowers x
    have hDc : Nat.card D = 2 := (Nat.card_zpowers x).trans hx
    have hi : ∀ a : A, ∀ x : E, x ∈ D → a • x ∈ D := by
      intro a x hx
      have ha : (a : MulAut E) = 1 := mem_bot.mp (hAb ▸ a.property)
      change (a : MulAut E) x ∈ D
      rw [ha]
      exact hx
    rcases hirr D hi with hh | hh
    · rw [hh, card_bot] at hDc
      omega
    · rw [hh, card_top, hE] at hDc
      omega
  rcases hc with hc | hc | hc
  · exact htrivial hc
  · have hp : IsPGroup 2 A := IsPGroup.of_card (n := 1) hc
    have hle : (⊤ : Subgroup A) ≤ pCore 2 A :=
      le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩
    have he : (⊤ : Subgroup A) = ⊥ := le_bot_iff.mp (hcore ▸ hle)
    have hh := congrArg (fun K : Subgroup A => Nat.card K) he
    rw [card_top, card_bot, hc] at hh
    omega
  let P : Sylow 3 A := Classical.choice inferInstance
  have hPc : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity]
    rcases hc with hc | hc
    · rw [hc]
      norm_num
    · rw [hc, show (6 : ℕ) = 2 * 3 by rfl,
        Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, (show Nat.Prime 3 by decide).factorization]
  have hn : (P : Subgroup A).Normal := by
    have hh := (P : Subgroup A).card_mul_index
    rw [hPc] at hh
    have hi : (P : Subgroup A).index ≤ 2 := by rcases hc with hc | hc <;> omega
    have hcount : Nat.card (Sylow 3 A) ≤ 2 :=
      (Nat.le_of_dvd (by rcases hc with hc | hc <;> omega) P.card_dvd_index).trans hi
    have hm := card_sylow_modEq_one 3 A
    change Nat.card (Sylow 3 A) % 3 = 1 % 3 at hm
    have hone : Nat.card (Sylow 3 A) = 1 := by omega
    let : Subsingleton (Sylow 3 A) := (Nat.card_eq_one_iff_unique.mp hone).1
    exact P.normal_of_subsingleton
  let : (P : Subgroup A).Normal := hn
  let F := FixedPoints.subgroup P E
  have hinv := fixedPoints_isInvariant_of_normalizing_actor (V := E)
    (⊤ : Subgroup A) (P : Subgroup A) (by rw [normalizer_eq_top])
  have hF : F = ⊤ := by
    apply (hirr F (fun a x hx => (hinv.invariant ⟨a, mem_top a⟩ x).mp hx)).resolve_left
    intro hh
    have hm := P.isPGroup'.card_modEq_card_fixedPoints E
    change Nat.card E % 3 = Nat.card F % 3 at hm
    rw [hE, hh, card_bot] at hm
    omega
  have hPb : (P : Subgroup A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have hx : x ∈ F := hF ▸ mem_top x
    exact hx ⟨a, ha⟩
  have hh : Nat.card P = 1 := by rw [hPb, card_bot]
  omega

/-- A minimal normal elementary abelian subgroup of order eight cannot occur
in a finite solvable group with only two and three as prime divisors. -/
theorem not_minimal_normal_elementary_eight_of_solvable_two_three
    {H : Type*} [Group H] [Finite H] (E : Subgroup H) [E.Normal]
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) (hs : Group.IsSolvable H)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3)
    (hmin : ∀ B : Subgroup H, B ≤ E → B.Normal → B = ⊥ ∨ B = E) : False := by
  let f : H →* MulAut E := MulAut.conjNormal
  let A := f.range
  let : Group.IsSolvable H := hs
  let : Group.IsSolvable A := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hseven : ¬ 7 ∣ Nat.card A := by
    intro hh
    have hp := hprime 7 (by decide) (hh.trans (card_range_dvd f))
    omega
  apply not_irreducible_solvable_elementary_eight hE A hseven
  intro D hD
  have hn : (D.map E.subtype).Normal := by
    constructor
    rintro x ⟨x, hx, rfl⟩ h
    exact ⟨f h x, hD ⟨f h, ⟨h, rfl⟩⟩ x hx, rfl⟩
  rcases hmin (D.map E.subtype) (map_subtype_le D) hn with hh | hh
  · exact Or.inl ((D.map_eq_bot_iff_of_injective E.subtype_injective).mp hh)
  · apply Or.inr
    apply Subgroup.map_injective E.subtype_injective
    rw [hh, ← MonoidHom.range_eq_map, E.range_subtype]
