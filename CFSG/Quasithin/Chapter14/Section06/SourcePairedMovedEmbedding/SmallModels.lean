module

public import CFSG.Quasithin.Chapter1.Section01.ModelActions115
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.CarrierSieve
public import Theory.Quasithin.CoprimeRank

/-!
# Small marked rows cannot contain a deleted alternating-five module

An elementary subgroup of order sixteen excludes the odd rows of 1.1.5
by their intrinsic two-rank bound. The alternating-six and alternating-seven
rows, including their specified central three-covers, have two-rank at most
three. The central-cover step uses the actual quotient homomorphism and its
coprime kernel, so it does not identify a cover with its simple quotient.

The source consumer retains exactly the Lie, two-cover, and sporadic branches
of the original marked model conclusion for the same automorphism.

Source: Aschbacher--Smith 14.6.9, p.1026, and 1.1.5(3), pp.501--503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
open Chapter15.Section03.Candidates.ComponentStructure
open ChapterA.Section03.SourceEmbeddings.FiveLocalFF

private theorem small_alternating_rank {n : ℕ} (hn : n ≤ 7) :
    primeRank 2 (alternatingGroup (Fin n)) ≤ 3 := by
  let P : Sylow 2 (alternatingGroup (Fin n)) := Classical.choice inferInstance
  rw [P.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le P).mpr
  intro E _
  apply E.card_le_card_group.trans
  rw [P.card_eq_multiplicity]
  interval_cases n
  · have hc : Nat.card (alternatingGroup (Fin 0)) = 1 := Nat.card_unique
    rw [hc]
    simp
  · have hc : Nat.card (alternatingGroup (Fin 1)) = 1 := Nat.card_unique
    rw [hc]
    simp
  all_goals rw [nat_card_alternatingGroup, Nat.card_fin]; decide +kernel

private theorem fermat_mersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  intro he
  rcases hp.2 with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hpow : 1 < 2 ^ (2 ^ k) := one_lt_pow' (by decide) (by positivity)
    omega
  · by_cases hk0 : k = 0
    · simp only [hk0, pow_zero] at hk
      omega
    · have hev : Even (2 ^ k) := (show Even 2 by decide).pow_of_ne_zero hk0
      rw [← hk, he] at hev
      norm_num at hev

variable {A : Type*} [Group A] [Finite A]

/-- The full alternating action predicate, including its central cover,
has no elementary sixteen in degree at most seven. -/
theorem not_small_alternating_action
    (E : Subgroup A) (hE : IsElementaryAbelian 2 E) (hc : 16 ≤ Nat.card E)
    (α : MulAut A) {n : ℕ} (hn : n ≤ 7) (σ : Equiv.Perm (Fin n)) :
    ¬ AlternatingAction α n σ := by
  intro hm
  have hr : primeRank 2 A ≤ 3 := by
    rcases hm with ⟨e, _⟩ | ⟨_, ⟨ec⟩, e, _⟩
    · rw [primeRank_equiv 2 e]
      exact small_alternating_rank hn
    · have hk : Nat.Coprime 2 (Nat.card (QuotientGroup.mk' (center A)).ker) := by
        rw [QuotientGroup.ker_mk', Nat.card_congr ec.toEquiv]
        change Nat.Coprime 2 (Nat.card (ZMod 3))
        norm_num
      exact (primeRank_le_of_coprime_ker 2 (QuotientGroup.mk' (center A)) hk).trans
        (by rw [primeRank_equiv 2 e]; exact small_alternating_rank hn)
  have hb := (primeRank_le_iff_elementary_card_le A).mp hr E hE
  norm_num at hb
  omega

/-- The original odd model predicate of 1.1.5 cannot contain the elementary
module of a deleted alternating-five block. -/
theorem not_marked_odd_model
    (E : Subgroup A) (hE : IsElementaryAbelian 2 E) (hc : 16 ≤ Nat.card E) :
    ¬ (ClassicalGroup.IsPSL A 3 3 ∨
      ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL A 2 p) := by
  rintro (hm | ⟨p, hp, hm⟩)
  · exact CarrierSieve.not_odd_model E hE hc
      (.linear_three 3 (by decide) (by decide) hm)
  · exact CarrierSieve.not_odd_model E hE hc
      (.linear_two p 1 hp.1 (fermat_mersenne_odd hp) (by decide)
        (by simpa only [pow_one] using hm))

/-- An actual elementary sixteen reduces the complete marked list to its
Lie, central two-cover, and sporadic cases, preserving the marked action. -/
theorem modelAction115_large_elementary_cases
    (E : Subgroup A) (hE : IsElementaryAbelian 2 E) (hc : 16 ≤ Nat.card E)
    {α : MulAut A} (hm : ModelAction115 A α) :
    (IsSimpleGroup A ∧ LieTypeTwoModel A ∧ α ∈ (MulAut.conj (G := A)).range) ∨
    (center A ≠ ⊥ ∧ center A = pCore 2 A ∧
      (ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 4 ∨
        ClassificationModels.IsG2At (A ⧸ pCore 2 A) 4) ∧
      α ∈ (MulAut.conj (G := A)).range) ∨
    (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* name.Carrier) ∧ TwoCentralInner α) := by
  cases hm with
  | lie hs hm hi => exact Or.inl ⟨hs, hm, hi⟩
  | two_cover hn hc hm hi => exact Or.inr (Or.inl ⟨hn, hc, hm, hi⟩)
  | six σ _ ha => exact (not_small_alternating_action E hE hc α (by decide) σ ha).elim
  | seven σ _ ha => exact (not_small_alternating_action E hE hc α (by decide) σ ha).elim
  | odd hm _ => exact (not_marked_odd_model E hE hc hm).elim
  | sporadic name hn hm ha => exact Or.inr (Or.inr ⟨name, hn, hm, ha⟩)

end CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
