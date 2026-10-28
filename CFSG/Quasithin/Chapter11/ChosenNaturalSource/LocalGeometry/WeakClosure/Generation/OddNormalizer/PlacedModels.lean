module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedOuter
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.UnitaryFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.UnitaryFive
public import CFSG.Quasithin.ChapterA.Section02.OddBModelTwoRank
public import Theory.SpecificGroups.FiniteModelTwoRank
public import Theory.SpecificGroups.SymplecticSix.OrderRank

/-!
# The complete B-catalogue after natural residual placement

The literal central image retains twelve factors of two, excluding all
alternating rows, binary Sp₆, J₃ and McL. Its elementary image has rank at
least six, excluding odd PSL₂, PSL₃ and PSU₃. The previously proved C-model
inspection leaves J₄ and Ru, and the unitary-four two-local bounds exclude
every binary unitary-four row. The full parabolic orders also exclude
PSU₅(4). Thus the additional placed B-models are precisely the remaining
odd four-dimensional/G₂ rows.
All field, covering and isomorphism conventions remain those of Theorem B.

The Source endpoint applies this sieve to the component of the original Hall
kernel normalizer. Exclusion of the surviving rows remains with this task.
Source: Aschbacher--Smith 4.4.12 and the following inspection, pp.621--622.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open ChapterA.Section02 ClassificationModels

/-- The actual B-only odd rows not excluded by the present rank bounds. -/
def RemainingOddPlacedModels (Q : Type*) [Group Q] : Prop :=
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSp Q 2 p) ∨
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ IsG2At Q p) ∨
  (∃ r : ℕ, r.Prime ∧ (∃ k : ℕ, r = 2 ^ (2 ^ k) + 1) ∧ ClassicalGroup.IsPSL Q 4 r) ∨
  (∃ s : ℕ, s.Prime ∧ (∃ b : ℕ, s + 1 = 2 ^ b) ∧ ClassicalGroup.IsPSU Q 4 s)

/-- Remaining actual central quotients of a component containing the natural residual. -/
def RemainingPlacedModels (Q : Type*) [Group Q] : Prop :=
  (Nonempty (Q ≃* Janko4.Model) ∨ Nonempty (Q ≃* Rudvalis.Model)) ∨
  RemainingOddPlacedModels Q

private theorem odd_models_of_rank_six {Q : Type*} [Group Q] [Finite Q]
    (h : IsTheoremBOddModel Q) (hr : 6 ≤ primeRank 2 Q) : RemainingOddPlacedModels Q := by
  cases h with
  | linear_two q ho hm => have := odd_psl_two_twoRank_le_two ho hm; omega
  | linear_three p e hp ho he hm => have := odd_psl_three_twoRank_le_two ho.pow hm; omega
  | unitary_three p e hp ho he hm => have := odd_psu_three_twoRank_le_two ho.pow hm; omega
  | symplectic p hp ho hm => exact Or.inl ⟨p,hp,ho,hm⟩
  | g2 p hp ho hm => exact Or.inr (Or.inl ⟨p,hp,ho,hm⟩)
  | linear_four r hp hf hm => exact Or.inr (Or.inr (Or.inl ⟨r,hp,hf,hm⟩))
  | unitary_four s hp hs hm => exact Or.inr (Or.inr (Or.inr ⟨s,hp,hs,hm⟩))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {Q : Type*} [Group Q] [Finite Q]
include D S

/-- Sieve the full Theorem B list on the literal projected covering image. -/
theorem NaturalCoverImage.theoremB_models (h : NaturalCoverImage D Q)
    (hm : IsTheoremBModel Q) : RemainingPlacedModels Q := by
  have hd := h.two_power_dvd D S
  have shared (hc : IsTheoremCModel Q) : RemainingPlacedModels Q :=
    Or.inl (h.theoremC_models D S hc)
  cases hm with
  | alternating n hn e =>
    obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv] at hd
    have hp := (alternatingGroup (Fin n)).card_subgroup_dvd_card
    rw [Nat.card_perm,Nat.card_fin] at hp
    have hh := hd.trans (hp.trans (Nat.factorial_dvd_factorial hn))
    norm_num [Nat.factorial] at hh
  | odd hm => exact Or.inr (odd_models_of_rank_six hm (h.twoRank_ge_six D S))
  | bender hm => exact shared (.bender hm)
  | linear_binary n hn hm => exact shared (.linear_binary n hn hm)
  | rank_two f hm =>
    cases hm with
    | linear hf hm => exact shared (.rank_two f (.linear hf hm))
    | unitary_four hf hm => exact (h.not_binary_unitary_four D S hf hm).elim
    | unitary_five hf hm =>
      subst f
      exact (h.not_unitary_five_four D S hm).elim
    | symplectic hf hm => exact shared (.rank_two f (.symplectic hf hm))
    | g2 hf hm => exact shared (.rank_two f (.g2 hf hm))
    | triality hf hm => exact shared (.rank_two f (.triality hf hm))
    | ree_f4 m hm hf e => exact shared (.rank_two f (.ree_f4 m hm hf e))
    | symplectic_derived hf e => exact shared (.rank_two f (.symplectic_derived hf e))
    | g2_derived hf e => exact shared (.rank_two f (.g2_derived hf e))
    | tits hf e => exact shared (.rank_two f (.tits hf e))
  | symplectic_binary hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv] at hd
    have hh := hd.trans (card_quotient_dvd_card
      (center (Theory.SpecificGroups.SymplecticSix.Sp F)))
    rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hF] at hh
    norm_num at hh
  | sporadic hm =>
    rcases hm with hm | hm | hm
    · obtain ⟨n,⟨e⟩⟩ := hm
      by_cases hn : n = .j3
      · subst n
        rw [Nat.card_congr e.toEquiv] at hd
        change 2 ^ 12 ∣ Nat.card Sporadic.Janko3.Model at hd
        rw [Sporadic.Janko3.model_card] at hd
        norm_num at hd
      · exact shared (.sporadic (Or.inl ⟨n,hn,⟨e⟩⟩))
    · exact shared (.sporadic (Or.inr hm))
    · obtain ⟨e⟩ := hm
      rw [Nat.card_congr e.toEquiv,
        Nat.card_congr Theory.SpecificGroups.McLaughlin.Multiplier.permutationModelEquiv.toEquiv,
        Atlas.Sporadic.McLaughlin.card] at hd
      norm_num [Atlas.Sporadic.McLaughlin.order] at hd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
