module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ComponentPlacement
public import CFSG.Quasithin.ChapterA.Section02.FiniteModelRankExclusions
public import CFSG.Quasithin.ChapterA.Section02.OddBModelTwoRank
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Bounds
public import Theory.SpecificGroups.SymplecticSix.OrderRank

/-!
# Excluding the small odd-normalizer component models

The marked unitary and Suzuki modules have binary rank at least twelve.
After component placement, the odd central covering kernel preserves that
rank. The complete Theorem B list then reduces to the actual Bender and
relative-rank-two characteristic-two groups: the odd rows have rank at most
seven, the finite rows are smaller, J₄ has rank eleven, and the order of
Sp₆(2) has two-part 2⁹. No family is identified solely from its order.

The last theorem applies this sieve to the original normal component and
retains its embedding, residual, odd centralizer and simple quotient section.
The remaining characteristic-two local inspection is not asserted here.
Source: Aschbacher--Smith, 4.4.11--12, printed pp.621--622.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open ChapterA.Section02 ClassificationModels
variable {Q : Type*} [Group Q] [Finite Q]

private theorem binary_symplectic_three_rank
    (h : ClassicalGroup.IsPSp Q 3 2) : primeRank 2 Q ≤ 9 := by
  obtain ⟨F,hF,hfinite,hcard,⟨e⟩⟩ := h
  apply primeRank_le_of_prime_pow_not_dvd
  intro hd
  have hd' : 2 ^ (9 + 1) ∣ Nat.card (Theory.SpecificGroups.SymplecticSix.Sp F) := by
    have hdq := (center (Theory.SpecificGroups.SymplecticSix.Sp F)).card_quotient_dvd_card
    rw [Nat.card_congr e.toEquiv] at hd
    exact hd.trans hdq
  rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hcard] at hd'
  norm_num at hd'

/-- Rank twelve leaves only the actual Bender and relative-rank-two
characteristic-two rows of the full Theorem B list. -/
theorem bender_or_rankTwo_of_rank_twelve
    (h : IsTheoremBModel Q) (hr : 12 ≤ primeRank 2 Q) :
    IsBenderModel Q ∨ ∃ f : ℕ, IsRankTwoModel Q f := by
  rcases h.remaining_of_twoRank_ge_eight (by omega) with ho | hb | hrank | hsp | hj
  · exact (no_theoremB_odd_model_of_twoRank_ge_eight (by omega) ho).elim
  · exact Or.inl hb
  · exact Or.inr hrank
  · have := binary_symplectic_three_rank hsp
    omega
  · obtain ⟨e⟩ := hj
    rw [primeRank_equiv 2 e] at hr
    have := Janko4.TwoRank.model_twoRank_le_eleven
    omega


/-- The actual characteristic-two component, retaining its original ambient
embedding, normality and central quotient section. -/
@[expose] def LieComponentCase {G : Type*} [Group G] (L V A : Subgroup G)
    (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧
    (IsBenderModel (K ⧸ center K) ∨ ∃ f : ℕ, IsRankTwoModel (K ⧸ center K) f) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    12 ≤ primeRank 2 (K ⧸ center K) ∧
    ∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f

/-- Literal consumer of the full B-model sieve: the normal component
constructed above has only the Bender or relative-rank-two alternatives. -/
theorem lie_component_of_rank_twelve
    {G S : Type*} [Group G] [Finite G] [Group S] {L V A : Subgroup G}
    (h : NormalComponentCase L V A S) (hr : 12 ≤ primeRank 2 V) :
    LieComponentCase L V A S := by
  obtain ⟨K,hK,hn,_,hout,hcore,hm,hv,hf,hc,hrK,hsection⟩ := h
  have hr' := hr.trans hrK
  exact ⟨K,hK,hn,hout,hcore,bender_or_rankTwo_of_rank_twelve hm hr',
    hv,hf,hc,hr',hsection⟩

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
