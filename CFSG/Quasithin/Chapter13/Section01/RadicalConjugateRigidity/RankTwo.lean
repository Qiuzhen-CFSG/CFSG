module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.IrreducibleActions
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Transfer
public import Theory.GroupAction.NormalizerFrattiniTransport
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.Quasithin.Rank

/-!
# The rank-two radical comparison in 13.1.11

The elementary or extraspecial odd groups defining Ξ have exponent p and
class at most two. In a strongly quasithin ambient group they have rank two.
Thus A.1.32 identifies a normal such radical with any such subgroup whose
normalizer is irreducible. Both the trivial and order-p alternatives are
excluded by the actual noncyclic radical, rather than by an extra assumption.

Source: Aschbacher--Smith 13.1.11, printed p.872, using A.1.32(2).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity
open Chapter1
variable {G : Type*} [Group G] [Finite G]

private theorem omega_class {Y : Type*} [Group Y] {p : ℕ}
    (h : XiOddQuotient p Y) : omega₁ Y (p := p) = ⊤ ∧
      (⊤ : Subgroup Y).lowerCentralSeries 2 = ⊥ := by
  have he : Monoid.exponent Y ∣ p := by
    rcases h with ⟨he, _⟩ | ⟨_, _, hx⟩
    · exact he.exponent_dvd_p
    · rw [hx]
  constructor
  · apply top_unique
    intro x _
    apply Subgroup.subset_closure
    change x ^ (p ^ 1) = 1
    simpa only [pow_one] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he x
  · have hd : _root_.commutator Y ≤ center Y := by
      rcases h with ⟨hE, _⟩ | ⟨hE, _, _⟩
      · let _ := hE
        rw [commutator_eq_bot]
        exact bot_le
      · let _ := hE.quotient_elementary_abelian
        exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    rw [show 2 = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ, top_lowerCentralSeries_one]
    exact bot_unique ((commutator_mono hd le_rfl).trans (commutator_center_left ⊤).le)

/-- Rank two follows from the ambient bound and the noncyclic defining Ξ groups. -/
theorem primeRank_eq_two {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hG : IsStronglyQuasithin G) (P : Subgroup G) (hP : XiOddQuotient p P) :
    primeRank p P = 2 := by
  have hu := (primeRank_subgroup_le p P).trans (hG p Fact.out ho)
  have hl : ¬ primeRank p P ≤ 1 := by
    intro hm
    apply hP.not_isCyclic
    apply hP.isPGroup.isCyclic_of_odd_of_elementary_card_le ho
    intro E he
    let _ := he
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hm E
  omega

/-- The complete A.1.32 comparison needed in 13.1.11. -/
theorem normal_radical_eq {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hG : IsStronglyQuasithin G) (R P : Subgroup G) [R.Normal]
    (hR : XiOddQuotient p R) (hP : XiOddQuotient p P)
    (hirr : IsNormalizerFrattiniIrreducible P) : R = P := by
  have hmP := primeRank_eq_two ho hG P hP
  have hmR := primeRank_eq_two ho hG R hR
  have hmG : primeRank p G = 2 := le_antisymm (hG p Fact.out ho)
    (hmP.ge.trans (primeRank_subgroup_le p P))
  obtain ⟨hoR,hcR⟩ := omega_class hR
  obtain ⟨hoP,hcP⟩ := omega_class hP
  rcases ChapterA.lemma_A_1_32_2 ho R P hR.isPGroup hoR hcR hmR.le
      hP.isPGroup hoP hcP hmP hirr hmG with hb | he | ⟨hc, _⟩
  · subst R
    exact (hR.not_isCyclic inferInstance).elim
  · exact he
  · exact (hR.not_isCyclic (isCyclic_of_prime_card hc)).elim

end CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity
