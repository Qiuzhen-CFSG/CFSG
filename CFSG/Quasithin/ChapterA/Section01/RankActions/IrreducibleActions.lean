module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.IrreducibleActions.Reduction
public import Theory.GroupAction.IrreducibleSmallLinear

/-!
# Irreducible normalizer actions on small odd-prime groups

This module proves A.1.32(1,2), retaining the concrete Heisenberg and cyclic
isomorphisms and the actual ambient center image. The small-model theorem
bounds |R/Φ(R)| by r². Rank two makes P noncyclic, so irreducibility forces
the determinant image, and then the image in SL₂(r), to be trivial. The
group-theoretic reductions now give centralization or inner action, and
the ambient rank bound identifies R with P or its center.

The earlier conditional consequence theorem is preserved. Its unconditional
version supplies precisely the commuting and normal-or-order-p implications
used in the Chapter 1 component reduction, with the trivial-action premise
discharged for the literal conjugation homomorphism.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.32(1,2), printed pp.28–29. Clause (2) retains the omitted R = 1 case;
the printed two alternatives are also supplied with explicit R ≠ 1.
-/

namespace CFSG.Quasithin.ChapterA.IrreducibleActions
open Subgroup

/-- The two implications used by Chapter 1, conditional on the separate
trivial-Frattini-action step. This theorem does not assume the Chapter 1 contract. -/
public theorem action_implications_of_trivial_frattini_action
    {G : Type*} [Group G] [Finite G]
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hr : Odd r) (hp : Odd p)
    (R P : Subgroup G) [R.Normal] (hR : IsPGroup r R)
    (hoR : omega₁ R (p := r) = ⊤)
    (hcR : (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥) (hmR : primeRank r R ≤ 2)
    (hP : IsPGroup p P) (hoP : omega₁ P (p := p) = ⊤)
    (hcP : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥) (hmP : primeRank p P = 2)
    (hirr : IsNormalizerFrattiniIrreducible P)
    (hfix : frattiniConjugationHom P R le_normalizer_of_normal = 1) :
    (r ≠ p → ⁅R, P⁆ = ⊥) ∧
      (r = p → primeRank p G = 2 → R ≠ ⊥ → R = P ∨ Nat.card R = p) := by
  constructor
  · intro hne
    rcases alternatives_of_frattiniConjugationHom_eq_one hr R P hR hoR hcR hmR hP hfix
      with hcomm | ⟨heq, _⟩
    · exact hcomm
    · exact (hne heq.symm).elim
  · intro heq hmG hne
    subst r
    rcases rank_two_alternatives_of_frattiniConjugationHom_eq_one hp R P hR hoR hcR hmR
        hP hoP hcP hmP hirr hmG hfix with hb | he | ⟨hc, _⟩
    · exact (hne hb).elim
    · exact Or.inl he
    · exact Or.inr hc

end CFSG.Quasithin.ChapterA.IrreducibleActions

open Subgroup
namespace CFSG.Quasithin.ChapterA

/-- The linear-action step of A.1.32: the actual conjugation action of P on
R/Φ(R) is trivial. The stronger small-linear theorem needs only noncyclicity
of P, supplied here by rank two; its omega and class assumptions are unnecessary. -/
public theorem IrreducibleActions.frattiniConjugationHom_eq_one
    {G : Type*} [Group G] [Finite G]
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hr : Odd r) (hp : Odd p)
    (R P : Subgroup G) [R.Normal] (hR : IsPGroup r R)
    (hoR : omega₁ R (p := r) = ⊤)
    (hcR : (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥) (hmR : primeRank r R ≤ 2)
    (hP : IsPGroup p P) (hmP : primeRank p P = 2)
    (hirr : IsNormalizerFrattiniIrreducible P) :
    frattiniConjugationHom P R le_normalizer_of_normal = 1 := by
  have hnc : ¬ IsCyclic P := by
    intro hcyc
    let := hcyc
    let S : Sylow p P := Classical.choice inferInstance
    have hm := S.primeRank_le_one_of_isCyclic inferInstance
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hp.not_two_dvd_nat (dvd_refl 2)
  exact hirr.frattiniConjugationHom_eq_one_of_card_le_sq hp2 hR
    (small_frattini_card hr hR hoR hcR hmR) hP hnc

/-- A.1.32(1): P centralizes R, or the primes agree, R is the concrete prime
Heisenberg group, and P lies in R C_G(R). The source hypotheses on P are
retained even though the linear argument does not need its omega or class bounds. -/
public theorem lemma_A_1_32_1
    {G : Type*} [Group G] [Finite G]
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hr : Odd r) (hp : Odd p)
    (R P : Subgroup G) [R.Normal] (hR : IsPGroup r R)
    (hoR : omega₁ R (p := r) = ⊤)
    (hcR : (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥) (hmR : primeRank r R ≤ 2)
    (hP : IsPGroup p P) (_hoP : omega₁ P (p := p) = ⊤)
    (_hcP : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥) (hmP : primeRank p P = 2)
    (hirr : IsNormalizerFrattiniIrreducible P) :
    ⁅R, P⁆ = ⊥ ∨ (p = r ∧ Nonempty (R ≃* HeisenbergPrime p) ∧
      P ≤ R ⊔ centralizer (R : Set G)) := by
  exact IrreducibleActions.alternatives_of_frattiniConjugationHom_eq_one
    hr R P hR hoR hcR hmR hP
    (IrreducibleActions.frattiniConjugationHom_eq_one hr hp R P hR hoR hcR hmR hP hmP hirr)

/-- A.1.32(2), with the omitted trivial case included: in ambient p-rank two,
R is trivial, equals P, or is cyclic of order p and is the actual ambient
image of the center of the Heisenberg group P. -/
public theorem lemma_A_1_32_2
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (R P : Subgroup G) [R.Normal]
    (hR : IsPGroup p R) (hoR : omega₁ R (p := p) = ⊤)
    (hcR : (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥) (hmR : primeRank p R ≤ 2)
    (hP : IsPGroup p P) (hoP : omega₁ P (p := p) = ⊤)
    (hcP : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥) (hmP : primeRank p P = 2)
    (hirr : IsNormalizerFrattiniIrreducible P) (hmG : primeRank p G = 2) :
    R = ⊥ ∨ R = P ∨ (Nat.card R = p ∧ Nonempty (R ≃* Multiplicative (ZMod p)) ∧
      Nonempty (P ≃* HeisenbergPrime p) ∧ R = (center P).map P.subtype) := by
  exact IrreducibleActions.rank_two_alternatives_of_frattiniConjugationHom_eq_one
    hp R P hR hoR hcR hmR hP hoP hcP hmP hirr hmG
    (IrreducibleActions.frattiniConjugationHom_eq_one hp hp R P hR hoR hcR hmR hP hmP hirr)

/-- The printed two alternatives of A.1.32(2), with the necessary
nontriviality hypothesis on R stated explicitly. -/
public theorem lemma_A_1_32_2_of_ne_bot
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (R P : Subgroup G) [R.Normal]
    (hR : IsPGroup p R) (hoR : omega₁ R (p := p) = ⊤)
    (hcR : (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥) (hmR : primeRank p R ≤ 2)
    (hP : IsPGroup p P) (hoP : omega₁ P (p := p) = ⊤)
    (hcP : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥) (hmP : primeRank p P = 2)
    (hirr : IsNormalizerFrattiniIrreducible P) (hmG : primeRank p G = 2) (hne : R ≠ ⊥) :
    R = P ∨ (Nat.card R = p ∧ Nonempty (R ≃* Multiplicative (ZMod p)) ∧
      Nonempty (P ≃* HeisenbergPrime p) ∧ R = (center P).map P.subtype) :=
  (lemma_A_1_32_2 hp R P hR hoR hcR hmR hP hoP hcP hmP hirr hmG).resolve_left hne

/-- The two A.1.32 implications used in Chapter 1's component reduction.
The auxiliary trivial-action premise is discharged from the source hypotheses.
The irreducibility predicate uses the same literal quotient
and conjugation map as Chapter 1's `RankTwoActionImplications`. -/
public theorem IrreducibleActions.action_implications
    {G : Type*} [Group G] [Finite G]
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hr : Odd r) (hp : Odd p)
    (R P : Subgroup G) [R.Normal] (hR : IsPGroup r R)
    (hoR : omega₁ R (p := r) = ⊤)
    (hcR : (⊤ : Subgroup R).lowerCentralSeries 2 = ⊥) (hmR : primeRank r R ≤ 2)
    (hP : IsPGroup p P) (hoP : omega₁ P (p := p) = ⊤)
    (hcP : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥) (hmP : primeRank p P = 2)
    (hirr : IsNormalizerFrattiniIrreducible P) :
    (r ≠ p → ⁅R, P⁆ = ⊥) ∧
      (r = p → primeRank p G = 2 → R ≠ ⊥ → R = P ∨ Nat.card R = p) :=
  action_implications_of_trivial_frattini_action hr hp R P hR hoR hcR hmR
    hP hoP hcP hmP hirr
    (frattiniConjugationHom_eq_one hr hp R P hR hoR hcR hmR hP hmP hirr)

end CFSG.Quasithin.ChapterA
