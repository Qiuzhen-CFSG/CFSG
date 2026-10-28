module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.Setup
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.FrattiniPair
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeFive

/-!
# Ratio and conditional assembly of the empty-family Xi-minus argument

Apply the separate source assertion 15.4.2(4) to the original XT and its
normalizer N_G(X). Solvability proves uniqueness independently of 3.2.13,
and normality puts [R₂(XT),X] inside O₂(N_G(X)). The quotient and action
below are the literal centralizer quotient and its conjugation action.

This is a conditional ratio step, not the Xi-minus inclusion. The reducedness
and exact Sylow kernel of this original module remain explicit until the
A.4.11/irreducibility argument supplies them. The subsequent D.2.13 and
five-group factor construction remain with this source branch's assembly.
The final conditional theorem applies the prime and factor outputs to the
literal Earlier1542 consumer; it does not assert either missing output.

Source: Aschbacher--Smith, 3.2.13, printed pp.584--585, and 15.4.2(4),
printed pp.1155--1156. The latter replaces 3.1.8 only in this application.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual source module satisfies the ratio bound once its reducedness
and exact original Sylow kernel have been proved. All remaining applicability
conditions of 15.4.2(4) are discharged here. -/
theorem source_cubicRatio_of_reduced_kernel
    (hA : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple K)
    (hC : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple K)
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (h44 : MaximalPrimeFive.Earlier1542Four (G := G))
    {X : Subgroup G} (hX : X ∈ Chapter1.Xi G (T : Subgroup G))
    (hred : IsPReduced 2 (sourceModule (T : Subgroup G) X))
    (hkernel : (T : Subgroup G).subgroupOf (sourceGroup (T : Subgroup G) X) ⊓
      centralizer (sourceModule (T : Subgroup G) X : Set (sourceGroup (T : Subgroup G) X)) =
        pCore 2 (sourceGroup (T : Subgroup G) X)) :
    let V := sourceModule (T : Subgroup G) X
    let := hred.normal
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set (sourceGroup (T : Subgroup G) X))))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  let H := sourceGroup (T : Subgroup G) X
  let V := sourceModule (T : Subgroup G) X
  let M := normalizer (X : Set G)
  have huniq := source_normalizer_unique hA hC T h hX
  have hHM : H ≤ M := sup_le X.le_normalizer hX.invariant
  have hNM : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N → N = M := by
    intro N hN hHN
    have hn : N ∈ ({M : Subgroup G | IsMaximalTwoLocal M ∧ H ≤ M} : Set (Subgroup G)) :=
      ⟨hN, hHN⟩
    rw [huniq.2] at hn
    exact Set.mem_singleton_iff.mp hn
  exact h44 T h H M ⟨hX.join_mem_H, show (T : Subgroup G) ≤ H from le_sup_right⟩
    huniq.1 hHM hNM V hred (hkernel.trans (source_centralizer_core hX).symm)
    (sourceModule_le_normalizerCore hX)

/-- Conditional terminal assembly from the prime bound and actual preserved
Frattini factors. These two inputs still require their source proofs. -/
theorem source_XiStarF_subset_XiMinus_of_prime_and_pair (T : Subgroup G)
    (hprime : ∀ X ∈ Chapter1.XiStarF G T, ∀ p : ℕ, p.Prime → Odd p →
      Chapter1.XiOddQuotient p (Chapter1.XiQuotient X) → p = 3 ∨ p = 5)
    (hpair : ∀ X ∈ Chapter1.XiStarF G T,
      Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X) → HasNormalizerFrattiniPair X) :
    Chapter1.XiStarF G T ⊆ Chapter3.XiMinus G T := by
  intro X hX
  obtain ⟨p, hp, ho, hq, hdiv⟩ := hX.1.1.card_prime_divisors
  rcases hprime X hX p hp ho hq with he | he
  · refine ⟨hX.1.1, Or.inl ?_⟩
    simpa only [he] using hdiv
  · subst p
    obtain ⟨B, C, hB, hC, hne, hgen, hperm⟩ := hpair X hX hq
    let : Fact (Nat.Prime 5) := ⟨hp⟩
    exact source_mem_XiMinus_of_frattini_pair hX.1.1 hq.isPGroup
      B C hB hC hne hgen hperm

/-- The actual Earlier1542 application. Final source assembly must discharge
the prime and factor callbacks using the original reduced module and the
separate 15.4.2(4) bound, rather than assuming the Xi-minus inclusion. -/
theorem source_earlier1542_of_prime_and_pair
    (hA : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple K)
    (hC : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple K)
    (hprime : ∀ T : Sylow 2 G, SourceHypotheses T →
      ∀ X ∈ Chapter1.XiStarF G (T : Subgroup G), ∀ p : ℕ, p.Prime → Odd p →
        Chapter1.XiOddQuotient p (Chapter1.XiQuotient X) → p = 3 ∨ p = 5)
    (hpair : ∀ T : Sylow 2 G, SourceHypotheses T →
      ∀ X ∈ Chapter1.XiStarF G (T : Subgroup G),
        Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X) → HasNormalizerFrattiniPair X) :
    Earlier1542 (G := G) :=
  TheoremCInputs.source_earlier1542 hA hC
    (fun T h => source_XiStarF_subset_XiMinus_of_prime_and_pair
      (T : Subgroup G) (hprime T h) (hpair T h))

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
