module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic.IndexThree
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.TwoPerfectOrderTwelve
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# The actual local residual in Goldschmidt's pushing-up input

For an S₃ quotient over the two-core, a Sylow two-subgroup has index three.
If no nontrivial characteristic subgroup of that Sylow is ambient-normal,
the proved binary solvable pushing-up theorem gives an order-twelve
two-residual in the characteristic-two case. Its two-perfectness identifies
it with A₄. Otherwise the two-residual is the normal cubic odd core.

This is the local structural input to Goldschmidt (2.14)--(2.15). It reuses
the already proved p=2, q=2 pushing-up argument instead of formalizing the
more general theorem cited as Niles, Theorem 3, in the prepublication source.
Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), pp.384--385;
Stellmacher, *Pushing up* (1986), binary specialization.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] [Finite G]

/-- The original local pushing-up hypotheses determine the actual
two-residual as a cyclic cubic group or A₄. -/
theorem local_residual_cubic_or_alternatingFour
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal) :
    Nonempty ((pResidual 2 G) ≃* Multiplicative (ZMod 3)) ∨
      Nonempty ((pResidual 2 G) ≃* alternatingGroup (Fin 4)) := by
  classical
  by_cases hfit : generalizedFitting G = pCore 2 G
  · have hs : Stellmacher.SectionTwo.Hypotheses G := by
      refine ⟨SymmetricThreeTwoCore.solvable e, ?_, ?_⟩
      · apply even_iff_two_dvd.mpr
        rw [SymmetricThreeTwoCore.card_eq e]
        exact dvd_mul_of_dvd_left (by decide : 2 ∣ 6) _
      · rw [← hfit]
        exact centralizer_generalizedFitting_le G
    obtain ⟨_, hc, hq, _, _⟩ :=
      ChapterC.RankOne.Solvable.MinimalParabolic.index_three_residual hs P
        (SymmetricThreeTwoCore.sylow_index_three e P) hP
    have hr : Nat.card (pResidual 2 G) = 12 := by
      have hh := (pCore 2 (pResidual 2 G)).index_mul_card
      change Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) * _ = _ at hh
      rw [hc, hq] at hh
      exact hh.symm
    exact Or.inr (alternatingFour_of_twoPerfect_card_twelve (isPPerfect_pResidual 2) hr)
  · have hr : Nat.card (pResidual 2 G) = 3 := by
      rw [SymmetricThreeTwoCore.residual_eq_oddCore e hfit]
      exact SymmetricThreeTwoCore.oddCore_card_of_not_characteristic_two e hfit
    exact Or.inl ⟨mulEquivOfPrimeCardEq hr (by simp)⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
