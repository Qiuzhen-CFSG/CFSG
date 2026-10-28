module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionMixedLeft
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientOmega

/-!
# The natural fixed quotient in the original moving rank-one branch

The literal chosen module and small-generation hypotheses construct
Hypothesis 6.1.1 on R₂(LT). If the original Thompson group moves that
reduced subgroup, the proved FF selection and omega-span restriction
supply the exact natural fixed quotient. The downstream mixed-left
construction then needs no quotient-model input in this branch.

The stationary branch of source 6.1.4 remains the doubled-natural and
orthogonal weak-closure analysis; the unconditional SmallExit is not
asserted by these consumers.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The original moving small rank-one branch supplies its own natural quotient. -/
theorem rankOne_small_natural_fixed_quotient_of_thompson_moves_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hsmall : ∀ I ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ChapterE.generationParameter I ≤ 1)
    (hmodel : ¬ Chapter6.Source.IsOneOrTwoA5Modules L (RankOneModule.commutatorLayer T L))
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (RankOneModule.wholeReduced T L : Set G)) :
    Chapter6.Source.IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n := by
  have h611 := RankOneModule.hypothesis611_of_generation_le_one
    D h.toHypothesis1221 hn hpsl hsmall hmodel
  exact h611.omega_natural_fixed_quotient_of_thompson_moves
    (D.rankOne_hasMaximalOutside_of_many h.toHypothesis1221 hmany) hj

/-- Every original mixed-left field follows in the moving branch, retaining
its actual outside H and noncentral omega action. -/
theorem rankOne_small_mixed_left_of_thompson_moves_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hsmall : ∀ I ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ChapterE.generationParameter I ≤ 1)
    (hmodel : ¬ Chapter6.Source.IsOneOrTwoA5Modules L (RankOneModule.commutatorLayer T L))
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (RankOneModule.wholeReduced T L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    let S := ChapterB.baumann (T : Subgroup G)
    Chapter1.IsSylowIn 2 S (L ⊔ S) ∧
      ClassicalGroup.IsPSL ((L ⊔ S : Subgroup G) ⧸ pCore 2 (L ⊔ S : Subgroup G))
        2 (2 ^ n) ∧
      generalizedFitting (L ⊔ S : Subgroup G) = pCore 2 (L ⊔ S : Subgroup G) ∧
      ∃ A : Subgroup G, A ≤ Chapter6.Source.RankOneGeneric.localBorel T L ∧
        IsHallSubgroup OddHall.oddPrimes
          (A.subgroupOf (Chapter6.Source.RankOneGeneric.localBorel T L)) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ ∧
        A ⊔ H ∈ Chapter1.HOver G (T : Set G) ∧
        A ≤ normalizer (S : Set G) ∧
        ChapterF.Source.borel (L ⊔ S) S = S ⊔ A := by
  exact D.rankOne_small_mixed_left_of_natural_quotient_of_many
    h hmany hn hpsl hsmall hmodel hH
    (D.rankOne_small_natural_fixed_quotient_of_thompson_moves_of_many
      h hmany hn hpsl hsmall hmodel hj) hZH

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
