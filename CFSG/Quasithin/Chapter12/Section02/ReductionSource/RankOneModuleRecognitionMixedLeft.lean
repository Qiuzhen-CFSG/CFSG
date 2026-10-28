module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognition
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarMixedLeftSource

/-!
# The original Chapter 12 small branch supplies the mixed left parabolic

Construct Hypothesis 6.1.1 on the whole reduced subgroup from the literal
generation-one branch. The proved 6.1.5 left construction then supplies its
actual Baumann Sylow, quotient, characteristic-two identity and Hall.
The same G,T,L and outside H are retained. The preceding natural fixed
quotient is still an explicit 6.1.4 source duty; no SmallExit or full 6.1.5
conclusion is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The actual small rank-one branch receives every left field used in the
mixed F.1.1 pair, without an extra left-group or Hall-selection premise. -/
theorem rankOne_small_mixed_left_of_natural_quotient_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hsmall : ∀ I ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ChapterE.generationParameter I ≤ 1)
    (hmodel : ¬ Chapter6.Source.IsOneOrTwoA5Modules L (RankOneModule.commutatorLayer T L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hm : Chapter6.Source.IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
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
  have h611 := RankOneModule.hypothesis611_of_generation_le_one
    D h.toHypothesis1221 hn hpsl hsmall hmodel
  exact h611.mixed_left_source_of_natural_quotient
    (D.rankOne_hasMaximalOutside_of_many h.toHypothesis1221 hmany) hH hm hZH

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
