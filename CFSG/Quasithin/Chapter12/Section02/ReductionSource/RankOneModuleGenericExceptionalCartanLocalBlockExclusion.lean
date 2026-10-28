module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBlockExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Original Chapter 12 applications of the right-block exclusion

The chosen module supplies the universal rank-one Input without changing
its group or Sylow marking. The original right residual cannot be a block
in the noncentral A₇ configuration. C.1.28 and the degree theorem leave a
degree-two left block, while a right block forces omega-centralization.

The degree-two left-block exclusion, whole-module recognition and component
sieve are still required for the source theorem.
Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.638,795,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C K : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The original literal right residual cannot be a block in the A₇ configuration. -/
theorem rankOne_local_cartan_not_right_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K) :
    ¬ ChapterC.IsChiBlockIn (pResidual 2 H) :=
  a.not_right_block
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d

/-- The surviving C.1.28 block is the original left subgroup. -/
theorem rankOne_local_cartan_left_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K) :
    ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G))) :=
  a.left_block
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d

/-- With the FF reduction discharged, the noncentral branch has degree two
and a left block, while its literal right residual is not a block. -/
theorem rankOne_local_cartan_noncentral_degree_two_left_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T) :
    n = 2 ∧ ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧
      ¬ ChapterC.IsChiBlockIn (pResidual 2 H) :=
  localCartan_noncentral_degree_two_left_block
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC

/-- A block on the original right residual forces omega-centralization. -/
theorem rankOne_local_cartan_centralizes_of_right_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C)
    (hb : ChapterC.IsChiBlockIn (pResidual 2 H)) : X ≤ omegaCentralizer T :=
  localCartan_centralizes_of_right_block
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hb

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
