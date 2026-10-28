module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRightBlock
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Both block alternatives for the original Chapter 12 Cartan inputs

The two local-class applications use one characteristic pair on the
original Baumann subgroup. Local uniqueness eliminates a common normalized
member. Thus the original left residual or the literal right residual is
a chi-block in its corresponding Sylow overgroup.

This is the block dichotomy on p.637. The exclusions of both possibilities
on p.638, the torus argument and source assembly remain necessary.
Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.637–638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The source block dichotomy on the literal original components. -/
theorem rankOne_local_cartan_noncentral_block_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T) :
    ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G))) ∨
      ChapterC.IsChiBlockIn (pResidual 2 H) :=
  localCartan_noncentral_block_alternative
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
