module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLeftCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Reselecting the original left two-core in Chapter 12

The noncentral A₇ configuration forces a left block. Its core squares
centralize that block, and the previously proved Sylow fixed subgroup is
trivial. The whole ambient two-core is therefore an elementary reduced
module and supplies the universal rank-one Input. Applying the original
cubic fixed-space theorem to that core makes it fully moved, identifying
it with the intrinsic block layer. No semisimplicity or equality of the
core with the layer is assumed.

This removes the extra-core premise in the remaining degree-two left-block
order argument. Source: Aschbacher–Smith 5.1.13, printed p.638,
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

/-- The entire original left two-core is an admissible module in the universal Input. -/
theorem rankOne_local_cartan_left_core_input
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K) :
    Input KnownSimple.IsKnownSimple T L ((L ⊔ (T : Subgroup G)).pCoreIn 2) n :=
  a.left_core_input
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d

/-- The actual ambient left core equals the intrinsic layer of the literal left block. -/
theorem rankOne_local_cartan_left_core_block_layer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X C) (a : LocalA7Configuration T L H X K) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      (ChapterC.blockU (L.subgroupOf (L ⊔ (T : Subgroup G)))).map
        ((L ⊔ (T : Subgroup G)).subtype.comp (L.subgroupOf (L ⊔ (T : Subgroup G))).subtype) :=
  a.left_core_block_layer
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
