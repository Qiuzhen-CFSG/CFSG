module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLeftBlock
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original Chapter 12 left block alternative

Apply the uniform local Cartan argument to the actual whole reduced subgroup
of LT. The result retains the original left chi-block, or constructs a
nontrivial characteristic subgroup of Baum(T), normalized by LT and escaped
by the literal right residual. Its full normalizer lies in N_G(L).

No block, local-class or characteristic-pair premise is supplied by the
caller. The companion RightBlock module supplies the right application.
The block exclusions and torus argument remain necessary.
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

/-- The first block application on the original subgroups and literal residual. -/
theorem rankOne_local_cartan_noncentral_left_block_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T) :
    ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G))) ∨
      ∃ E : Subgroup (ChapterB.baumann (T : Subgroup G)), E.Characteristic ∧ E ≠ ⊥ ∧
        L ⊔ (T : Subgroup G) ≤ normalizer
          (E.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ∧
        ¬ residual H ≤ normalizer
          (E.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ∧
        normalizer (E.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ≤
          normalizer (L : Set G) :=
  localCartan_noncentral_left_block_alternative
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
