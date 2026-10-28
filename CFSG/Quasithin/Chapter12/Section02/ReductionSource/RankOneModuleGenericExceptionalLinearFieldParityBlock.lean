module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupBlock
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParitySolvableCore

/-!
# The actual Chapter12 module in the nonabelian block branch

The chosen-module producer constructs the natural Fundamental Setup.
The odd binary multiplier theorem then removes the core's central layer;
the established G.2.3 collapse recognizes the original L as an L₂(2ⁿ)-block
if its full point-normalizer span is nonabelian. No block or module marking
is assumed. Solvability refers to the exact residual quotient-action kernel.

The final parity owner qt-d-1222-linear-field-parity retains source
5.1.16(2), block exclusion, full residual-normalizer TI and Seed discharge.
Source: Aschbacher–Smith 5.1.17, pp.640–641, used in 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

theorem rankOne_odd_linear_core_eq_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n) :
    L.pCoreIn 2 = ⁅L.pCoreIn 2,L⁆ :=
  odd_linear_core_eq_commutator
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hodd

theorem rankOne_odd_nonabelian_block_of_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L V).U) :
    L.pCoreIn 2 = V ∧ ChapterC.IsL2EvenBlock L n := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_nonabelian_block_of_solvable hi hH c hodd hm hnf hlinear hsolv F hnat hnon
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
