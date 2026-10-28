module
public import Theory.SpecificGroups.HeisenbergPrime.CyclicOuterExclusion
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.PSL2.OuterSolvable.BinaryCyclic
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage

/-!
# Binary SL₂ has no faithful ternary Heisenberg automorphisms

Odd Sylows in binary SL₂ are cyclic. The actual semilinear automorphism
coverage makes its outer quotient cyclic as well. Applying the cyclic-kernel
obstruction to a putative Heisenberg action gives a contradiction, uniformly
in the binary field degree, including the prime field.

Source: the rank-one C.2.7 row in Aschbacher–Smith 14.7.26, printed p.1053;
the automorphism coverage is GLS3 2.5.12, as cited in the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SL2
/-- No binary rank-one model admits the faithful original Heisenberg action. -/
theorem no_heisenberg_automorphism_action
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (f : HeisenbergPrime 3 →* MulAut SL(2,F)) (hf : Function.Injective f) : False := by
  let e := BenderSuzuki.ZD.Linear.sl2QuotientEquiv F
  let : IsCyclic (MulAut.Outer (Theory.PSL2.Group F)) :=
    Theory.PSL2.OuterSolvable.outer_isCyclic_of_field_coverage
      BenderSuzuki.ZD.Linear.semilinear_coverage
  let : IsCyclic (MulAut.Outer SL(2,F)) := (MulAut.outerCongr e).isCyclic.mpr inferInstance
  have ho : primeRank 3 (MulAut.Outer SL(2,F)) ≤ 1 :=
    (default : Sylow 3 (MulAut.Outer SL(2,F))).primeRank_le_one_of_isCyclic inferInstance
  exact HeisenbergPrime.no_faithful_action_of_rank_one BenderSuzuki.Converse.center_SL2_eq_bot
    (binary_odd_primeRank_le_one (by decide : Odd 3)) ho f hf
end Matrix.SL2
