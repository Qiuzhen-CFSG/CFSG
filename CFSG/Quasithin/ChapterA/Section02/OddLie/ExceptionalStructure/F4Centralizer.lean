module

public import Theory.SpecificGroups.LieType.F4OddFundamentalCentralizer
public import Theory.SpecificGroups.SymplecticSix.ThreeRank

/-!
# The F₄ residual-centralizer source interface

Aschbacher--Smith A.2.17 (printed p.39) applies the bound
`m₃(J*) ≤ 1` to the prime-to-`p` residual of the centralizer of a proper
fundamental `SL₂`.  For the actual split carrier, the corresponding literal
candidate and residual are defined in
`Theory.SpecificGroups.LieType.F4OddFundamentalCentralizer`.

This source-facing lemma consumes an actual embedding of `Sp₆(F)` into that
literal residual.  The rank-one map, its properness, and the centralizer
identification remain to be constructed from the elementary adjoint matrix
group and its central quotient; this lemma deliberately does not package
those missing facts as assumptions hidden in a projection.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.F4Centralizer

open ExceptionalSplit
open Theory.AlgebraicGroup.StandardRootSystem

variable {F : Type*} [Field F] [Finite F]

/-- The source's `m₃(J*) ≤ 1` bound is contradicted by an actual `Sp₆(F)`
embedding into the literal F₄ residual centralizer. -/
public theorem source_bound_contradiction
    (p : ℕ) (i : typeF4RootPairing_base.support)
    (hbound : primeRank 3 (f4FundamentalResidual (F := F) p i) ≤ 1)
    (f : Matrix.symplecticGroup (Fin 3) F →*
      f4FundamentalResidual (F := F) p i)
    (hf : Function.Injective f) : False := by
  exact ExceptionalSplit.F4OddFundamentalCentralizer.no_three_rank_one_residual
    p i hbound f hf

end CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.F4Centralizer

end
