module

public import Theory.PrimeRank
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.IsPerfect

/-!
# Independent inputs to the remaining rank-action branches

The residual-action argument uses a two-dimensional representation of each
small-rank odd p-group's automorphism group with p-group kernel. The perfect
action argument additionally uses the absence of nontrivial perfect central
extensions of SL₂(p), for prime p > 3. These are explicit mathematical
contracts, not assertions that either input has been established here.

The automorphism-quotient branch owns the first input; the second must be
discharged from the genuine Chapter I universal-cover result in final
assembly. They allow the action arguments to be proved independently.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.25(2), A.1.26 and A.1.29, printed pp.25–27; I.1.3, printed p.407.
-/

namespace CFSG.Quasithin.ChapterA.RankActions

universe u

/-- The actual linear representation needed by the residual-action argument.
Its kernel condition is a p-group assertion, not a faithfulness assumption. -/
@[expose] public def SmallRankAutomorphismRepresentation : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Odd p →
    ∀ (P : Type u) [Group P] [Finite P], IsPGroup p P → primeRank p P ≤ 2 →
      ∃ f : MulAut P →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p),
        IsPGroup p f.ker

/-- The precise multiplier consequence needed for the quasisimple quotient
clause: every finite perfect central cover of prime-field SL₂(p), p > 3,
is an isomorphism. This contract does not concern any particular local action. -/
@[expose] public def PrimeSL2CoverRigidity : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E]
      (f : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)),
      Function.Surjective f → f.ker ≤ Subgroup.center E → Function.Injective f

end CFSG.Quasithin.ChapterA.RankActions
