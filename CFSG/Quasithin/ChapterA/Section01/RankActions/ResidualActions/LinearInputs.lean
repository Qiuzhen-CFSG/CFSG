module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.Inputs
public import Theory.GroupTheory.PResidual.PrimeSet
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The two linear normalizer calculations in A.1.26

These explicit universal contracts isolate the calculations in GL₂(p) from
the reduction using automorphisms of odd p-cores. They are not asserted here.
The first says that a two-perfect group normalizing an elementary abelian
two-subgroup centralizes it. The second uses the actual {2,3}-residual and
allows an arbitrary two-subgroup.

Source: Aschbacher–Smith, A.1.26, printed pp.25–26.
-/

namespace CFSG.Quasithin.ChapterA.RankActions

/-- The elementary abelian normalizer calculation needed in A.1.26(1). -/
@[expose] public def ElementaryTwoLinearNormalizer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Odd p →
    ∀ X V : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
      IsPPerfect 2 X → IsElementaryAbelian 2 V →
      X ≤ Subgroup.normalizer (V : Set _) → ⁅V, X⁆ = ⊥

/-- The arbitrary two-subgroup normalizer calculation needed in A.1.26(2). -/
@[expose] public def TwoLinearNormalizer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Odd p →
    ∀ X V : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
      IsPiPerfect twoThreePrimes X → IsPGroup 2 V →
      X ≤ Subgroup.normalizer (V : Set _) → ⁅V, X⁆ = ⊥

end CFSG.Quasithin.ChapterA.RankActions
