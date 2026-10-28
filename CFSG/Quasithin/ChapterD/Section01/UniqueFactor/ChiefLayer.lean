module

public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import Theory.GroupTheory.PResidual.Defs

/-!
# The chief-layer interface inside D.1.4

Put K = O²(G₂) and I = [U,K]. The unique noncentral chief factor implies
that every G₂-normal subgroup of U either centralizes K or contains I.
Together with [I,K] = I and U = IV, this is the source's use of the
irreducible quotient I/C_I(K) and the lifting observation (*).

This record specifies an intermediate theorem still to be proved from the
actual chief-series hypothesis. It is not a source assumption or a proof
of D.1.4. Its producer and the two subsequent implications can be developed
independently; the source assembly must construct it before using them.
Source: Aschbacher--Smith, D.1.4, printed pp.175--176, (*) and (**).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.UniqueFactor
open Subgroup
variable {G : Type*} [Group G]

/-- Exact intermediate group-theoretic content of the unique chief layer. -/
structure ChiefLayerGeometry (G₂ V : Subgroup G) : Prop where
  nontrivial : ⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆ ≠ ⊥
  idempotent :
    ⁅⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆,
      (pResidual 2 G₂).map G₂.subtype⁆ =
      ⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆
  generation : conjugateSpan G₂ V =
    ⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆ ⊔ V
  normal_subgroup_dichotomy : ∀ X : Subgroup G,
    X ≤ conjugateSpan G₂ V → G₂ ≤ normalizer (X : Set G) →
      ⁅X, (pResidual 2 G₂).map G₂.subtype⁆ = ⊥ ∨
      ⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆ ≤ X

end CFSG.Quasithin.ChapterD.UniqueFactor
