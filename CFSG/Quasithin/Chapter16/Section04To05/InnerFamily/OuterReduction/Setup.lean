module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Cases
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Elementary
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.EmptyCase
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Selection
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic
public import Theory.Mathieu.M22.Basic

/-!
# Interfaces for the outer-action reduction in 16.4.9

The commuting-Sylow dichotomy retains the actual quotient by O₂(L) and
excludes actual isomorphisms with PSL₃(4) and M₂₂ in its second branch.
A residual fusion witness is an element of O²(C_L(r)), together with an
L-conjugator carrying r to its product with that element. Such a witness
contradicts (!) once 16.4.8 places the residual in L′.

These definitions specify intermediate targets, not additional standing
hypotheses or proofs of their existence. Their construction belongs to the
separate local-geometry and model arguments.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed pp.1190–1191.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction

open Subgroup
variable {G : Type*} [Group G]

/-- The dichotomy preceding (!) on printed p.1190. -/
def CommutingSylowDichotomy (T : Sylow 2 G) (z : G) (L : Subgroup G) : Prop :=
  commutingSylow T L = zpowers z ∨
    z ∈ L ∧
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL) ∧
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22)

/-- A concrete witness forbidden by (!) under the empty-family assumption. -/
def ResidualFusionWitness (L : Subgroup G) (r : G) : Prop :=
  ∃ l ∈ L, ∃ v ∈ OuterResidual.involutionResidual L r,
    v ≠ 1 ∧ MulAut.conj l r = r * v

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction
