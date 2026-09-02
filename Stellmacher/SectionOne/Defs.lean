module

public import Stellmacher.FinalTheorem
public import FeitThompson.Extraspecial

/-!
# Stellmacher, Section 1: common definitions

This module contains the action terminology and standing notation used by the
numbered results in Section 1.  The three introductory results are kept in
separate modules (`LemmaOneOne`, `LemmaOneTwo`, and `LemmaOneThree`); this
file is their shared interface.

The scan on journal page 14 reads `W = O_{2'}(G)`.  The transcription at
`refs/latex/stellmacher-n-group.tex` line 249 lost the prime; accordingly
`oddCore G` is `pPrimeCore 2 G`.  The distinct standing hypothesis at line
243 remains `O₂(G) = 1`.
-/

universe u v

namespace Stellmacher

/-- The action of `Y` on `V` is quadratic when `[V,Y,Y]=1`.

Source: `refs/latex/stellmacher-n-group.tex`, lines 233--236. -/
@[expose] public def IsQuadraticAction
    (Y : Type u) (V : Type v) [Group Y] [Group V]
    [MulDistribMulAction Y V] : Prop :=
  commutatorAction₂ Y V = ⊥

/-- The element `t` induces a transvection on the finite module `V` when
`|V/C_V(t)| = 2`.

Source: `refs/latex/stellmacher-n-group.tex`, lines 235--237. -/
@[expose] public def InducesTransvection
    {Y : Type u} (V : Type v) [Group Y] [Group V] [Finite V]
    [MulDistribMulAction Y V] (t : Y) : Prop :=
  Nat.card V = 2 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V)

/-- The group `Y` induces transvections on `V` when its action is nontrivial
and every element outside `C_Y(V)` induces one.

Source: `refs/latex/stellmacher-n-group.tex`, lines 236--238. -/
@[expose] public def InducesTransvections
    (Y : Type u) (V : Type v) [Group Y] [Group V] [Finite V]
    [MulDistribMulAction Y V] : Prop :=
  commutatorAction Y V ≠ ⊥ ∧
    ∀ t : Y, t ∉ fixingSubgroup Y (Set.univ : Set V) →
      InducesTransvection V t

namespace SectionOne

/-- The standing hypotheses of Section 1: `G` is finite, solvable, and of
even order; `V` is a finite multiplicative `GF(2)` module; the action is
faithful; and `O₂(G)=1`.

Finiteness, the elementary abelian structure on `V`, and the action are
typeclass parameters of this predicate.

Source: `refs/latex/stellmacher-n-group.tex`, lines 240--244. -/
public structure Hypotheses
    (G : Type u) (V : Type v) [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V] : Prop where
  G_solvable : Group.IsSolvable G
  G_even : Even (Nat.card G)
  action_faithful : fixingSubgroup G (Set.univ : Set V) = ⊥
  twoCore_eq_bot : pCore 2 G = ⊥

/-- The corrected Section 1 notation `W = O_{2'}(G)`.

Source: `refs/files/stellmacher-n-group.pdf`, journal page 14. -/
@[expose] public def oddCore (G : Type u) [Group G] : Subgroup G :=
  pPrimeCore 2 G

end SectionOne
end Stellmacher
