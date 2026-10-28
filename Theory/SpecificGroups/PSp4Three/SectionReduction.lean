module

public import Theory.SpecificGroups.PSp4Three.MatrixModel
public import Theory.GroupTheory.SimpleSectionSolvableLayers
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.ZMod.Basic

/-!
# Proper-subgroup interfaces for PSp₄(3)

Reducibility is tested on the actual four-dimensional representation of the
full inverse image in Sp₄(3). It means preservation of a nonzero proper
linear subspace; scalar matrices act on this space, so this is deliberately
not an action of the projective quotient on vectors.

The irreducible branch asks for solvable normal layers around a subgroup
of A₆. This accommodates both 2⁴:A₅ and S₆ using actual quotient maps.
Neither the reducible solvability theorem nor exhaustive irreducible
coverage is asserted here. They are independent intrinsic proof obligations.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`. The candidate maximal-subgroup
shapes are recorded at https://brauer.maths.qmul.ac.uk/Atlas/clas/U42/;
that table is a guide for proving coverage, not an assumed theorem.
-/

namespace Matrix.PSp4Three

/-- A proper nonzero subspace preserved by every lift of a projective subgroup. -/
@[expose] public def HasInvariantSubspace (U : Subgroup (PSp 2 (ZMod 3))) : Prop :=
  ∃ W : Submodule (ZMod 3) (Vector 2 (ZMod 3)), W ≠ ⊥ ∧ W ≠ ⊤ ∧
    ∀ (g : Sp 2 (ZMod 3)), projection g ∈ U →
      ∀ v ∈ W, g • v ∈ W

/-- Two solvable normal layers around a faithful subgroup of the actual A₆. -/
@[expose] public def HasAlternatingLayers (H : Type*) [Group H] : Prop :=
  Group.IsSolvable H ∨
    Theory.GroupTheory.SolvableLayersEmbedding H (alternatingGroup (Fin 6))

end Matrix.PSp4Three
