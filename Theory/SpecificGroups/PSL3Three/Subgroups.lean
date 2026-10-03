module

public import Theory.SpecificGroups.PSL3Three.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Concrete subgroups for the PSL₃(3) maximal-subgroup problem

We fix the stabilizers of the first coordinate line and the last two
coordinate plane, the monomial subgroup, and the normalizer of a cyclic
subgroup of order thirteen. All four are actual subgroups of the matrix group,
with specified images in PSL₃(3). This module constructs the candidates; it
does not assert that the list of maximal subgroups is complete.

The cyclic subgroup uses the companion matrix of `X³ - X - 1` over `ZMod 3`.
Its determinant and thirteenth power are checked by kernel reduction, and
primality of thirteen gives its exact order. The geometric stabilizers use
the natural action on sets of vectors, so they stabilize subspaces setwise,
not pointwise.

Source: the subgroup constructions in GLS, volume 3, Theorem 6.5.3(a–c),
in `refs/KGroup/GLS3/chapter6.tex`. We use these as concrete inputs to the
maximal-subgroup route in `docs/thompson-minimal-simple-roadmap.md`, M8;
the source theorem's abstract isomorphism alternatives are not used as a
substitute for an inclusion or completeness proof.
-/

namespace Matrix.PSL3Three

open scoped Pointwise

/-- The stabilizer of the first coordinate line in SL₃(3). -/
@[expose] public def lineStabilizerSL : Subgroup SL :=
  MulAction.stabilizer SL {v : Fin 3 → ZMod 3 | v 1 = 0 ∧ v 2 = 0}

/-- The stabilizer of the last two coordinate plane in SL₃(3). -/
@[expose] public def planeStabilizerSL : Subgroup SL :=
  MulAction.stabilizer SL {v : Fin 3 → ZMod 3 | v 0 = 0}

/-- The determinant-one subgroup preserving the six signed coordinate vectors.
Over `ZMod 3`, the equation below says exactly that one coordinate is nonzero. -/
@[expose] public def monomialSL : Subgroup SL :=
  MulAction.stabilizer SL
    {v : Fin 3 → ZMod 3 | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1}

/-- The vectors stabilized setwise by `monomialSL` are exactly the nonzero
vectors supported on one coordinate. -/
public theorem norm_one_iff_single_support :
    ∀ v : Fin 3 → ZMod 3, v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 ↔
      ∃ i : Fin 3, v i ≠ 0 ∧ ∀ j : Fin 3, j ≠ i → v j = 0 := by
  decide

/-- A companion matrix generating a Singer subgroup of SL₃(3). -/
@[expose] public def singerGenerator : SL :=
  ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by decide⟩

public theorem singerGenerator_pow_thirteen : singerGenerator ^ 13 = 1 := by
  decide

public theorem singerGenerator_ne_one : singerGenerator ≠ 1 := by
  decide

public theorem orderOf_singerGenerator : orderOf singerGenerator = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact orderOf_eq_prime singerGenerator_pow_thirteen singerGenerator_ne_one

/-- The cyclic Singer subgroup in the determinant-one matrix model. -/
@[expose] public def singerSubgroupSL : Subgroup SL :=
  Subgroup.zpowers singerGenerator

public theorem card_singerSubgroupSL : Nat.card singerSubgroupSL = 13 := by
  rw [singerSubgroupSL, Nat.card_zpowers, orderOf_singerGenerator]

/-- The normalizer of the specified Singer subgroup in SL₃(3). -/
@[expose] public def singerNormalizerSL : Subgroup SL :=
  Subgroup.normalizer (singerSubgroupSL : Set SL)

/-- The first coordinate line stabilizer in PSL₃(3). -/
@[expose] public def lineStabilizer : Subgroup PSL :=
  lineStabilizerSL.map project

/-- The last two coordinate plane stabilizer in PSL₃(3). -/
@[expose] public def planeStabilizer : Subgroup PSL :=
  planeStabilizerSL.map project

/-- The monomial subgroup in PSL₃(3). -/
@[expose] public def monomial : Subgroup PSL :=
  monomialSL.map project

/-- The image of the Singer normalizer in PSL₃(3). -/
@[expose] public def singerNormalizer : Subgroup PSL :=
  singerNormalizerSL.map project

end Matrix.PSL3Three
