module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Contracts

/-!
# Local orbit and product inputs for the involution census

Write `H = C_G(z)`, `Q = coreInG z`, and `F = fusionCore z`. The source
separates the twelve involutions of `Q` outside `F` from the single orbit of
involutions of `H` outside `Q`. For a fixed involution `t` of the first kind,
the product calculation counts four elements of `F - {1,z}` and sixteen
outside-core involutions whose product with `t` generates a group containing
`z`. These are explicit intermediate conclusions, not source hypotheses.

The assembly in `Census` uses the selected ambient fusion of `u` and identifies
these cyclic-membership conditions with the actual half-order fiber.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.3, 2.7 and the count in the proof of 4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census

open Subgroup

variable {G : Type*} [Group G]

/-- The literal long-orbit set; fusion-eight data identify its ambient class. -/
public abbrev CoreSecond (z : G) :=
  {x : G // x ∈ coreInG z ∧ orderOf x = 2 ∧ x ∉ fusionCore z}

/-- The four qualifying elements of the short core orbit, using the source's
cyclic-subgroup condition rather than assuming a half-order count. -/
public abbrev CoreProducts (z t : G) :=
  {x : G // x ∈ fusionCore z ∧ x ≠ 1 ∧ x ≠ z ∧ z ∈ zpowers (x * t)}

/-- The sixteen qualifying outside-core involutions, before using their
ambient fusion to the distinguished involution. -/
public abbrev OutsideProducts (z t : G) :=
  {x : G // x ∈ Centralizer z ∧ x ∉ coreInG z ∧ orderOf x = 2 ∧
    z ∈ zpowers (x * t)}

/-- Local conjugacy and the size of the long orbit. No ambient class coverage
or mixed-pair count is included in this contract. -/
public structure OrbitData (z u : G) : Prop where
  core_card : Nat.card (CoreSecond z) = 12
  core_transitive : ∀ x y : CoreSecond z,
    ∃ c : Centralizer z, MulAut.conj (c : G) (x : G) = (y : G)
  outside_transitive : ∀ x : G, x ∈ Centralizer z → x ∉ coreInG z →
    orderOf x = 2 → ∃ c : Centralizer z, MulAut.conj (c : G) u = x

/-- The two separate product calculations of 4.3; their producer must prove
the product assertions and these counts from the local action. -/
public structure ProductData (z t : G) : Prop where
  core_products : Nat.card (CoreProducts z t) = 4
  outside_products : Nat.card (OutsideProducts z t) = 16

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
