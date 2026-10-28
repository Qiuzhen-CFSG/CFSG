module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Fin.Basic

/-!
# Relations for Held's eight generators

This is the explicit relation family on printed p.239 of D. Held,
"A Characterization of some multiply transitive permutation groups, I",
Illinois J. Math. 13 (1969), 224--240, DOI 10.1215/ijm/1256053756,
Lemma 5.11. Indices here are zero-based: the first generator has cube one,
the other seven have square one, adjacent products have cube one, and
products separated by at least one index have square one.

The relation family has the trivial realization. To obtain an A10 embedding
one must also construct a nontrivial marked word. Held's word for the
original central involution is `M 1 * M 3 * M 5` (his `M₂ M₄ M₆`).
Neither existence of the generators nor that marking is assumed to follow
from the ambient centralizer data in this module.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction

/-- The relations in Held 5.11, with all index ranges made explicit. -/
public structure DicksonRelations {G : Type*} [Group G] (M : Fin 8 → G) : Prop where
  /-- Held's `M₁³ = 1`. -/
  root_cube : M 0 ^ 3 = 1
  /-- Held's `M₂² = ⋯ = M₈² = 1`. -/
  tail_square : ∀ i : Fin 8, i ≠ 0 → M i ^ 2 = 1
  /-- All seven adjacent products have cube one. -/
  adjacent_cube : ∀ i : Fin 7, (M i.castSucc * M i.succ) ^ 3 = 1
  /-- The nonadjacent product relation also includes the first generator. -/
  distant_square : ∀ i j : Fin 8, i.val + 1 < j.val → (M i * M j) ^ 2 = 1

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction
