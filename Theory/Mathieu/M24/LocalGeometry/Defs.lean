module

public import Theory.Mathieu.M24.Basic

/-!
# Octad and sextet local subgroups of the concrete M24

An octad is a block of the certified Witt design. A sextet is a partition of
the 24 points into six tetrads, every two of which have an octad as their union.
Their stabilizers are subgroups of `Sporadic.Mathieu.M24` itself. These
definitions therefore require no comparison with a different Golay-code model.

Source: GLS, volume 3, Table 5.3e, and its cited Mathieu geometry. The local
structure and generation assertions are separate mathematical obligations;
they are not fields of these geometric objects.
-/

@[expose] public section

namespace Sporadic.Mathieu.M24LocalGeometry

open scoped Pointwise

/-- An octad in the fixed W24 design. -/
abbrev Octad := {O : Finset (Fin 24) // O ∈ m24Blocks}

/-- A sextet of the fixed W24 design, with the literal partition retained. -/
structure Sextet where
  parts : Finset (Finset (Fin 24))
  card : parts.card = 6
  tetrad : ∀ A ∈ parts, A.card = 4
  disjoint : ∀ A ∈ parts, ∀ B ∈ parts, A ≠ B → Disjoint A B
  cover : parts.biUnion id = Finset.univ
  octad : ∀ A ∈ parts, ∀ B ∈ parts, A ≠ B → A ∪ B ∈ m24Blocks

/-- The setwise stabilizer of an actual octad. -/
noncomputable def octadStabilizer (O : Octad) : Subgroup M24 :=
  MulAction.stabilizer M24 O.val

/-- The setwise stabilizer of an actual sextet, allowing permutation of its parts. -/
noncomputable def sextetStabilizer (X : Sextet) : Subgroup M24 :=
  MulAction.stabilizer M24 X.parts

/-- Membership in the two specified geometric families means equality with
an actual stabilizer, not an abstract group-family label. -/
def IsGeometryLocal (P : Subgroup M24) : Prop :=
  (∃ O : Octad, P = octadStabilizer O) ∨
    (∃ X : Sextet, P = sextetStabilizer X)

end Sporadic.Mathieu.M24LocalGeometry

end
