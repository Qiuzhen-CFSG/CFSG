module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Defs

/-!
# The earlier intersection premise for AS91 involution fusion

The hypothesis of (6.2) is retained: distinct conjugates of E have a pure
marker-class intersection only when that intersection already contains a
conjugate of z. No fusion, centralizer or generation conclusion is assumed.
All groups and maps are those of the original marked `LocalData`.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.2)(3), pp.601–602.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open Subgroup SourceIncidence
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- Source (6.2)(3), including the standing existential hypothesis of (6.2). -/
def MarkerIntersection (a : LocalData h) : Prop :=
  ∀ g : G, a.P.E.map (MulAut.conj g).toMonoidHom ≠ a.P.E →
    (∃ w ∈ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom, IsConj z w) →
    ∀ u ∈ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom, u ≠ 1 → IsConj z u

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
