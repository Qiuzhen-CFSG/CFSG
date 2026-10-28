module

public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.Intrinsic
public import Theory.GroupTheory.GraphUniquenessSystem.CosetConstruction

/-!
# The type-J₄ coset construction and its intrinsic local subgroup

The specified vertices are left cosets G/M, with base vertex M and the
second vertex tM. The plane subgroup is literally C_G(z); `local_eq_normalizer`
also identifies it with the normalizer of the ambient extraspecial core.
The marked cubic kernel and both of its quotient maps remain available in
`CubicLift`.

`systemOfLocalSubgroups` is a conditional construction, not source (5.1).
It proves the graph, transitivity, stabilizer and two local generation
claims from explicit algebraic hypotheses. Existence of the source M, the
line subgroup, their module structures, and the algebraic hypotheses must
still be proved from `IsTypeJ4`. No such existence is assumed in the
intrinsic core and cubic-extension theorems.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), 589–607; exposition
*The study of J₄ via the theory of uniqueness systems*, (3.1), (3.2),
(5.1), pp.16–20. The remaining subgroup producer must retain the Todd
module, the actual line subgroup and all their intersections.
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry

open Subgroup GraphUniquenessSystem

variable {G : Type*} [Group G]

/-- Points of the source geometry, after its point subgroup has been constructed. -/
abbrev Vertex (M : Subgroup G) := Cosets.Vertex M

variable (z : G) (M : Subgroup G) (t : G)
variable (htH : t ∈ centralizer z) (htM : t ∉ M) (ht2 : t * t ∈ M)
variable (hfaithful : M.normalCore = ⊥) (hgenerate : centralizer z ⊔ M = ⊤)
variable (hvertex : IsCoatom ((centralizer z).subgroupOf M))
variable (hlocal : IsCoatom (M.subgroupOf (centralizer z)))
variable (hedge : ¬ M ⊓ M.comap (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer z)

/-- Application to the literal centralizer. All additional local subgroup
hypotheses are displayed; constructing them from type-J₄ is still required. -/
def systemOfLocalSubgroups : System G (Vertex M) :=
  Cosets.system M t (centralizer z) htH htM ht2 hfaithful hgenerate hvertex hlocal hedge

local notation "U" =>
  systemOfLocalSubgroups z M t htH htM ht2 hfaithful hgenerate hvertex hlocal hedge

/-- The local group is the original ambient involution centralizer. -/
@[simp] theorem local_eq : (U).H = centralizer z := rfl

/-- The point stabilizer is the supplied subgroup, with equality in G. -/
@[simp] theorem vertexGroup_eq : (U).vertexGroup = M := Cosets.stabilizer_base M

/-- The edge fixer uses the left-action conjugation convention. -/
theorem edgeGroup_eq :
    (U).edgeGroup = M ⊓ M.comap (MulAut.conj t⁻¹).toMonoidHom := Cosets.edgeFixer_eq M t

/-- Identification with the literal coset collinearity graph once the source
line action has been supplied. -/
theorem graph_adj_iff_collinear (P : Subgroup G) (htP : t ∈ P)
    (hP : Cosets.LineTransitive M t P) (a b : Vertex M) :
    (U).graph.Adj a b ↔ Cosets.Collinear M P a b :=
  Cosets.adj_iff_collinear M t P htM htP hP a b

/-- Actual application of the intrinsic core-normalizer theorem to the local
subgroup of this coset construction. -/
theorem local_eq_normalizer [Finite G] (h : IsTypeJ4 z) :
    (U).H = normalizer (ambientCore z : Set G) := (normalizer_ambientCore h).symm

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry
