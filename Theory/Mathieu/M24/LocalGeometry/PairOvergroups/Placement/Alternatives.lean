module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Trio
public import Theory.Mathieu.M24.LocalGeometry.LinearFourPlacement.Orbits
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Two intrinsic inputs for the M₂₄ pair-placement alternative

An intransitive Sylow overgroup fixes an actual octad, by the checked orbit
calculation in `LinearFourPlacement.Orbits`. Thus placing a small Sylow
overgroup in an octad or a translated standard trio only requires a theorem
about the transitive case. Both possible orders, 9,216 and 27,648, are retained.

The octad branch has a separate eight-point action problem: a permuting
elementary nine and Sylow two-subgroup in A₈ must have a line invariant under
their common inner normalizer. The conjugators belong to A₈ itself, not to
the larger symmetric group. These two inputs are unproved contracts here;
the conditional geometry lemma proves only the reduction to the first one.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528); Aschbacher, *Sporadic Groups*, Chapter 7, §20; GLS3, Table 5.3e.
The octad, sextet and trio families in that table do not by themselves prove
exhaustive coverage. The transitive contract still requires that coverage,
including possible pairs in sextet stabilizers.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement

/-- The transitive small-overgroup obligation, on the fixed Witt-design carrier.
It concerns containment in the stabilizer of a literal translated partition. -/
def TransitiveSmallSylowPlacement : Prop :=
  ∀ (S : Sylow 2 M24) (H : Subgroup M24), S.toSubgroup ≤ H →
    Group.IsSolvable H → (Nat.card H = 9216 ∨ Nat.card H = 27648) →
    MulAction.IsPretransitive H (Fin 24) →
    ∃ g : M24, H ≤ conjugateTrioStabilizer g

/-- The exact eight-point line calculation needed after restricting an octad
stabilizer to its octad. No extending automorphisms outside A₈ are included. -/
def EightPointPairLine : Prop :=
  ∀ (P : Sylow 2 (alternatingGroup (Fin 8))) (D : Subgroup (alternatingGroup (Fin 8))),
    IsElementaryAbelian 3 D → Nat.card D = 9 →
    (D : Set (alternatingGroup (Fin 8))) * (P : Set (alternatingGroup (Fin 8))) =
      (P : Set (alternatingGroup (Fin 8))) * (D : Set (alternatingGroup (Fin 8))) →
    ∃ C : Subgroup (alternatingGroup (Fin 8)), C ≤ D ∧ Nat.card C = 3 ∧
      ∀ g ∈ (P : Subgroup (alternatingGroup (Fin 8))) ⊓
        normalizer (D : Set (alternatingGroup (Fin 8))),
        ∀ x ∈ C, g * x * g⁻¹ ∈ C

/-- The checked intransitive case reduces full geometric coverage to the
transitive contract. The sextet cases remain part of that contract. -/
theorem small_sylow_overgroup_geometry (ht : TransitiveSmallSylowPlacement)
    (S : Sylow 2 M24) (H : Subgroup M24) (hSH : S.toSubgroup ≤ H)
    (hsolv : Group.IsSolvable H) (hcard : Nat.card H = 9216 ∨ Nat.card H = 27648) :
    (∃ O : Octad, H ≤ octadStabilizer O) ∨
      ∃ g : M24, H ≤ conjugateTrioStabilizer g := by
  by_cases htrans : MulAction.IsPretransitive H (Fin 24)
  · exact Or.inr (ht S H hSH hsolv hcard htrans)
  · exact Or.inl
      (LinearFourPlacement.intransitive_sylow_overgroup_le_octadStabilizer S H hSH htrans)

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement

end
