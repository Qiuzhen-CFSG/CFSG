module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.Geometry

/-!+# Contracts for the remaining irreducible subgroup argument

The local case is detected by an actual nonidentity abelian normal subgroup.
The complementary case asks for a self-centralizing nonabelian simple normal
subgroup, with a multiplicative equivalence to one of the concrete models.
`CoreModel` does not assert that these models exhaust the possibilities.
Recognition and solvability of the outer quotient remain to be proved.
The parameter bounds are established separately in the descent modules.

Source: GLS3, Theorem 6.5.3(b–i), `refs/KGroup/GLS3/chapter6.tex`.
The source's shortened recognition proof uses the K-group hypothesis. The
intrinsic characteristic-two recognition required here must be proved
independently of that hypothesis.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open CFSG.KnownSimple

/-- A nonidentity abelian subgroup normal in the group under consideration. -/
@[expose] public def HasAbelianNormal (H : Type) [Group H] : Prop :=
  ∃ N : Subgroup H, N.Normal ∧ N ≠ ⊥ ∧ IsMulCommutative N

/-- Actual possible simple-core models. Degree-three exponents are positive;
their strict bounds are a separate conclusion to be proved from the embedding. -/
public inductive CoreModel (S : Type) [Group S] : Prop where
  | linearTwo (q : ℕ) (hS : ClassicalGroup.IsPSL S 2 q)
  | binaryThree (hS : ClassicalGroup.IsPSL S 3 2)
  | alternatingSix (e : Nonempty (S ≃* alternatingGroup (Fin 6)))
  | linear (m : ℕ) (hm : 0 < m) (hS : ClassicalGroup.IsPSL S 3 (2 ^ m))
  | unitary (m : ℕ) (hm : 0 < m) (hS : ClassicalGroup.IsPSU S 3 (2 ^ m))

/-- The core lies in the actual subgroup, with normality relative to that
subgroup. Trivial centralizer supplies faithfulness of its conjugation action. -/
@[expose] public def HasRecognizedCore (H : Type) [Group H] : Prop :=
  ∃ N : Subgroup H, N.Normal ∧ IsSimpleGroup N ∧ ¬ Group.IsSolvable N ∧
    Subgroup.centralizer (N : Set H) = ⊥ ∧ CoreModel N

end CFSG.Quasithin.MainConverse.LinearThreeSections
