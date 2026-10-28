module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Alternatives
public import Theory.GroupTheory.DihedralRotationQuotient


/-!
# Markings shared by the cover reduction and its model inputs

A projective marking identifies the literal quotient `L/O₂(L)` with one
projective matrix group. Diagonal, graph, and field actions are all required to
use that same equivalence and to lift actual conjugation on L. The graph and
field conditions allow the inner-diagonal factor in their matrix descriptions;
the field factor is specifically the square Frobenius, as required over F₄.

`SylowThreeLift` is an OUTPUT contract for the Frattini and normalizer argument.
Its section is tied to the actual normalizer of a Sylow three-subgroup of Y,
and its reflections carry the marked model actions. No theorem here constructs
that output from the source hypotheses. In particular the definitions are not
substitutes for the cover reduction or 15.3.38.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed p.1136.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction
variable {G : Type*} [Group G]

/-- A literal projective matrix quotient, retaining its coefficient field. -/
structure ProjectiveMarking (L : Subgroup G) (q : ℕ) where
  F : Type
  [field : Field F]
  [finite : Finite F]
  card : Nat.card F = q
  equivalence : (L ⧸ pCore 2 L) ≃* PSL(3,F)

attribute [instance] ProjectiveMarking.field ProjectiveMarking.finite

namespace ProjectiveMarking
variable {L : Subgroup G} {q : ℕ} (c : ProjectiveMarking L q)

/-- The displayed matrix automorphism is transported from conjugation by a. -/
def Realizes (a : G) (α : MulAut PSL(3,c.F)) : Prop :=
  ∃ β : MulAut L, Candidates.ConjugationOn L a β ∧
    ∀ x : L, c.equivalence (QuotientGroup.mk' (pCore 2 L) (β x)) =
      α (c.equivalence (QuotientGroup.mk' (pCore 2 L) x))

/-- An order-three actor with a genuinely outer diagonal matrix action. -/
def Diagonal (y : G) : Prop :=
  orderOf y = 3 ∧ ∃ a : Matrix.GeneralLinearGroup (Fin 3) c.F,
    Matrix.PSL3.OuterSolvable.linearConj c.F a ∉ MulAut.innerSubgroup PSL(3,c.F) ∧
      c.Realizes y (Matrix.PSL3.OuterSolvable.linearConj c.F a)

/-- The graph coset, with its actual inverse-transpose action. -/
def Graph (τ : G) : Prop :=
  ∃ a : Matrix.GeneralLinearGroup (Fin 3) c.F,
    c.Realizes τ (Matrix.PSL3.OuterSolvable.linearConj c.F a *
      Matrix.PSL3.OuterSolvable.graph c.F)

/-- The field coset, with its actual square-Frobenius action. -/
def Field (f : G) : Prop :=
  ∃ (σ : c.F ≃+* c.F) (a : Matrix.GeneralLinearGroup (Fin 3) c.F),
    (∀ x : c.F, σ x = x ^ 2) ∧
      c.Realizes f (Matrix.PSL3.OuterSolvable.linearConj c.F a *
        Matrix.PSL3.OuterSolvable.fieldAction c.F σ)

end ProjectiveMarking

/-- The Sylow-three normalizer and its marked dihedral complement. This is
a conclusion to be constructed, not a standing source hypothesis. -/
structure SylowThreeLift (T : Sylow 2 G) (Y S L : Subgroup G)
    (c : ProjectiveMarking L 4) where
  X : Sylow 3 Y
  dihedral : DihedralGroup.SplitSection (L.subgroupOf (T : Subgroup G))
  normalizer_YS : Nonempty ((((Y ⊔ S : Subgroup G) ⊓
    normalizer (((X : Subgroup Y).map Y.subtype) : Set G) : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
  normalizer_T : dihedral.sectionMap.range.map (T : Subgroup G).subtype =
    (T : Subgroup G) ⊓ normalizer (((X : Subgroup Y).map Y.subtype) : Set G)
  first_mem : (dihedral.firstReflection : G) ∈ S
  halfTurn_mem : (dihedral.halfTurn : G) ∈ S
  second_not_mem : (dihedral.secondReflection : G) ∉ S
  graph : c.Graph (dihedral.firstReflection : G)
  field : c.Field (dihedral.halfTurn : G)
  inverts : ∀ x : X, (MulAut.conj (dihedral.halfTurn : G)) ((x : Y) : G) =
    (((x : Y) : G))⁻¹

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction
