module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.PGroupCore

/-!
# Local inputs for the symplectic elementary two-core rank gap

Two independent calculations suffice: a maximum elementary subgroup of the
plane local either lies in the symmetric-matrix radical or has at least q
elements in the actual SL₂ image; and a subgroup of SL₂ with nontrivial
two-core contains all of its two-subgroups in that core.

These are explicit proof obligations, not instances or asserted model facts.
The assembly uses the literal plane quotient and intrinsic two-cores.

Source application: Aschbacher--Smith, E.1.14(1), printed p.214, citing
Aschbacher [Asc82a], Lemma 4.7; the local matrices underlie F.1.12(I)(2).
-/

@[expose] public section

namespace Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap

variable (F : Type*) [Field F]

/-- The geometric image bound in the actual determinant-one plane local. -/
def PlaneImageBound : Prop :=
  ∀ A : Subgroup (planeLocal (F := F)), IsElementaryAbelian 2 A →
    Nat.card A = Nat.card F ^ 3 →
    A ≤ Plane.radical ∨ Nat.card F ≤ Nat.card (A.map Plane.quotientMap)

/-- Rank-one core control for every subgroup of the actual SL₂ matrix group. -/
def RankOneCoreControl : Prop :=
  ∀ R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), pCore 2 R ≠ ⊥ →
    ∀ B : Subgroup R, IsPGroup 2 B → B ≤ pCore 2 R

end Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap
