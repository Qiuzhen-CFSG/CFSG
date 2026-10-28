module

public import CFSG.Quasithin.ClassicalModels

/-!
# The special and projective alternatives in G.7.2(3)

The notation `(S)L₃^ε(p)` on printed pp.347--348 of Aschbacher--Smith
includes the special and projective groups, for either sign. These
predicates use actual matrix-group equivalences. In the unitary case `p`
is the fixed-field order, so the coefficient field has order `p²`.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section07.OddCharacteristic

open scoped MatrixGroups

/-- The special linear alternative, before quotienting its center. -/
def IsSLThree (G : Type*) [Group G] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* SL(3, F))

/-- The special unitary alternative with the source fixed-field convention. -/
def IsSUThree (G : Type*) [Group G] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F),
    Nat.card F = q ^ 2 ∧ (∀ x, J.conj x = x ^ q) ∧
      Nonempty (G ≃* J.specialSubgroup)

/-- All four actual model alternatives denoted by `(S)L₃^ε(p)`. -/
def IsLinearUnitaryThree (G : Type*) [Group G] (q : ℕ) : Prop :=
  ClassicalGroup.IsPSL G 3 q ∨ IsSLThree G q ∨
    ClassicalGroup.IsPSU G 3 q ∨ IsSUThree G q

end CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
