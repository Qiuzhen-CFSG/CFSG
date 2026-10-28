module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Finite word tables and their group realizations

A table describes 96 rows using two generators, positive words, and a binary
operation. A realization must compare that operation with actual group
multiplication. The table itself is not assumed to be a group. Its word
identities then prove that homomorphisms are determined by two generator
images, and its relators impose necessary conditions on those images.

This is the finite-certificate boundary for the binary G₂ derived amalgam
in Aschbacher--Smith F.1.12 and Definition F.4.3.
-/

@[expose] public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound

structure WordTable where
  mul : Fin 96 → Fin 96 → Fin 96
  word : Fin 96 → List Bool
  label : Fin 96 → Nat
  overlap : Fin 32 → Fin 96
  relations : List (List Bool)

def WordTable.eval (T : WordTable) (x y : Fin 96) : List Bool → Fin 96
  | [] => 0
  | b :: w => T.mul (if b then y else x) (T.eval x y w)

/-- Only directly checkable identities and inequalities, not a presentation claim. -/
structure WordTable.Valid (T : WordTable) : Prop where
  words : ∀ i, T.eval 1 2 (T.word i) = i
  relations : ∀ w ∈ T.relations, T.eval 1 2 w = 0
  fourth_ne : T.eval 1 2 [false, false, false, false] ≠ 0
  common : T.overlap 1 = 1

/-- A full coordinate comparison with an actual group. -/
structure WordTable.Realization (T : WordTable) (G : Type*) [Group G] where
  equiv : Fin 96 ≃ G
  one_eq : equiv 0 = 1
  mul_eq : ∀ i j, equiv (T.mul i j) = equiv i * equiv j

def groupWord {G : Type*} [Group G] (x y : G) : List Bool → G
  | [] => 1
  | b :: w => (if b then y else x) * groupWord x y w

theorem map_groupWord {G H : Type*} [Group G] [Group H] (f : G →* H)
    (x y : G) (w : List Bool) :
    f (groupWord x y w) = groupWord (f x) (f y) w := by
  induction w with
  | nil => exact f.map_one
  | cons b w ih => cases b <;> simp only [groupWord, Bool.false_eq_true,
      if_false, if_true, map_mul, ih]

theorem WordTable.Realization.eval_eq {T : WordTable} {G : Type*} [Group G]
    (E : T.Realization G) (x y : Fin 96) (w : List Bool) :
    E.equiv (T.eval x y w) = groupWord (E.equiv x) (E.equiv y) w := by
  induction w with
  | nil => exact E.one_eq
  | cons b w ih => cases b <;> simp only [WordTable.eval, groupWord,
      Bool.false_eq_true, if_false, if_true, E.mul_eq, ih]

theorem WordTable.Realization.word_eq {T : WordTable} {G : Type*} [Group G]
    (E : T.Realization G) (hT : T.Valid) (i : Fin 96) :
    groupWord (E.equiv 1) (E.equiv 2) (T.word i) = E.equiv i := by
  rw [← E.eval_eq, hT.words]

theorem WordTable.Realization.hom_ext {T : WordTable} {G H : Type*}
    [Group G] [Group H] (E : T.Realization G) (hT : T.Valid)
    (f g : G →* H) (h₁ : f (E.equiv 1) = g (E.equiv 1))
    (h₂ : f (E.equiv 2) = g (E.equiv 2)) : f = g := by
  ext x
  obtain ⟨i, rfl⟩ := E.equiv.surjective x
  rw [← E.word_eq hT i, map_groupWord, map_groupWord, h₁, h₂]

/-- Necessary local constraints for the images of the two marked generators. -/
def WordTable.LocalCandidate (T : WordTable) (x y : Fin 96) : Prop :=
  T.eval x y [false, false, false, false] ≠ 0 ∧ y ≠ 0 ∧
    (∀ w ∈ T.relations, T.eval x y w = 0) ∧
    ∀ i : Fin 32, ∃ j : Fin 32, T.eval x y (T.word (T.overlap i)) = T.overlap j

instance (T : WordTable) (x y : Fin 96) : Decidable (T.LocalCandidate x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∀ _i : Fin 32, ∃ _j : Fin 32, _))

theorem WordTable.Realization.aut_eval {T : WordTable} {G : Type*} [Group G]
    (E : T.Realization G) (a : G ≃* G) (x y : Fin 96)
    (hx : E.equiv x = a (E.equiv 1)) (hy : E.equiv y = a (E.equiv 2))
    (w : List Bool) :
    E.equiv (T.eval x y w) = a (E.equiv (T.eval 1 2 w)) := by
  rw [E.eval_eq, E.eval_eq, hx, hy]
  exact (map_groupWord a.toMonoidHom (E.equiv 1) (E.equiv 2) w).symm

theorem WordTable.Realization.aut_row {T : WordTable} {G : Type*} [Group G]
    (E : T.Realization G) (hT : T.Valid) (a : G ≃* G) (x y : Fin 96)
    (hx : E.equiv x = a (E.equiv 1)) (hy : E.equiv y = a (E.equiv 2))
    (i : Fin 96) : E.equiv (T.eval x y (T.word i)) = a (E.equiv i) := by
  rw [E.aut_eval a x y hx hy, hT.words]

theorem WordTable.Realization.localCandidate {T : WordTable} {G : Type*} [Group G]
    (E : T.Realization G) (hT : T.Valid) (a : G ≃* G) (x y : Fin 96)
    (hx : E.equiv x = a (E.equiv 1)) (hy : E.equiv y = a (E.equiv 2))
    (ho : ∀ i : Fin 32, ∃ j : Fin 32,
      a (E.equiv (T.overlap i)) = E.equiv (T.overlap j)) : T.LocalCandidate x y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply hT.fourth_ne
    apply E.equiv.injective
    apply a.injective
    rw [← E.aut_eval a x y hx hy, h, E.one_eq, map_one]
  · intro h
    have he : E.equiv 2 = E.equiv 0 := by
      apply a.injective
      rw [← hy, h, E.one_eq, map_one]
    have hn := E.equiv.injective he
    exact (by decide : (2 : Fin 96) ≠ 0) hn
  · intro w hw
    apply E.equiv.injective
    rw [E.aut_eval a x y hx hy, hT.relations w hw, E.one_eq, map_one]
  · intro i
    obtain ⟨j, hj⟩ := ho i
    exact ⟨j, E.equiv.injective ((E.aut_row hT a x y hx hy _).trans hj)⟩

abbrev Signature := Fin 32 × Fin 96 × Fin 96

def WordTable.Compatible (L R : WordTable) (s : Signature) : Prop :=
  L.LocalCandidate (L.overlap s.1) s.2.1 ∧
  R.LocalCandidate (R.overlap s.1) s.2.2 ∧
  ∀ i : Fin 32,
    L.label (L.eval (L.overlap s.1) s.2.1
      (L.word (L.overlap i))) =
    R.label (R.eval (R.overlap s.1) s.2.2
      (R.word (R.overlap i)))

instance (L R : WordTable) (s : Signature) : Decidable (L.Compatible R s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _i : Fin 32, _))

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
