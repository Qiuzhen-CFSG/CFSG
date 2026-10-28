module

public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic

/-!
# Singular subspaces of binary pentagon forms

A quadratic form on five binary coordinates that vanishes on the coordinate
vectors and is invariant under their cyclic permutation has two coefficients:
one on adjacent pairs and one on diagonal pairs. Each of the three nonzero
forms has no totally singular three-dimensional subspace. The small checked
certificates test triples of the 32 vectors; linear independence transfers
the calculation to an arbitrary singular submodule.

This is the finite quadratic calculation used for the five-orbit conjugate
span in the asymmetric index-five branch of Aschbacher–Smith 14.2.20(1).
-/

@[expose] public section
namespace BinaryPentagon

abbrev Space := Fin 5 → ZMod 2

def polynomial (a b : ZMod 2) (v : Space) : ZMod 2 :=
  a * (v 0 * v 1 + v 1 * v 2 + v 2 * v 3 + v 3 * v 4 + v 4 * v 0) +
  b * (v 0 * v 2 + v 1 * v 3 + v 2 * v 4 + v 3 * v 0 + v 4 * v 1)

def dependent (x y z : Space) : Prop :=
  x = 0 ∨ y = 0 ∨ z = 0 ∨ x + y = 0 ∨ x + z = 0 ∨ y + z = 0 ∨ x + y + z = 0

def singularTriple (a b : ZMod 2) (x y z : Space) : Prop :=
  polynomial a b x = 0 ∧ polynomial a b y = 0 ∧ polynomial a b z = 0 ∧
  polynomial a b (x + y) = 0 ∧ polynomial a b (x + z) = 0 ∧
  polynomial a b (y + z) = 0 ∧ polynomial a b (x + y + z) = 0

instance (x y z : Space) : Decidable (dependent x y z) := inferInstanceAs (Decidable (_ ∨ _))
instance (a b : ZMod 2) (x y z : Space) : Decidable (singularTriple a b x y z) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem adjacent : ∀ x y z : Space, singularTriple 1 0 x y z → dependent x y z := by
  decide +kernel

private theorem diagonal : ∀ x y z : Space, singularTriple 0 1 x y z → dependent x y z := by
  decide +kernel

private theorem complete : ∀ x y z : Space, singularTriple 1 1 x y z → dependent x y z := by
  decide +kernel

private theorem enumeration (a b : ZMod 2) (hab : a ≠ 0 ∨ b ≠ 0)
    (x y z : Space) (hs : singularTriple a b x y z) : dependent x y z := by
  have binary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases binary a with rfl | rfl <;> rcases binary b with rfl | rfl
  · simp at hab
  · exact diagonal x y z hs
  · exact adjacent x y z hs
  · exact complete x y z hs

private theorem dependent_not_independent (x y z : Space)
    (hd : dependent x y z) : ¬ LinearIndependent (ZMod 2) ![x,y,z] := by
  intro hi
  have hr := Fintype.linearIndependent_iff.mp hi
  rcases hd with hx | hy | hz | hxy | hxz | hyz | hxyz
  · exact hi.ne_zero 0 hx
  · exact hi.ne_zero 1 hy
  · exact hi.ne_zero 2 hz
  · have hh := hr ![1,1,0] (by simpa [Fin.sum_univ_succ] using hxy) 0
    norm_num at hh
  · have hh := hr ![1,0,1] (by simpa [Fin.sum_univ_succ] using hxz) 0
    norm_num at hh
  · have hh := hr ![0,1,1] (by simpa [Fin.sum_univ_succ] using hyz) 1
    norm_num at hh
  · have hh := hr ![1,1,1] (by simpa [Fin.sum_univ_succ, add_assoc] using hxyz) 0
    norm_num at hh

theorem polynomial_singular_submodule_card_lt_eight
    (a b : ZMod 2) (hab : a ≠ 0 ∨ b ≠ 0)
    (S : Submodule (ZMod 2) Space) (hS : ∀ x ∈ S, polynomial a b x = 0) :
    Nat.card S < 8 := by
  by_contra hsmall
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
  simp only [Nat.card_zmod] at hc
  have hdim : 3 ≤ Module.finrank (ZMod 2) S := by
    by_contra hd
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show Module.finrank (ZMod 2) S ≤ 2 by omega)
    rw [← hc] at hh
    norm_num at hh
    omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hdim
  let w : Fin 3 → Space := fun i => v i
  have hw : LinearIndependent (ZMod 2) w :=
    hv.map' S.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hs : singularTriple a b (w 0) (w 1) (w 2) :=
    ⟨hS _ (v 0).property, hS _ (v 1).property, hS _ (v 2).property,
      hS _ (S.add_mem (v 0).property (v 1).property),
      hS _ (S.add_mem (v 0).property (v 2).property),
      hS _ (S.add_mem (v 1).property (v 2).property),
      hS _ (S.add_mem (S.add_mem (v 0).property (v 1).property) (v 2).property)⟩
  apply dependent_not_independent (w 0) (w 1) (w 2) (enumeration a b hab _ _ _ hs)
  convert hw using 1
  ext i
  fin_cases i <;> rfl

end BinaryPentagon
