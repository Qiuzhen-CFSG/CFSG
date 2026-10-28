module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.Relations
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Matrix realization of the characteristic-two C₂ relations

The five commuting pairs and crossing equation are checked in 2-by-2
blocks. The actual words x₆(1)x₇(1)x₆(1) and x₂(1)x₃(1)x₂(1) implement
the two permutations of the eight roots. The permutations realized by
matrix automorphisms form a subgroup, so the base equations imply every
chamber equation in the stated schema. All calculations include fields
of orders two and four; no field-size condition is used.

Source: Steinberg §6, relations (A),(B), printed p.68, in the original
`FirstCohomologySymplecticFour.Generation` matrix conventions.
-/

@[expose] public section
open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootPresentation
variable {F : Type*} [Field F]
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
variable [CharP F 2]

theorem matrix_positive : PositiveRelations (rootElement (K := F)) where
  add := RootSubgroup.element_add
  commuting i s t := by
    change rootElement _ s * rootElement _ t = rootElement _ t * rootElement _ s
    apply Subtype.ext
    change rootMatrix _ s * rootMatrix _ t = rootMatrix _ t * rootMatrix _ s
    fin_cases i <;>
      simp [commutingPairs, rootMatrix, Matrix.fromBlocks_multiply,
        Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, add_comm, mul_comm]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, sub_eq_add_neg, CharTwo.neg_eq, add_assoc,
        CharTwo.add_self_eq_zero, mul_comm]
  crossing v c := by
    apply Subtype.ext
    change rootMatrix 2 v * rootMatrix 6 c =
      rootMatrix 6 c * rootMatrix 0 (c^2*v) * rootMatrix 4 (c*v) * rootMatrix 2 v
    simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, CharTwo.neg_eq, CharTwo.add_self_eq_zero, add_assoc] <;>
      (ring_nf; all_goals simp [CharTwo.two_eq_zero, show (3 : F) = 1 from by linear_combination CharTwo.two_eq_zero (R := F), CharTwo.neg_eq])

def shortWeyl : Sp F := rootElement 6 1 * rootElement 7 1 * rootElement 6 1

def longWeyl : Sp F := rootElement 2 1 * rootElement 3 1 * rootElement 2 1

theorem shortWeyl_root (r : Fin 8) (t : F) :
    shortWeyl * rootElement r t = rootElement (shortReflection r) t * shortWeyl := by
  apply Subtype.ext
  change (rootMatrix 6 1 * rootMatrix 7 1 * rootMatrix 6 1) * rootMatrix r t =
    rootMatrix (shortReflection r) t * (rootMatrix 6 1 * rootMatrix 7 1 * rootMatrix 6 1)
  fin_cases r <;>
    simp [shortReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub] <;>
    (repeat' apply And.intro) <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_two,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero, add_assoc] <;>
    (ring_nf; all_goals simp [CharTwo.two_eq_zero, show (3 : F) = 1 from by linear_combination CharTwo.two_eq_zero (R := F), CharTwo.neg_eq])


theorem longWeyl_root (r : Fin 8) (t : F) :
    longWeyl * rootElement r t = rootElement (longReflection r) t * longWeyl := by
  apply Subtype.ext
  change (rootMatrix 2 1 * rootMatrix 3 1 * rootMatrix 2 1) * rootMatrix r t =
    rootMatrix (longReflection r) t * (rootMatrix 2 1 * rootMatrix 3 1 * rootMatrix 2 1)
  fin_cases r <;>
    simp [longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub] <;>
    (repeat' apply And.intro) <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_two,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero, add_assoc]


private def realized : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | ∃ a : MulAut (Sp F), ∀ r t, a (rootElement r t) = rootElement (σ r) t}
  one_mem' := ⟨1, fun _ _ => rfl⟩
  mul_mem' := by
    rintro σ τ ⟨a,ha⟩ ⟨b,hb⟩
    exact ⟨a*b, fun r t => by change a (b (rootElement r t)) = _; rw [hb, ha]; rfl⟩
  inv_mem' := by
    rintro σ ⟨a,ha⟩
    refine ⟨a.symm, fun r t => ?_⟩
    apply a.injective
    simp [ha]

theorem exists_weyl_automorphism (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ weyl) :
    ∃ a : MulAut (Sp F), ∀ r t, a (rootElement r t) = rootElement (σ r) t := by
  have h : weyl ≤ realized (F := F) := by
    apply (closure_le _).mpr
    rintro σ (rfl | rfl)
    · refine ⟨MulAut.conj (shortWeyl (F := F)), fun r t => ?_⟩
      exact mul_inv_eq_iff_eq_mul.mpr (shortWeyl_root r t)
    · refine ⟨MulAut.conj (longWeyl (F := F)), fun r t => ?_⟩
      exact mul_inv_eq_iff_eq_mul.mpr (longWeyl_root r t)
  exact h hσ

theorem matrix_relations : Relations (rootElement (K := F)) := by
  intro σ hσ
  obtain ⟨a,ha⟩ := exists_weyl_automorphism (F := F) σ hσ
  refine {add := ?_, commuting := ?_, crossing := ?_}
  · intro r s t
    exact RootSubgroup.element_add _ _ _
  · intro i s t
    rw [← ha, ← ha]
    exact ((matrix_positive (F := F)).commuting i s t).map a.toMonoidHom
  · intro v c
    simp only [← ha]
    simpa only [map_mul] using congrArg a ((matrix_positive (F := F)).crossing v c)
end Theory.SpecificGroups.SymplecticFour.RootPresentation
