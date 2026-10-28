module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.CosetWordCertificate.RelatorScan
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# A small subgroup of the Hall--Janko presentation

In the abstract five-relator presentation, `a` and `c = b⁻¹ab` are
involutions and `(ac)¹² = 1`. Consequently `⟨a,c⟩` is finite of order at
most 24. A certified cover by 25200 cosets will bound the whole presentation
by 604800. The auxiliary letter `c` is an actual word, not an additional
hypothesis on the presentation.

Source: ATLAS J2G1-P2, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J2G1-P2.
The application is Aschbacher--Smith K.4.5, printed p.460/PDF p.471.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact
open Presentation Subgroup.CosetWordCertificate

abbrev a : UniversalGroup := PresentedGroup.of 0
abbrev b : UniversalGroup := PresentedGroup.of 1

/-- The original five equations hold in the presented group itself. -/
theorem universal_relations : Relations a b := by
  intro i
  have h := PresentedGroup.one_of_mem (rels := relators) (Set.mem_range_self i)
  rw [map_relatorValues] at h
  exact h

def c : UniversalGroup := b⁻¹ * a * b

def dihedral : Subgroup UniversalGroup := Subgroup.closure ({a, c} : Set UniversalGroup)

theorem a_sq : a ^ 2 = 1 := universal_relations 0

theorem a_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using a_sq)

theorem c_sq : c ^ 2 = 1 := by
  calc
    c ^ 2 = b⁻¹ * a ^ 2 * b := by simp [c, pow_two, mul_assoc]
    _ = 1 := by rw [a_sq]; simp

theorem ac_pow : (a * c) ^ 12 = 1 := by
  have h : (a⁻¹ * b⁻¹ * a * b) ^ 12 = 1 := universal_relations 3
  simpa only [a_inv, c, mul_assoc] using h

/-- The subgroup bound uses only the first and fourth defining relations. -/
theorem dihedral_bound : Finite dihedral ∧ Nat.card dihedral ≤ 24 := by
  simpa only [dihedral, Set.pair_comm a c] using
    Subgroup.closure_pair_finite_card_le_of_involutions (by decide : 0 < 12)
      c a c_sq a_sq ac_pow

/-- The third letter names the conjugate involution used by the enumerator. -/
def generator : Nat → UniversalGroup
  | 0 => a
  | 1 => b
  | _ => c

def allowed (x : Letter Nat) : Bool := x == (0, true) || x == (2, true)

theorem allowed_mem (x : Letter Nat) (h : allowed x = true) :
    eval generator [x] ∈ dihedral := by
  have hx : x = (0, true) ∨ x = (2, true) := by simpa [allowed] using h
  rcases hx with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert a {c})
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton c))

/-- Five literal source words, the definition of `c`, and two proved consequences. -/
def sourceWords : Fin 8 → Word Nat := fun i => match i.val with
  | 0 => [(0, true), (0, true)]
  | 1 => [(1, true), (1, true), (1, true)]
  | 2 => [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)]
  | 3 => [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)]
  | 4 => [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]
  | 5 => [(1, false), (0, true), (1, true), (2, false)]
  | 6 => [(2, true), (2, true)]
  | 7 => [(0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true)]
  | _ => []

theorem sourceWords_eval (i : Fin 8) : eval generator (sourceWords i) = 1 := by
  fin_cases i
  · change eval generator [(0, true), (0, true)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, relatorValues, longWord, pow_succ, mul_assoc]
      using universal_relations 0
  · change eval generator [(1, true), (1, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, relatorValues, longWord, pow_succ, mul_assoc]
      using universal_relations 1
  · change eval generator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, relatorValues, longWord, pow_succ, mul_assoc]
      using universal_relations 2
  · change eval generator [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, relatorValues, longWord, pow_succ, mul_assoc]
      using universal_relations 3
  · change eval generator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, relatorValues, longWord, pow_succ, mul_assoc]
      using universal_relations 4
  · change eval generator [(1, false), (0, true), (1, true), (2, false)] = 1
    simp [eval, FreeGroup.lift_mk, generator, c, mul_assoc]
  · change eval generator [(2, true), (2, true)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, pow_succ, mul_assoc] using c_sq
  · change eval generator [(0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, pow_succ, mul_assoc] using ac_pow

/-- Every inverse rotation remains an actual relation in the presentation. -/
def rotatedRelator (r : Nat) : Word Nat :=
  (if r % 128 < 64 then sourceWords ⟨(r / 128) % 8, Nat.mod_lt _ (by decide)⟩
   else FreeGroup.invRev (sourceWords ⟨(r / 128) % 8, Nat.mod_lt _ (by decide)⟩)).rotate
    (r % 64)

theorem rotatedRelator_eval (r : Nat) : eval generator (rotatedRelator r) = 1 := by
  have hr : eval generator
      (if r % 128 < 64 then sourceWords ⟨(r / 128) % 8, Nat.mod_lt _ (by decide)⟩
       else FreeGroup.invRev (sourceWords ⟨(r / 128) % 8, Nat.mod_lt _ (by decide)⟩)) = 1 := by
    split
    · exact sourceWords_eval _
    · rw [eval_invRev, sourceWords_eval, inv_one]
  simpa [eval, FreeGroup.lift_mk, rotatedRelator, List.map_rotate] using
    List.prod_rotate_eq_one_of_prod_eq_one (by simpa [eval, FreeGroup.lift_mk] using hr)
      (r % 64)

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact
