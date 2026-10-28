module

public import Theory.SpecificGroups.SymmetricEight.InvolutionActions
public import Theory.GroupTheory.PPerfectHom

/-!
# The two unused points in the symmetric-eight branch

A two-perfect subgroup centralizing `(01)(23)(45)` fixes 6 and 7
individually: its permutation action on that pair has two-group image.
Consequently `(67)` centralizes it. The three-cycle `(23)(34)` is even,
commutes with `(67)`, and does not commute with `(01)(23)(45)`.
These are the permutation calculations used in Aschbacher--Smith,
16.4.9(1), printed p.1189, case (II).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.SymmetricEight.Permutation
open Subgroup Equiv Equiv.Perm

abbrev S := Perm (Fin 8)
abbrev triple : S := Theory.SpecificGroups.SymmetricEight.Involutions.threePairs
def tailSwap : S := swap 6 7
def cubic : S := swap 2 3 * swap 3 4

private theorem triple_fixed (x : Fin 8) : triple x = x ↔ x = 6 ∨ x = 7 := by
  fin_cases x <;> decide

theorem twoPerfect_le_tailFixer (P : Subgroup S) (hperf : IsPPerfect 2 P)
    (hP : P ≤ centralizer ({triple} : Set S)) :
    P ≤ MulAction.stabilizer S (6 : Fin 8) ⊓ MulAction.stabilizer S (7 : Fin 8) := by
  let p : Fin 8 → Prop := fun x => triple x = x
  have hpres (g : P) (x : Fin 8) : p (g.val x) ↔ p x := by
    have hc := mem_centralizer_singleton_iff.mp (hP g.property)
    have he := congrArg (fun w : S => w x) hc
    change g.val (triple x) = triple (g.val x) at he
    constructor
    · intro hg
      apply g.val.injective
      exact he.trans hg
    · intro hx
      exact he.symm.trans (congrArg g.val hx)
  let ρ : P →* Perm {x // p x} :=
    { toFun := fun g => g.val.subtypePerm (hpres g)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hp : IsPGroup 2 (Perm {x // p x}) := by
    apply IsPGroup.of_card
    rw [Nat.card_eq_fintype_card]
    have hc : Fintype.card {x // p x} = 2 := by decide +kernel
    rw [Fintype.card_perm, hc]
    exact (show 2 = 2 ^ 1 by decide)
  have htriv : ρ = 1 := hperf.hom_eq_one_of_isPGroup hp ρ
  intro g hg
  have ht : ρ ⟨g, hg⟩ = 1 := congrArg (fun k : P →* Perm {x // p x} => k ⟨g, hg⟩) htriv
  exact ⟨congrArg (fun w : Perm {x // p x} =>
      (w ⟨6, (triple_fixed 6).mpr (Or.inl rfl)⟩).val) ht,
    congrArg (fun w : Perm {x // p x} =>
      (w ⟨7, (triple_fixed 7).mpr (Or.inr rfl)⟩).val) ht⟩

theorem tailSwap_centralizes_twoPerfect (P : Subgroup S) (hperf : IsPPerfect 2 P)
    (hP : P ≤ centralizer ({triple} : Set S)) : tailSwap ∈ centralizer (P : Set S) := by
  intro a ha
  have hh := twoPerfect_le_tailFixer P hperf hP ha
  change a 6 = 6 ∧ a 7 = 7 at hh
  change a * swap 6 7 = swap 6 7 * a
  rw [mul_swap_eq_swap_mul, hh.1, hh.2]

theorem tailSwap_order : orderOf tailSwap = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · intro h
    have hh := congrArg (fun p : S => p 6) h
    exact (by decide +kernel : tailSwap 6 ≠ (1 : S) 6) hh

theorem tailSwap_not_even : tailSwap ∉ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup]
  decide +kernel

theorem cubic_even : cubic ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup]
  decide +kernel

theorem cubic_commutes_tailSwap : cubic * tailSwap = tailSwap * cubic := by
  decide +kernel

theorem cubic_order : orderOf cubic = 3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · intro h
    have hh := congrArg (fun p : S => p 2) h
    exact (by decide +kernel : cubic 2 ≠ (1 : S) 2) hh

theorem cubic_not_commutes_triple : cubic * triple ≠ triple * cubic := by
  intro h
  exact (by decide +kernel : (cubic * triple) 2 ≠ (triple * cubic) 2)
    (congrArg (fun p : S => p 2) h)

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.SymmetricEight.Permutation
