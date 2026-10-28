module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Order.Atoms
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# A check on the maximality shortcut in 2.3.9(7)

In S₇ the centralizer of (01)(23)(45), the stabilizer of its three pairs
and its fixed point, is strictly contained in the stabilizer of 6. Thus
the sentence on printed p.526 asserting ordinary maximality cannot be
used as stated. The local characteristic-two restrictions must be used
when proving the A₇ intersection assertion. This is an obstruction to
that shortcut, not a counterexample to Lemma 2.3.9(7).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, p.526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSevenCheck

open Equiv Subgroup

/-- A permutation of the precise cycle type occurring in 1.1.5(3)(d). -/
def tripleSwap : Perm (Fin 7) := swap 0 1 * swap 2 3 * swap 4 5

private theorem tripleSwap_fixed (i : Fin 7) : tripleSwap i = i ↔ i = 6 := by
  fin_cases i <;> decide

private theorem centralizer_le_point :
    centralizer ({tripleSwap} : Set (Perm (Fin 7))) ≤
      MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) := by
  intro g hg
  have hc := congrArg (fun f : Perm (Fin 7) => f 6)
    (mem_centralizer_singleton_iff.mp hg)
  change g (tripleSwap 6) = tripleSwap (g 6) at hc
  have hz : tripleSwap 6 = 6 := by decide
  rw [hz] at hc
  exact (tripleSwap_fixed (g 6)).mp hc.symm

/-- The centralizer lies properly inside the point stabilizer. -/
theorem centralizer_lt_point :
    centralizer ({tripleSwap} : Set (Perm (Fin 7))) <
      MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) := by
  apply lt_of_le_not_ge centralizer_le_point
  intro h
  have hm : (swap 1 2 : Perm (Fin 7)) ∈
      MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) := by decide
  have hc := congrArg (fun f : Perm (Fin 7) => f 0)
    (mem_centralizer_singleton_iff.mp (h hm))
  exact (by decide : ((swap 1 2 : Perm (Fin 7)) * tripleSwap) (0 : Fin 7) ≠
    (tripleSwap * (swap 1 2 : Perm (Fin 7))) 0) hc

/-- The point stabilizer is proper in S₇. -/
theorem point_lt_top :
    MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro h
  have hm : (swap 0 6 : Perm (Fin 7)) ∈
      MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) := by rw [h]; trivial
  change (swap 0 6 : Perm (Fin 7)) 6 = 6 at hm
  exact (by decide : (swap 0 6 : Perm (Fin 7)) 6 ≠ 6) hm

/-- Ordinary maximality of this centralizer is false. A model-local
recognition proof must retain the restrictions on admissible overgroups. -/
theorem centralizer_not_isCoatom :
    ¬ IsCoatom (centralizer ({tripleSwap} : Set (Perm (Fin 7)))) := by
  intro h
  exact centralizer_lt_point.ne
    ((h.le_iff_eq point_lt_top.ne).mp centralizer_le_point).symm

end CFSG.Quasithin.Chapter2.ComponentRefinement.AlternatingSevenCheck

end
