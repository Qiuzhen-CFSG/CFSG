module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.CompiledMarkedActions
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Branches

/-!
# Certified cached actions for the Held prime-orbit checks

The four packed marked actions already certified by the double-coset
calculation replace repeated evaluation of the same long marked words.
Their equality with the original test action transports the two orbit
checks to `obstruction_of_testAction`, so the result is an actual prime-order
element of the original generated subgroup, without additional premises.

Source: the fixed ATLAS Held carrier and `../source/README.md`;
`DoubleCosets.CompiledActions.markTable_eq` certifies the reused cache.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
open DoubleCosets.CompiledActions

@[expose] public def cachedLetter (j : Fin 4831) : ℕ → Fin 2058 → Fin 2058
  | 1 => markTable 0
  | 2 => markTable 1
  | 3 => markTable 2
  | 4 => markTable 3
  | _ => representativeAction j

private theorem cachedLetter_eq (j : Fin 4831) (i : ℕ) :
    cachedLetter j i = testLetterAction j i := by
  unfold cachedLetter testLetterAction
  split
  · exact (funext (markTable_eq 0)).trans (markedAction_eq 0).symm
  · exact (funext (markTable_eq 1)).trans (markedAction_eq 1).symm
  · exact (funext (markTable_eq 2)).trans (markedAction_eq 2).symm
  · exact (funext (markTable_eq 3)).trans (markedAction_eq 3).symm
  · split <;> first | contradiction | rfl

@[expose] public def cachedAction (j : Fin 4831) : List ℕ → Fin 2058 → Fin 2058
  | [], t => t
  | i :: w, t => cachedLetter j i (cachedAction j w t)

public theorem cachedAction_eq (j : Fin 4831) (w : List ℕ) :
    cachedAction j w = testAction j w := by
  funext t
  induction w generalizing t with
  | nil => rfl
  | cons i w ih => simp only [cachedAction, testAction, cachedLetter_eq, ih]

public theorem obstruction_of_cachedAction (j : Fin 4831) (w : List ℕ) (p e : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (i : Fin 2058)
    (hper : (cachedAction j w)^[e * p] i = i)
    (hne : (cachedAction j w)^[e] i ≠ i) : HasPrimeObstruction (representative j) := by
  rw [cachedAction_eq] at hper hne
  exact obstruction_of_testAction j w p e hp hp2 hp3 i hper hne

end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
