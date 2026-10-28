module

public import Theory.SpecificGroups.Alternating.SmallSolvableFive
public import Theory.SpecificGroups.AlternatingSix.SmallIndex

/-!
# The eight-letter endpoint of the alternating five-divisibility obstruction

A solvable subgroup D containing a Sylow two-subgroup of A₈ has order
divisible by 64. A point stabilizer H embeds in A₇, so its order divides
2520 and its index in D is at most eight. Divisibility therefore forces
that index to be eight. Consequently H retains a Sylow two-subgroup of
A₇ and any factor of five in |D|, contradicting the seven-letter theorem.

The final theorem gives the complete A₅–A₈ normalized-subgroup form used
in Aschbacher–Smith 15.2.4, printed pp.1106–1107.
-/

public section

open Subgroup Equiv.Perm
namespace Theory.SpecificGroups.Alternating.SmallSolvableFive
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The complete small alternating normalized-subgroup obstruction. -/
theorem not_five_dvd_of_sylow_normalizes_le_eight {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (Y : Subgroup (alternatingGroup (Fin n))) (hsolv : Group.IsSolvable Y)
    (S : Sylow 2 (alternatingGroup (Fin n)))
    (hSY : (S : Subgroup (alternatingGroup (Fin n))) ≤
      normalizer (Y : Set (alternatingGroup (Fin n)))) : ¬5 ∣ Nat.card Y :=
  not_five_dvd_of_sylow_normalizes hn Y hsolv S hSY

end Theory.SpecificGroups.Alternating.SmallSolvableFive
