module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The normalized pivot candidates in the marked symmetric six

Fix the marked transposition (01). An even nonidentity involution commuting
with it is one of nine permutations. If it commutes with its conjugates by
(23), (34), and (45), only the three nonidentity elements of the Klein four
on the other four letters remain. The single finite check below is reduced
by Lean's kernel; no native computation is trusted.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), proof of Lemma 4.8, p.41.
-/

@[expose] public section

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange.PivotPermutations

open Equiv Equiv.Perm

abbrev P := Perm (Fin 6)
def base : P := swap 0 1
def klein0 : P := swap 2 3 * swap 4 5
def klein1 : P := swap 2 4 * swap 3 5
def klein2 : P := swap 2 5 * swap 3 4

def commutesConjugate (q g : P) : Prop :=
  q * (g * q * g⁻¹) = (g * q * g⁻¹) * q

instance (q g : P) : Decidable (commutesConjugate q g) :=
  inferInstanceAs (Decidable (_ = _))

/-- Normalization of an abelian even subgroup by the marked transposition
centralizer forces its nonidentity elements into the complementary Klein four. -/
theorem candidates : ∀ q : P,
    (q * q = 1 ∧ q * base = base * q ∧ q ≠ 1 ∧ sign q = 1 ∧
      commutesConjugate q (swap 2 3) ∧ commutesConjugate q (swap 3 4) ∧
      commutesConjugate q (swap 4 5)) →
    q = klein0 ∨ q = klein1 ∨ q = klein2 := by
  decide +kernel

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange.PivotPermutations
end
