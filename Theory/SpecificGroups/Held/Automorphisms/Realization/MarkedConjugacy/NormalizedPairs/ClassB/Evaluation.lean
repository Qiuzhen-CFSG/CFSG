module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Tables
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Words

/-!
# Evaluation of the actual Held conjugation words

Source: the literal generators and relators of HeG1-P1.M in the retained
HeG1-p2058B0 carrier. Conjugation by powers of `ab` preserves the normalized
relation test. Closure under `a` and `ab` covers the entire conjugacy class.
-/

@[expose] public section

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB

def fastWord : Nat → Nat → Equiv.Perm (Fin 2058)
  | 0, _ => perm 18
  | n + 1, code => if code = 0 then perm 18 else
      MulAut.conj (perm 17 * powPerm (digit code)) (fastWord n (code / 32))

theorem representation_word (n code : Nat) : representation (word n code) = fastWord n code := by
  induction n generalizing code with
  | zero => exact perm_eq_18.symm
  | succ n ih =>
    simp only [word, fastWord]
    split
    · exact perm_eq_18.symm
    · change representation ((a * (a * b) ^ (digit code).val) * word n (code / 32) *
        (a * (a * b) ^ (digit code).val)⁻¹) =
        (perm 17 * powPerm (digit code)) * fastWord n (code / 32) *
          (perm 17 * powPerm (digit code))⁻¹
      simp only [map_mul, map_inv, map_pow, ih,
        perm_eq_17, powPerm_eq]
      rfl

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB
