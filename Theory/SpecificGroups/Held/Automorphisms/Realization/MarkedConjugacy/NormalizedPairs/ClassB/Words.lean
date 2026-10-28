module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.Contracts

/-!
# Short conjugation words for the second Held involution class

These definitions assert no coverage or rejection facts. The separate checks
identify their action and certify each required equation in the original
ATLAS HeG1-p2058B0 carrier; the seed is literally `(ab³)⁴`.
-/

@[expose] public section

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB

def digit (code : Nat) : Fin 17 := ⟨(code % 32 - 1) % 17, Nat.mod_lt _ (by decide)⟩

def word : Nat → Nat → He
  | 0, _ => secondSeed
  | n + 1, code => if code = 0 then secondSeed else
      MulAut.conj (a * (a * b) ^ (digit code).val) (word n (code / 32))

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB
