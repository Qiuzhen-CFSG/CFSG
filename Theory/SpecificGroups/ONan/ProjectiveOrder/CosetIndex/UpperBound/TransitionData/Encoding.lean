module
public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.UpperBound.MatrixCertificate
/-!
# Prefix encoding for the O'Nan transition witnesses

Words are reconstructed from a finite prefix tree with explicit depth fuel.
The local alphabet is encoded separately, so every reconstructed local word
uses only the specified subgroup generators, independently of numerical data.
The full transition identities remain separate obligations.

Source: ATLAS matrices in `refs/original/onan/` and the local words attributed
in `ProjectiveOrder/source/`. The numerical producer is in `source/`.
-/

namespace ONan.OrderCertificate.UpperBound.TransitionData
open Subgroup.CosetWordCertificate
@[expose] public def localLetter (n : Nat) : Letter (Fin 4) :=
  (if n % 2 = 0 then 2 else 3, n / 2 % 2 = 0)
@[expose] public def prefixWord (parent letter : Nat → Nat)
    (decode : Nat → Letter (Fin 4)) : Nat → Nat → Word (Fin 4)
  | 0, _ => []
  | fuel + 1, i => if i = 0 then [] else
      prefixWord parent letter decode fuel (parent i) ++ [decode (letter i)]
public theorem prefixWord_allowed (parent letter : Nat → Nat) (fuel i : Nat) :
    ∀ b ∈ prefixWord parent letter localLetter fuel i, allowed b = true := by
  induction fuel generalizing i with
  | zero => simp [prefixWord]
  | succ fuel ih =>
    simp only [prefixWord]
    split
    · simp
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ih _ _ hb
      · have he : b = localLetter (letter i) := List.mem_singleton.mp hb
        subst b
        simp only [localLetter, allowed]
        split <;> decide
end ONan.OrderCertificate.UpperBound.TransitionData
