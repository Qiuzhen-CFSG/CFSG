module

public import Theory.SpecificGroups.AlternatingSix.M10.Action.DegreeTen.Coordinates

/-!
# Words reaching every ordered triple of distinct labels

The first two permutations translate the nine finite points, and the third
interchanges zero and infinity. The eight words in `pairWord` fix zero and
infinity and send one to each remaining point. Combining these words gives a
word sending (infinity, zero, one) to any ordered triple of distinct labels.
The certificate checks the resulting ten-point permutations by kernel reduction.
`DegreeTen` lifts the same words to the actual extension using `SylowModel`.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), the degree-ten action used in 4.10, pp.41–42.
-/

@[expose] public section

namespace AlternatingSix.M10.Action.DegreeTen

def wordPermutation (w : List (Fin 4)) : Equiv.Perm (Fin 10) :=
  (w.map permutation).prod

def pairWord : Fin 10 → List (Fin 4) := ![
  [], [], [2,3,3,0], [1,3,1,3,2], [0,3,3,1,3,0],
  [0,3,1,2,1,2], [2,1,3,1,3], [0,2,1,3,0,2], [2,0,2,1,3,0], []]

def translationWord (i : Fin 10) : List (Fin 4) :=
  List.replicate (i.val % 3) 0 ++ List.replicate (i.val / 3) 1

def pointWord (i : Fin 10) : List (Fin 4) :=
  if i = 9 then [] else translationWord i ++ [2]

def tripleWord (a b c : Fin 10) : List (Fin 4) :=
  let u := pointWord a
  let v := translationWord ((wordPermutation u)⁻¹ b)
  let w := pairWord ((wordPermutation (u ++ v))⁻¹ c)
  u ++ v ++ w

theorem tripleWord_spec : ∀ a b c : Fin 10, a ≠ b → a ≠ c → b ≠ c →
    wordPermutation (tripleWord a b c) 9 = a ∧
    wordPermutation (tripleWord a b c) 0 = b ∧
    wordPermutation (tripleWord a b c) 1 = c := by decide +kernel

end AlternatingSix.M10.Action.DegreeTen
