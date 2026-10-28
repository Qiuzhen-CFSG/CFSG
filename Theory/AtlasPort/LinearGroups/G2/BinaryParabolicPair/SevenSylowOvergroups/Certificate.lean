module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups.Basic

/-!
# Checking recovery words through intermediate matrix columns

The certificate is a path of actual generator actions on eight basis columns.
Induction identifies the resulting columns with the action of the word, and
linear extensionality identifies the original octonion automorphisms. Matrix
labels and proposed words have no mathematical authority before these checks.
The recovery modules consume this interface, avoiding expansion of long words.

The coordinate packing follows the licensed binary G₂ amalgam calculation;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
namespace Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
open Atlas.G2.Explicit Atlas.SplitOctonion

namespace Certificate

/-- Three letters: two derived Sylow elements and the chosen Bruhat representative. -/
def letter (g : G) (i : Fin 3) : G := ![sylowGenerator, rootE 1, g] i

def word (g : G) (w : List (Fin 3)) : G := (w.map (letter g)).prod

/-- Entry `(r,c)` occupies bit `8*r+c`; labels are only candidate matrices. -/
def column (n : ℕ) (c : Fin 8) : Carrier (ZMod 2) :=
  fun r => ((n >>> (8*r.val + c.val)) % 2 : ℕ)

/-- Each constructor checks one actual linear action on every basis column. -/
inductive Check (g : G) : List (Fin 3) → ℕ → Prop
  | nil : Check g [] 9241421688590303745
  | cons {i : Fin 3} {w : List (Fin 3)} {a b : ℕ}
      (step : ∀ c, (letter g i).val (column b c) = column a c)
      (tail : Check g w b) : Check g (i::w) a

private theorem check_action {g : G} {w : List (Fin 3)} {a : ℕ}
    (h : Check g w a) (c : Fin 8) :
    (word g w).val (basisVector c) = column a c := by
  induction h with
  | nil =>
    exact funext ((by decide +kernel : ∀ c r : Fin 8,
      basisVector (F := ZMod 2) c r = column 9241421688590303745 c r) c)
  | @cons i w a b hs ht ih =>
    change (letter g i).val ((word g w).val (basisVector c)) = _
    rw [ih, hs]

/-- A checked column path proves equality in the original automorphism group. -/
theorem check_eq {g : G} {w : List (Fin 3)} {a : ℕ} (h : Check g w a)
    {t : G} (ht : ∀ c, t.val (basisVector c) = column a c) : word g w = t := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext
  intro c
  exact (check_action h c).trans (ht c).symm

theorem word_mem (K : Subgroup G) (hP : derivedSylowAmbient ≤ K) {g : G}
    (hg : g ∈ K) (w : List (Fin 3)) : word g w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons i w ih =>
    apply K.mul_mem ?_ ih
    fin_cases i
    · exact hP sylowGenerator_mem
    · exact hP rootE_mem
    · exact hg

end Certificate

end Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
