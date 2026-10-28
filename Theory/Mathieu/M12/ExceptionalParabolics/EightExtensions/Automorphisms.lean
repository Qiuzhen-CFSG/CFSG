module
public import Theory.Mathieu.M12.ExceptionalParabolics.EightExtensions.Automorphisms.Certificate

/-!
# Explicit automorphisms of the first marked M₁₂ parabolic

The certified coordinate permutations act on the literal endpoint through the
coordinate equivalence. Their right-generator identities extend to all words,
so the maps preserve multiplication; the fourth-iterate identity supplies their
inverses. Products of these four automorphisms realize the restrictions used by
the eight-preserving extension theorem.

Source: the marked local model of Aschbacher--Smith 14.2.21, printed p.988.
The candidate permutations are untrusted data in `Automorphisms.Certificate`.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.EightExtensions
open Coordinates
set_option maxRecDepth 1000000

def mapFn (g : Fin 4) (x : firstParabolic) : firstParabolic :=
  element (image g (equiv.symm x))

theorem mapFn_element (g : Fin 4) (i : Fin 192) :
    mapFn g (element i) = element (image g i) := by
  change element (image g (equiv.symm (equiv i))) = _
  rw [equiv.symm_apply_apply]

private theorem mapFn_one (g : Fin 4) : mapFn g 1 = 1 := by
  rw [← element_zero, mapFn_element, image_zero]

private theorem mapFn_mul_generator (g : Fin 4) (x : firstParabolic) (j : Fin 4) :
    mapFn g (x * generator j) = mapFn g x * mapFn g (generator j) := by
  obtain ⟨i, rfl⟩ := element_surjective x
  rw [← element_step, mapFn_element, image_step, element_rightWord,
    mapFn_element, ← element_generator j, mapFn_element]
  rfl

private theorem mapFn_mul_evaluate (g : Fin 4) (w : List (Fin 4))
    (x : firstParabolic) :
    mapFn g (x * evaluate w) = mapFn g x * mapFn g (evaluate w) := by
  induction w generalizing x with
  | nil => simp only [evaluate, mul_one, mapFn_one]
  | cons j w ih =>
    calc
      mapFn g (x * evaluate (j :: w)) =
          mapFn g ((x * generator j) * evaluate w) := by rw [evaluate, mul_assoc]
      _ = mapFn g (x * generator j) * mapFn g (evaluate w) := ih _
      _ = mapFn g x * (mapFn g (generator j) * mapFn g (evaluate w)) := by
        rw [mapFn_mul_generator, mul_assoc]
      _ = mapFn g x * mapFn g (evaluate (j :: w)) := by rw [evaluate, ih]

private theorem mapFn_mul (g : Fin 4) (x y : firstParabolic) :
    mapFn g (x * y) = mapFn g x * mapFn g y := by
  obtain ⟨i, rfl⟩ := element_surjective y
  exact mapFn_mul_evaluate g (words i) x

private theorem mapFn_four (g : Fin 4) (x : firstParabolic) :
    mapFn g (mapFn g (mapFn g (mapFn g x))) = x := by
  obtain ⟨i, rfl⟩ := element_surjective x
  simp only [mapFn_element, image_four]

/-- Four explicitly certified automorphisms of the actual first endpoint. -/
def automorphism (g : Fin 4) : MulAut firstParabolic where
  toFun := mapFn g
  invFun := fun x => mapFn g (mapFn g (mapFn g x))
  left_inv := by exact mapFn_four g
  right_inv := by exact mapFn_four g
  map_mul' := by exact mapFn_mul g

theorem automorphism_element (g : Fin 4) (i : Fin 192) :
    automorphism g (element i) = element (image g i) := mapFn_element g i

def wordAutomorphism : List (Fin 4) → MulAut firstParabolic
  | [] => 1
  | g :: w => automorphism g * wordAutomorphism w

def wordImage : List (Fin 4) → Fin 192 → Fin 192
  | [], i => i
  | g :: w, i => image g (wordImage w i)

theorem wordAutomorphism_element (w : List (Fin 4)) (i : Fin 192) :
    wordAutomorphism w (element i) = element (wordImage w i) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    change automorphism g (wordAutomorphism w (element i)) = _
    rw [ih, automorphism_element]
    rfl

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.EightExtensions
