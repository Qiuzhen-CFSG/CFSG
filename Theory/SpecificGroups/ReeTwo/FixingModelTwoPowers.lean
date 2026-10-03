module
public import Theory.SpecificGroups.ReeTwo.FixingModelTwoCoordinates

/-!
# Fourth powers in the nonsplit fixing action-two model

On the intrinsic first-core coordinate relation, collected multiplication gives
an explicit square polynomial. Applying it twice gives the fourth-power
polynomial used to count the fibers over the three nonidentity central elements.
The square preserves the coordinate relation, so both applications are justified.

Source: Shinoda (1975), pp.81–83, through the verified fixing action coordinates
and the cyclic extension with actor fourth power equal to the last root.
-/

@[expose] public section
namespace ReeTwo.FixingModel.Two
private theorem core_mul_eq (x y : Core) : x * y = Core.mul x y := rfl
def squarePolynomial (g : Model 2 true) : Model 2 true :=
  let x := g.core
  if g.idx.val = 0 then
    ⟨⟨0,
      0,
      0,
      0,
      0,
      x.b1 + x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b2 * x.b3 + x.b2 * x.b4 + x.b3 * x.b4,
      x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b4 + x.b1 * x.b4,
      x.b2 * x.b3 + x.b4 + x.b3 * x.b4,
      x.b3 + x.b1 * x.b4 + x.b2 * x.b4,
      x.b2 + x.b1 * x.b4 + x.b4 * x.b5 + x.b3 * x.b6 + x.b1 * x.b7 + x.b1 * x.b8 + x.b3 * x.b8 + x.b4 * x.b8⟩,0⟩
  else if g.idx.val = 1 then
    ⟨⟨x.b1 + x.b4,
      x.b3 + x.b4,
      0,
      x.b3 + x.b4,
      x.b1 + x.b4,
      x.b2 * x.b3 + x.b4 + x.b2 * x.b4 + x.b3 * x.b4 + x.b6 + x.b8,
      x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b4 + x.b7 + x.b8,
      x.b1 + x.b3 + x.b2 * x.b4 + x.b5 + x.b6,
      x.b1 * x.b2 + x.b1 * x.b3 + x.b2 * x.b3 + x.b4 + x.b3 * x.b4 + x.b5 + x.b7,
      x.b2 + x.b3 + x.b1 * x.b4 + x.b1 * x.b2 * x.b4 + x.b3 * x.b4 + x.b2 * x.b3 * x.b4 + x.b5 + x.b1 * x.b5 + x.b6 + x.b4 * x.b6 + x.b7 + x.b1 * x.b7 + x.b3 * x.b7 + x.b4 * x.b7 + x.b8 + x.b3 * x.b8⟩,2⟩
  else if g.idx.val = 2 then
    ⟨⟨x.b1 + x.b3,
      x.b1 + x.b3,
      0,
      x.b1 + x.b3,
      x.b1 + x.b3,
      x.b1 * x.b3 + x.b4 + x.b1 * x.b4 + x.b3 * x.b4 + x.b5 + x.b8,
      x.b3 + x.b6 + x.b7,
      x.b1 + x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b2 * x.b3 + x.b1 * x.b4 + x.b3 * x.b4 + x.b6 + x.b7,
      x.b1 + x.b1 * x.b2 + x.b2 * x.b3 + x.b4 + x.b5 + x.b8,
      1 + x.b2 + x.b3 + x.b2 * x.b3 + x.b1 * x.b2 * x.b3 + x.b4 + x.b1 * x.b4 + x.b1 * x.b2 * x.b4 + x.b2 * x.b3 * x.b4 + x.b1 * x.b5 + x.b3 * x.b5 + x.b4 * x.b5 + x.b1 * x.b6 + x.b3 * x.b7 + x.b4 * x.b8⟩,0⟩
  else
    ⟨⟨x.b3 + x.b4,
      x.b1 + x.b4,
      0,
      x.b1 + x.b4,
      x.b3 + x.b4,
      x.b1 * x.b2 + x.b1 * x.b3 + x.b2 * x.b3 + x.b1 * x.b4 + x.b2 * x.b4 + x.b3 * x.b4 + x.b7 + x.b8,
      x.b3 + x.b1 * x.b3 + x.b2 * x.b3 + x.b1 * x.b4 + x.b2 * x.b4 + x.b5 + x.b7,
      x.b1 + x.b1 * x.b2 + x.b3 + x.b2 * x.b3 + x.b4 + x.b1 * x.b4 + x.b6 + x.b8,
      x.b1 + x.b3 + x.b2 * x.b3 + x.b1 * x.b4 + x.b3 * x.b4 + x.b5 + x.b6,
      1 + x.b2 + x.b2 * x.b3 + x.b1 * x.b2 * x.b3 + x.b4 + x.b1 * x.b4 + x.b3 * x.b4 + x.b5 + x.b3 * x.b5 + x.b6 + x.b1 * x.b6 + x.b3 * x.b6 + x.b4 * x.b6 + x.b7 + x.b4 * x.b7 + x.b8 + x.b1 * x.b8⟩,2⟩

def fourthPolynomial (g : Model 2 true) : Model 2 true :=
  let x := g.core
  if g.idx.val = 0 then
    ⟨⟨0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0⟩,0⟩
  else if g.idx.val = 1 then
    ⟨⟨0,
      0,
      0,
      0,
      0,
      x.b1 + x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b2 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8,
      x.b1 + x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b2 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8,
      x.b1 + x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b2 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8,
      x.b1 + x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b2 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8,
      1 + x.b1 + x.b1 * x.b2 + x.b3 + x.b1 * x.b2 * x.b3 + x.b1 * x.b2 * x.b4 + x.b2 * x.b3 * x.b4 + x.b1 * x.b5 + x.b3 * x.b5 + x.b1 * x.b6 + x.b3 * x.b6 + x.b1 * x.b7 + x.b3 * x.b7 + x.b1 * x.b8 + x.b3 * x.b8⟩,0⟩
  else if g.idx.val = 2 then
    ⟨⟨0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      x.b1 + x.b3⟩,0⟩
  else
    ⟨⟨0,
      0,
      0,
      0,
      0,
      x.b1 * x.b2 + x.b1 * x.b3 + x.b2 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8,
      x.b1 * x.b2 + x.b1 * x.b3 + x.b2 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8,
      x.b1 * x.b2 + x.b1 * x.b3 + x.b2 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8,
      x.b1 * x.b2 + x.b1 * x.b3 + x.b2 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8,
      1 + x.b1 * x.b2 + x.b1 * x.b2 * x.b3 + x.b1 * x.b2 * x.b4 + x.b2 * x.b3 * x.b4 + x.b1 * x.b5 + x.b3 * x.b5 + x.b1 * x.b6 + x.b3 * x.b6 + x.b1 * x.b7 + x.b3 * x.b7 + x.b1 * x.b8 + x.b3 * x.b8⟩,0⟩


set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem squarePolynomial_eq (g : Model 2 true)
    (hg : g.core.b0 = g.core.b1 + g.core.b3 + g.core.b4) :
    squarePolynomial g = cmul g g := by
  obtain ⟨x,t⟩ := g
  change x.b0 = x.b1 + x.b3 + x.b4 at hg
  fin_cases t <;> apply CyclicFourCentralExtension.Model.ext
  all_goals first
    | apply Core.ext
    | rfl
    | apply Fin.ext; norm_num [squarePolynomial, cmul]
  all_goals simp [squarePolynomial, cmul, action, action1, action2, action3,
    core_mul_eq, Core.mul, CyclicFourCentralExtension.mark, Core.root, Core.ofCoords, hg]
  all_goals ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide,
    show ∀ z : ZMod 2, z ^ 3 = z from by decide,
    show ∀ z : ZMod 2, z ^ 4 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char

theorem squarePolynomial_relation (g : Model 2 true) :
    (squarePolynomial g).core.b0 = (squarePolynomial g).core.b1 +
      (squarePolynomial g).core.b3 + (squarePolynomial g).core.b4 := by
  unfold squarePolynomial
  split_ifs <;> dsimp <;> ring_nf <;> reduce_mod_char

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem fourthPolynomial_eq (g : Model 2 true)
    (hg : g.core.b0 = g.core.b1 + g.core.b3 + g.core.b4) :
    fourthPolynomial g = g ^ 4 := by
  have he : fourthPolynomial g = squarePolynomial (squarePolynomial g) := by
    obtain ⟨x,t⟩ := g
    fin_cases t <;> apply CyclicFourCentralExtension.Model.ext
    all_goals first | apply Core.ext | rfl
    all_goals simp [fourthPolynomial, squarePolynomial]
    all_goals ring_nf
    all_goals reduce_mod_char
    all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide,
      show ∀ z : ZMod 2, z ^ 3 = z from by decide,
      show ∀ z : ZMod 2, z ^ 4 = z from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  rw [he, squarePolynomial_eq _ (squarePolynomial_relation _), squarePolynomial_eq _ hg]
  simp only [cmul_eq, show 4 = 2 * 2 from rfl, pow_mul, pow_two]
end ReeTwo.FixingModel.Two
