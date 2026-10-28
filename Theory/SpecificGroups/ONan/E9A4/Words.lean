module

public import Theory.SpecificGroups.ONan.MatrixModel
public import Theory.SpecificGroups.Alternating.E9A4Words
import Mathlib.Tactic.FinCases

/-!
# Candidate words for the E₉ × A₄ subgroup of O'Nan

The ATLAS max5 straight-line program supplies two elements of the fixed
projective matrix group. Four short words in these elements are candidates
for the two E₉ generators, a double transposition, and a three-cycle.

The definitions are actual words in the published matrices, so membership in
`ONan.Model` is unconditional. The desired relations and faithfulness remain
separate matrix-checking obligations; no subgroup label is used as a proof.

Sources: ATLAS `ONG1-max5W1`, preserved in `source/`; Aschbacher--Smith,
*The Classification of Quasithin Groups*, A.2.19, printed p. 41.
See `source/README.md` for discovery, attribution, and conventions.
-/

@[expose] public section
namespace ONan.E9A4
open Theory.GroupTheory

/-- The exact two outputs of the ATLAS max5 program. -/
def localGenerators {G : Type*} [Group G] (a b : G) : Fin 2 → G :=
  let w0 := a * b
  let w1 := w0 * b
  let w2 := w0 * w1
  let w3 := w0 * w2
  let w4 := w3 * w0
  let w5 := w4 * w1
  let w6 := w4 * w5
  let w7 := w6 * w6
  let w8 := w6 * w6
  let w9 := w3 * w1
  let w10 := w9 ^ 19
  let w11 := w10⁻¹
  let w12 := w11 * w8
  let w13 := w12 * w10
  let w14 := w1 * w3
  let w15 := w14 ^ 17
  let w16 := w2 * w1
  let w17 := w16 * w0
  let w18 := w17 ^ 8
  let w19 := w15 * w18
  let w20 := w19⁻¹
  let w21 := w20 * w7
  let w22 := w21 * w19
  ![w13, w22]

/-- Four positive letters encode the two local generators and their inverses. -/
def signedLocalGenerators {G : Type*} [Group G] (a b : G) : Fin 4 → G :=
  let c := localGenerators a b
  ![c 0, c 1, (c 0)⁻¹, (c 1)⁻¹]

/-- Fixed words, in the order E₉, E₉, involution, three-cycle. -/
def basisWords : Fin 4 → List (Fin 4) :=
  ![[1, 2, 3, 3, 0, 3, 3, 0, 0, 1], [3, 3, 2, 2, 3, 3, 2, 1, 1, 0], [2, 3, 0, 3, 0, 1, 2, 3, 0, 3, 0, 1, 0, 3, 0, 0, 1, 2, 1, 2, 3, 2], [2, 1, 2, 1, 1, 2, 1, 1, 0, 3]]

def basis {G : Type*} [Group G] (a b : G) : Fin 4 → G :=
  fun i => evalWord (signedLocalGenerators a b) (basisWords i)

def generators : Fin 4 → Model := basis generatorA generatorB
abbrev Linear := Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)
abbrev Mat := Matrix (Fin 45) (Fin 45) (ZMod 7)
def linearGenerators : Fin 4 → Linear := basis linearA linearB

theorem map_evalWord {G H : Type*} [Group G] [Group H]
    (f : G →* H) {n : ℕ} (g : Fin n → G) (w : List (Fin n)) :
    f (evalWord g w) = evalWord (fun i => f (g i)) w := by
  induction w with
  | nil => exact f.map_one
  | cons i w ih => simp only [evalWord, map_mul, ih]

theorem map_basis {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (i : Fin 4) :
    f (basis a b i) = basis (f a) (f b) i := by
  simp only [basis, map_evalWord]
  congr 1
  funext j
  fin_cases j <;> simp [signedLocalGenerators, localGenerators]

theorem project_linearGenerators (i : Fin 4) :
    Matrix.ProjGenLinGroup.mk (linearGenerators i) = (generators i).val := by
  rw [linearGenerators, map_basis]
  let inclusion : Model →* Matrix.ProjGenLinGroup (Fin 45) (ZMod 7) :=
    { toFun := fun g => g.val, map_one' := rfl, map_mul' := fun _ _ => rfl }
  change basis projectiveA projectiveB i = inclusion (basis generatorA generatorB i)
  exact (map_basis inclusion generatorA generatorB i).symm

def normalForm : Theory.SpecificGroups.E9A4.Coord → Model :=
  Theory.SpecificGroups.E9A4.normalForm generators

end ONan.E9A4
