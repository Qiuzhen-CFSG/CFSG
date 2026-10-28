module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.Presentation
public import Theory.GroupTheory.CosetWordCertificate

/-!
# The fixed subgroup for the six-relator G₂(3) order bound

The two words below are the outputs of the ATLAS `G23G1-max3W1` program.
They specify a subgroup of the literal six-relator presentation. The intended
bound is obtained from a 364-coset cover and the subgroup bound 11664.
Neither the ATLAS subgroup label nor the exploratory permutation calculation
is used to assert either bound here.

The first generator is a conjugate of the original involution. The signed-word
interfaces evaluate in the original presented group and retain all six source
relations, including the fifth displayed relation.

Source: https://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max3W1;
the original program and discovery data are retained in `source/`.
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound

open Subgroup.CosetWordCertificate

/-- Literal outputs of the max3 straight-line program, in an arbitrary group. -/
def subgroupWord {G : Type*} [Group G] (a b : G) : Bool → G :=
  let c := a * b
  let d := c * b
  fun
  | false => (c ^ 6)⁻¹ * a * c ^ 6
  | true => (d ^ 3)⁻¹ * (b * ((c * (c * d)) * c)) * d ^ 3

theorem map_subgroupWord {G K : Type*} [Group G] [Group K] (f : G →* K)
    (a b : G) (s : Bool) :
    f (subgroupWord a b s) = subgroupWord (f a) (f b) s := by
  cases s <;> simp [subgroupWord]

/-- Both generators are fixed words in the original marked pair. -/
def boundGenerator : Bool → Presentation.Presented :=
  subgroupWord (Presentation.generator false) (Presentation.generator true)

/-- The actual subgroup whose finite order must be bounded. -/
def boundSubgroup : Subgroup Presentation.Presented :=
  Subgroup.closure (Set.range boundGenerator)

theorem boundGenerator_mem (s : Bool) : boundGenerator s ∈ boundSubgroup :=
  Subgroup.subset_closure ⟨s, rfl⟩

theorem lift_generator_eq_toPresented :
    FreeGroup.lift Presentation.generator = Presentation.toPresented := by
  apply FreeGroup.ext_hom
  intro s
  exact FreeGroup.lift_apply_of

/-- The six relations hold in this presentation itself, without a model map. -/
theorem generator_relations (i : Fin 6) :
    Presentation.word (Presentation.generator false) (Presentation.generator true) i = 1 := by
  change Presentation.word (Presentation.toPresented (FreeGroup.of false))
    (Presentation.toPresented (FreeGroup.of true)) i = 1
  rw [← Presentation.map_word]
  exact Presentation.toPresented_relator i

/-- Concatenate a fixed word a specified number of times. -/
def powerLetters (w : Word Bool) : Nat → Word Bool
  | 0 => []
  | n + 1 => w ++ powerLetters w n

@[simp] theorem eval_powerLetters {G : Type*} [Group G] (g : Bool → G)
    (w : Word Bool) (n : Nat) : eval g (powerLetters w n) = eval g w ^ n := by
  induction n with
  | zero => simp [powerLetters]
  | succ n ih => rw [powerLetters, eval_append, ih, pow_succ']

def commutatorLetters (u v : Word Bool) : Word Bool :=
  FreeGroup.invRev u ++ FreeGroup.invRev v ++ u ++ v

@[simp] theorem eval_commutatorLetters {G : Type*} [Group G] (g : Bool → G)
    (u v : Word Bool) : eval g (commutatorLetters u v) =
      Presentation.sourceCommutator (eval g u) (eval g v) := by
  simp only [commutatorLetters, eval_append, eval_invRev, Presentation.sourceCommutator]

/-- The unreduced spellings of all six source words, before free cancellation. -/
def sourceLetters : Fin 6 → Word Bool :=
  let a : Word Bool := [(false, true)]
  let b : Word Bool := [(true, true)]
  let c := a ++ b
  let d := a ++ FreeGroup.invRev b
  ![powerLetters a 2, powerLetters b 3, powerLetters c 13,
    powerLetters (commutatorLetters a b) 13,
    powerLetters c 2 ++ powerLetters (commutatorLetters a b) 4 ++
      powerLetters c 3 ++ powerLetters (commutatorLetters a (b ++ a ++ b)) 3,
    powerLetters (powerLetters (powerLetters c 3 ++ d) 2 ++
      powerLetters c 2 ++ powerLetters d 2) 2]

theorem eval_sourceLetters {G : Type*} [Group G] (g : Bool → G) (i : Fin 6) :
    eval g (sourceLetters i) = Presentation.word (g false) (g true) i := by
  fin_cases i <;>
    simp [sourceLetters, Presentation.word, eval_append, eval_cons, eval_invRev, mul_assoc]

/-- Freely reduced signed words, still using Mathlib's positive-Boolean convention. -/
def relatorLetters (i : Fin 6) : Word Bool := reduce (sourceLetters i)

theorem relatorLetters_eq_one (i : Fin 6) :
    eval Presentation.generator (relatorLetters i) = 1 := by
  rw [relatorLetters, eval_reduce, eval_sourceLetters, generator_relations]

def boundFreeWord : Bool → FreeGroup Bool :=
  subgroupWord (FreeGroup.of false) (FreeGroup.of true)

/-- The subgroup program expanded into signed words, then freely reduced. -/
def boundLetters (s : Bool) : Word Bool :=
  let a : Word Bool := [(false, true)]
  let b : Word Bool := [(true, true)]
  let c := a ++ b
  let d := c ++ b
  reduce (if s then FreeGroup.invRev (powerLetters d 3) ++
      (b ++ ((c ++ (c ++ d)) ++ c)) ++ powerLetters d 3
    else FreeGroup.invRev (powerLetters c 6) ++ a ++ powerLetters c 6)

theorem eval_boundLetters (s : Bool) :
    eval Presentation.generator (boundLetters s) = boundGenerator s := by
  cases s <;> simp [boundLetters, eval_reduce, eval_append, eval_invRev,
    eval_cons, boundGenerator, subgroupWord, mul_assoc]

/-- This local relation already follows from the first source relator. -/
theorem boundGenerator_false_sq : boundGenerator false ^ 2 = 1 := by
  have h : Presentation.generator false ^ 2 = 1 := generator_relations 0
  change (((Presentation.generator false * Presentation.generator true) ^ 6)⁻¹ *
    Presentation.generator false *
    (Presentation.generator false * Presentation.generator true) ^ 6) ^ 2 = 1
  simpa only [inv_inv, h, mul_one, inv_mul_cancel] using
    (conj_pow (a := ((Presentation.generator false * Presentation.generator true) ^ 6)⁻¹)
      (b := Presentation.generator false) (i := 2))

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound
