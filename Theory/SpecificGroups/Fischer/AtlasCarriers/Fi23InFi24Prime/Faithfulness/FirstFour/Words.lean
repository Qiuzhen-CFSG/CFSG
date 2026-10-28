module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# The first four stabilizer word lists in an arbitrary group

These are exactly nodes 3 through 32 of `StabilizerWords`, made polymorphic
in their two generators. Naturality under group homomorphisms lets finite
permutation certificates be transported to the literal ATLAS carrier.
No stabilizer assertion is built into these definitions.

The source witnesses are `source/faithfulness/nodes.json` and `levels.json`;
`source/generate_model.py` reproduces this transcription directly from the
existing Lean words. Source motivation: GLS3 Table 5.3v, ATLAS F24G1-p306936B0.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.Word
variable {G H : Type*} [Group G] [Group H]

def word3 (a b : G) : G :=
  a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * b * a⁻¹ * b * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * b * a⁻¹ * b * b * a⁻¹ * b * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * b * a⁻¹

theorem map_word3 (f : G →* H) (a b : G) :
    f (word3 a b) = word3 (f a) (f b) := by
  simp only [word3, map_mul, map_inv]

def word4 (a b : G) : G :=
  b * b * a⁻¹ * b * a⁻¹ * b * b * a⁻¹ * b * b * a⁻¹ * b * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * b * a⁻¹ * b * b * a⁻¹

theorem map_word4 (f : G →* H) (a b : G) :
    f (word4 a b) = word4 (f a) (f b) := by
  simp only [word4, map_mul, map_inv]

def word5 (a b : G) : G :=
  (word3 a b) * b * (word4 a b)⁻¹

theorem map_word5 (f : G →* H) (a b : G) :
    f (word5 a b) = word5 (f a) (f b) := by
  simp only [word5, map_mul, map_inv, map_word3, map_word4]

def word6 (a b : G) : G :=
  a⁻¹ * b * b * a⁻¹ * b * b * a⁻¹ * b * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹

theorem map_word6 (f : G →* H) (a b : G) :
    f (word6 a b) = word6 (f a) (f b) := by
  simp only [word6, map_mul, map_inv]

def word7 (a b : G) : G :=
  b * b * a⁻¹ * b * b * a⁻¹ * b * a⁻¹ * b * b * a⁻¹ * b * b * a⁻¹ * b * a⁻¹ * b * b * a⁻¹ * b * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * b * a⁻¹

theorem map_word7 (f : G →* H) (a b : G) :
    f (word7 a b) = word7 (f a) (f b) := by
  simp only [word7, map_mul, map_inv]

def word8 (a b : G) : G :=
  (word6 a b) * b * (word7 a b)⁻¹

theorem map_word8 (f : G →* H) (a b : G) :
    f (word8 a b) = word8 (f a) (f b) := by
  simp only [word8, map_mul, map_inv, map_word6, map_word7]

def word9 (a b : G) : G :=
  (word8 a b) * (word5 a b) * (word5 a b) * (word8 a b) * (word8 a b) * (word5 a b) * (word8 a b) * (word5 a b) * (word5 a b) * (word8 a b) * (word5 a b) * (word8 a b) * (word5 a b) * (word8 a b) * (word5 a b)

theorem map_word9 (f : G →* H) (a b : G) :
    f (word9 a b) = word9 (f a) (f b) := by
  simp only [word9, map_mul, map_word5, map_word8]

def word10 (a b : G) : G :=
  (word8 a b) * (word5 a b) * (word5 a b) * (word5 a b) * (word5 a b) * (word5 a b) * (word5 a b) * (word5 a b) * (word8 a b) * (word8 a b) * (word5 a b) * (word8 a b) * (word8 a b) * (word5 a b) * (word8 a b)

theorem map_word10 (f : G →* H) (a b : G) :
    f (word10 a b) = word10 (f a) (f b) := by
  simp only [word10, map_mul, map_word5, map_word8]

def word11 (a b : G) : G :=
  (word9 a b) * (word5 a b) * (word10 a b)⁻¹

theorem map_word11 (f : G →* H) (a b : G) :
    f (word11 a b) = word11 (f a) (f b) := by
  simp only [word11, map_mul, map_inv, map_word10, map_word5, map_word9]

def word12 (a b : G) : G :=
  (word8 a b) * (word8 a b) * (word5 a b) * (word8 a b) * (word5 a b) * (word5 a b) * (word5 a b) * (word8 a b) * (word8 a b) * (word5 a b) * (word5 a b) * (word5 a b)

theorem map_word12 (f : G →* H) (a b : G) :
    f (word12 a b) = word12 (f a) (f b) := by
  simp only [word12, map_mul, map_word5, map_word8]

def word13 (a b : G) : G :=
  (word5 a b) * (word8 a b) * (word8 a b) * (word8 a b) * (word8 a b) * (word8 a b) * (word5 a b) * (word5 a b) * (word8 a b) * (word5 a b) * (word8 a b) * (word8 a b) * (word5 a b)

theorem map_word13 (f : G →* H) (a b : G) :
    f (word13 a b) = word13 (f a) (f b) := by
  simp only [word13, map_mul, map_word5, map_word8]

def word14 (a b : G) : G :=
  (word12 a b) * (word8 a b) * (word13 a b)⁻¹

theorem map_word14 (f : G →* H) (a b : G) :
    f (word14 a b) = word14 (f a) (f b) := by
  simp only [word14, map_mul, map_inv, map_word12, map_word13, map_word8]

def word15 (a b : G) : G :=
  (word11 a b) * (word14 a b) * (word14 a b) * (word14 a b) * (word11 a b) * (word11 a b) * (word14 a b) * (word11 a b) * (word14 a b) * (word14 a b) * (word11 a b) * (word11 a b) * (word11 a b)

theorem map_word15 (f : G →* H) (a b : G) :
    f (word15 a b) = word15 (f a) (f b) := by
  simp only [word15, map_mul, map_word11, map_word14]

def word16 (a b : G) : G :=
  (word11 a b) * (word14 a b) * (word11 a b) * (word14 a b) * (word14 a b) * (word11 a b) * (word14 a b)

theorem map_word16 (f : G →* H) (a b : G) :
    f (word16 a b) = word16 (f a) (f b) := by
  simp only [word16, map_mul, map_word11, map_word14]

def word17 (a b : G) : G :=
  (word15 a b) * (word11 a b) * (word16 a b)⁻¹

theorem map_word17 (f : G →* H) (a b : G) :
    f (word17 a b) = word17 (f a) (f b) := by
  simp only [word17, map_mul, map_inv, map_word11, map_word15, map_word16]

def word18 (a b : G) : G :=
  (word11 a b) * (word14 a b) * (word11 a b) * (word14 a b) * (word11 a b) * (word11 a b) * (word14 a b) * (word11 a b) * (word14 a b) * (word14 a b) * (word11 a b) * (word11 a b)

theorem map_word18 (f : G →* H) (a b : G) :
    f (word18 a b) = word18 (f a) (f b) := by
  simp only [word18, map_mul, map_word11, map_word14]

def word19 (a b : G) : G :=
  (word14 a b) * (word14 a b) * (word11 a b) * (word14 a b) * (word14 a b) * (word14 a b) * (word11 a b) * (word14 a b) * (word14 a b) * (word14 a b) * (word11 a b) * (word14 a b)

theorem map_word19 (f : G →* H) (a b : G) :
    f (word19 a b) = word19 (f a) (f b) := by
  simp only [word19, map_mul, map_word11, map_word14]

def word20 (a b : G) : G :=
  (word18 a b) * (word11 a b) * (word19 a b)⁻¹

theorem map_word20 (f : G →* H) (a b : G) :
    f (word20 a b) = word20 (f a) (f b) := by
  simp only [word20, map_mul, map_inv, map_word11, map_word18, map_word19]

def word21 (a b : G) : G :=
  (word20 a b) * (word20 a b) * (word20 a b) * (word20 a b) * (word20 a b) * (word20 a b) * (word20 a b) * (word17 a b) * (word17 a b) * (word17 a b)

theorem map_word21 (f : G →* H) (a b : G) :
    f (word21 a b) = word21 (f a) (f b) := by
  simp only [word21, map_mul, map_word17, map_word20]

def word22 (a b : G) : G :=
  (word17 a b) * (word20 a b) * (word20 a b) * (word17 a b) * (word20 a b) * (word20 a b) * (word20 a b) * (word20 a b) * (word17 a b) * (word17 a b) * (word20 a b)

theorem map_word22 (f : G →* H) (a b : G) :
    f (word22 a b) = word22 (f a) (f b) := by
  simp only [word22, map_mul, map_word17, map_word20]

def word23 (a b : G) : G :=
  (word21 a b) * (word17 a b) * (word22 a b)⁻¹

theorem map_word23 (f : G →* H) (a b : G) :
    f (word23 a b) = word23 (f a) (f b) := by
  simp only [word23, map_mul, map_inv, map_word17, map_word21, map_word22]

def word24 (a b : G) : G :=
  (word17 a b) * (word17 a b) * (word17 a b) * (word20 a b) * (word20 a b) * (word20 a b) * (word17 a b) * (word20 a b) * (word20 a b) * (word20 a b)

theorem map_word24 (f : G →* H) (a b : G) :
    f (word24 a b) = word24 (f a) (f b) := by
  simp only [word24, map_mul, map_word17, map_word20]

def word25 (a b : G) : G :=
  (word17 a b) * (word20 a b) * (word17 a b) * (word17 a b) * (word17 a b) * (word20 a b)

theorem map_word25 (f : G →* H) (a b : G) :
    f (word25 a b) = word25 (f a) (f b) := by
  simp only [word25, map_mul, map_word17, map_word20]

def word26 (a b : G) : G :=
  (word24 a b) * (word17 a b) * (word25 a b)⁻¹

theorem map_word26 (f : G →* H) (a b : G) :
    f (word26 a b) = word26 (f a) (f b) := by
  simp only [word26, map_mul, map_inv, map_word17, map_word24, map_word25]

def word27 (a b : G) : G :=
  (word17 a b) * (word17 a b) * (word17 a b) * (word20 a b) * (word17 a b) * (word17 a b) * (word20 a b) * (word17 a b) * (word20 a b)

theorem map_word27 (f : G →* H) (a b : G) :
    f (word27 a b) = word27 (f a) (f b) := by
  simp only [word27, map_mul, map_word17, map_word20]

def word28 (a b : G) : G :=
  (word17 a b) * (word17 a b) * (word20 a b) * (word20 a b) * (word17 a b) * (word17 a b) * (word20 a b) * (word17 a b) * (word17 a b)

theorem map_word28 (f : G →* H) (a b : G) :
    f (word28 a b) = word28 (f a) (f b) := by
  simp only [word28, map_mul, map_word17, map_word20]

def word29 (a b : G) : G :=
  (word27 a b) * (word20 a b) * (word28 a b)⁻¹

theorem map_word29 (f : G →* H) (a b : G) :
    f (word29 a b) = word29 (f a) (f b) := by
  simp only [word29, map_mul, map_inv, map_word20, map_word27, map_word28]

def word30 (a b : G) : G :=
  (word17 a b) * (word20 a b) * (word20 a b) * (word17 a b) * (word17 a b) * (word20 a b) * (word17 a b) * (word20 a b) * (word17 a b)

theorem map_word30 (f : G →* H) (a b : G) :
    f (word30 a b) = word30 (f a) (f b) := by
  simp only [word30, map_mul, map_word17, map_word20]

def word31 (a b : G) : G :=
  (word20 a b) * (word17 a b) * (word20 a b) * (word17 a b) * (word20 a b) * (word20 a b)

theorem map_word31 (f : G →* H) (a b : G) :
    f (word31 a b) = word31 (f a) (f b) := by
  simp only [word31, map_mul, map_word17, map_word20]

def word32 (a b : G) : G :=
  (word30 a b) * (word17 a b) * (word31 a b)⁻¹

theorem map_word32 (f : G →* H) (a b : G) :
    f (word32 a b) = word32 (f a) (f b) := by
  simp only [word32, map_mul, map_inv, map_word17, map_word30, map_word31]

/-- The five literal generator lists at either end of the four reductions. -/
def generators (a b : G) : Fin 5 → List G
  | 0 => [a, b]
  | 1 => [word5 a b, word8 a b]
  | 2 => [word11 a b, word14 a b]
  | 3 => [word17 a b, word20 a b]
  | 4 => [word23 a b, word26 a b, word29 a b, word32 a b]

/-- Subgroups generated by the literal word lists. -/
def stage (a b : G) (i : Fin 5) : Subgroup G :=
  Subgroup.closure {g | g ∈ generators a b i}

theorem map_generators (f : G →* H) (a b : G) (i : Fin 5) :
    (generators a b i).map f = generators (f a) (f b) i := by
  fin_cases i <;>
    simp only [generators, List.map_cons, List.map_nil, map_word5, map_word8,
      map_word11, map_word14, map_word17, map_word20, map_word23, map_word26,
      map_word29, map_word32]

theorem map_stage (f : G →* H) (a b : G) (i : Fin 5) :
    (stage a b i).map f = stage (f a) (f b) i := by
  simp only [stage, MonoidHom.map_closure]
  congr 1
  ext y
  rw [← map_generators f a b i]
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]

/-- Evaluate the four-letter alphabet used by the original `Base` module. -/
def evaluate (a b : G) (w : List (Fin 4)) : G :=
  (w.map fun i => if i = 0 then a else if i = 1 then b
    else if i = 2 then a⁻¹ else b⁻¹).prod

theorem map_evaluate (f : G →* H) (a b : G) (w : List (Fin 4)) :
    f (evaluate a b w) = evaluate (f a) (f b) w := by
  simp only [evaluate, map_list_prod, List.map_map, Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  split
  · rfl
  · split
    · rfl
    · split <;> exact map_inv f _

/-- The first four exact base words, using the original alphabet. -/
def baseWord : Fin 4 → List (Fin 4)
  | 0 => []
  | 1 => [2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2]
  | 2 => [3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2]
  | 3 => [2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.Word
