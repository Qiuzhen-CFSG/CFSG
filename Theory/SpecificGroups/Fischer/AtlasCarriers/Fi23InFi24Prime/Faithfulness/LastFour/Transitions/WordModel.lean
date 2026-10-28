module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Setup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.Model

/-!
# Transport of all final-four stabilizer words

Words 33 through 50 extend the existing polymorphic words through 32, with
exactly the formulas of `StabilizerWords`. Naturality under the two subgroup
inclusions compares every padded generator with the full-degree model, using
only the two original candidate-comparison hypotheses. No restriction action
or faithfulness premise enters this comparison.

Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v; the literal formulas and their
straight-line witnesses are in `StabilizerWords` and `source/faithfulness/nodes.json`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions
namespace Word
open FirstFourModel.Word
variable {G H : Type*} [Group G] [Group H]

def word33 (a b : G) : G :=
  (word23 a b) * (word32 a b)⁻¹ * (word23 a b)

theorem map_word33 (f : G →* H) (a b : G) :
    f (word33 a b) = word33 (f a) (f b) := by
  simp only [word33, map_mul, map_inv, map_word23, map_word32]

def word34 (a b : G) : G :=
  (word23 a b) * (word26 a b) * (word23 a b)

theorem map_word34 (f : G →* H) (a b : G) :
    f (word34 a b) = word34 (f a) (f b) := by
  simp only [word34, map_mul, map_word23, map_word26]

def word35 (a b : G) : G :=
  (word33 a b) * (word26 a b) * (word34 a b)⁻¹

theorem map_word35 (f : G →* H) (a b : G) :
    f (word35 a b) = word35 (f a) (f b) := by
  simp only [word35, map_mul, map_inv, map_word26, map_word33, map_word34]

def word36 (a b : G) : G :=
  (word23 a b) * (word26 a b) * (word23 a b)

theorem map_word36 (f : G →* H) (a b : G) :
    f (word36 a b) = word36 (f a) (f b) := by
  simp only [word36, map_mul, map_word23, map_word26]

def word37 (a b : G) : G :=
  (word23 a b) * (word32 a b)⁻¹

theorem map_word37 (f : G →* H) (a b : G) :
    f (word37 a b) = word37 (f a) (f b) := by
  simp only [word37, map_mul, map_inv, map_word23, map_word32]

def word38 (a b : G) : G :=
  (word36 a b) * (word29 a b) * (word37 a b)⁻¹

theorem map_word38 (f : G →* H) (a b : G) :
    f (word38 a b) = word38 (f a) (f b) := by
  simp only [word38, map_mul, map_inv, map_word29, map_word36, map_word37]

def word39 (a b : G) : G :=
  (word26 a b) * (word26 a b)

theorem map_word39 (f : G →* H) (a b : G) :
    f (word39 a b) = word39 (f a) (f b) := by
  simp only [word39, map_mul, map_word26]

def word40 (a b : G) : G :=
  (word26 a b) * (word23 a b) * (word29 a b)

theorem map_word40 (f : G →* H) (a b : G) :
    f (word40 a b) = word40 (f a) (f b) := by
  simp only [word40, map_mul, map_word23, map_word26, map_word29]

def word41 (a b : G) : G :=
  (word39 a b) * (word26 a b) * (word40 a b)⁻¹

theorem map_word41 (f : G →* H) (a b : G) :
    f (word41 a b) = word41 (f a) (f b) := by
  simp only [word41, map_mul, map_inv, map_word26, map_word39, map_word40]

def word42 (a b : G) : G :=
  (word38 a b) * (word41 a b)

theorem map_word42 (f : G →* H) (a b : G) :
    f (word42 a b) = word42 (f a) (f b) := by
  simp only [word42, map_mul, map_word38, map_word41]

def word43 (a b : G) : G :=
  (word41 a b) * (word38 a b)

theorem map_word43 (f : G →* H) (a b : G) :
    f (word43 a b) = word43 (f a) (f b) := by
  simp only [word43, map_mul, map_word38, map_word41]

def word44 (a b : G) : G :=
  (word42 a b) * (word35 a b) * (word43 a b)⁻¹

theorem map_word44 (f : G →* H) (a b : G) :
    f (word44 a b) = word44 (f a) (f b) := by
  simp only [word44, map_mul, map_inv, map_word35, map_word42, map_word43]

def word45 (a b : G) : G :=
  (word41 a b) * (word38 a b)

theorem map_word45 (f : G →* H) (a b : G) :
    f (word45 a b) = word45 (f a) (f b) := by
  simp only [word45, map_mul, map_word38, map_word41]

def word46 (a b : G) : G :=
  (word35 a b)

theorem map_word46 (f : G →* H) (a b : G) :
    f (word46 a b) = word46 (f a) (f b) := by
  simp only [word46, map_word35]

def word47 (a b : G) : G :=
  (word45 a b) * (word41 a b) * (word46 a b)⁻¹

theorem map_word47 (f : G →* H) (a b : G) :
    f (word47 a b) = word47 (f a) (f b) := by
  simp only [word47, map_mul, map_inv, map_word41, map_word45, map_word46]

def word48 (a b : G) : G :=
  (word47 a b)

theorem map_word48 (f : G →* H) (a b : G) :
    f (word48 a b) = word48 (f a) (f b) := by
  simp only [word48, map_word47]

def word49 (a b : G) : G :=
  (word47 a b)

theorem map_word49 (f : G →* H) (a b : G) :
    f (word49 a b) = word49 (f a) (f b) := by
  simp only [word49, map_word47]

def word50 (a b : G) : G :=
  (word48 a b) * (word44 a b) * (word49 a b)⁻¹

theorem map_word50 (f : G →* H) (a b : G) :
    f (word50 a b) = word50 (f a) (f b) := by
  simp only [word50, map_mul, map_inv, map_word44, map_word48, map_word49]

/-- The five padded lists, evaluated in any group. -/
def generator (a b : G) : Fin 5 → Fin 4 → G
  | 0 => ![word23 a b, word26 a b, word29 a b, word32 a b]
  | 1 => ![word35 a b, word38 a b, word41 a b, 1]
  | 2 => ![word44 a b, word47 a b, 1, 1]
  | 3 => ![word50 a b, 1, 1, 1]
  | 4 => ![1, 1, 1, 1]

theorem map_generator (f : G →* H) (a b : G) (i : Fin 5) (c : Fin 4) :
    f (generator a b i c) = generator (f a) (f b) i c := by
  fin_cases i <;> fin_cases c
  · exact map_word23 f a b
  · exact map_word26 f a b
  · exact map_word29 f a b
  · exact map_word32 f a b
  · exact map_word35 f a b
  · exact map_word38 f a b
  · exact map_word41 f a b
  · exact map_one f
  · exact map_word44 f a b
  · exact map_word47 f a b
  · exact map_one f
  · exact map_one f
  · exact map_word50 f a b
  · exact map_one f
  · exact map_one f
  · exact map_one f
  · exact map_one f
  · exact map_one f
  · exact map_one f
  · exact map_one f

end Word

/-- Specialization inside the literal lifted group agrees before any comparison. -/
theorem generator_actual (i : Fin 5) (c : Fin 4) :
    (Word.generator aLift bLift i c).val = LastFour.generator i c := by
  fin_cases i <;> fin_cases c <;> rfl

/-- The model permutations use the exact same final-four word formulas. -/
def modelGenerator : Fin 5 → Fin 4 → Equiv.Perm (Fin 306936) :=
  Word.generator FirstFourModel.aPerm FirstFourModel.bPerm

/-- Both subgroup inclusions preserve the words; comparison is on all letters. -/
theorem generator_val_of_compared_candidates
    (ha : candidateA.val = FirstFourModel.aPerm)
    (hb : candidateB.val = FirstFourModel.bPerm) (i : Fin 5) (c : Fin 4) :
    (LastFour.generator i c).val = modelGenerator i c := by
  rw [← generator_actual]
  have h₁ := Word.map_generator liftedGroup.subtype aLift bLift i c
  have h₂ := Word.map_generator Fi24Prime.generated.subtype candidateA candidateB i c
  change (Word.generator aLift bLift i c).val =
    Word.generator candidateA candidateB i c at h₁
  change (Word.generator candidateA candidateB i c).val =
    Word.generator candidateA.val candidateB.val i c at h₂
  rw [h₁, h₂, ha, hb]
  rfl

/-- Positive-word evaluation in the full ambient permutation model. -/
def modelEvaluate (i : Fin 5) (w : List (Fin 4)) : Equiv.Perm (Fin 306936) :=
  (w.map (modelGenerator i)).prod

theorem evaluate_val_of_compared_candidates
    (ha : candidateA.val = FirstFourModel.aPerm)
    (hb : candidateB.val = FirstFourModel.bPerm) (i : Fin 5) (w : List (Fin 4)) :
    (LastFour.evaluate i w).val = modelEvaluate i w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change (LastFour.generator i c).val * (LastFour.evaluate i w).val =
      modelGenerator i c * modelEvaluate i w
    rw [generator_val_of_compared_candidates ha hb, ih]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions
