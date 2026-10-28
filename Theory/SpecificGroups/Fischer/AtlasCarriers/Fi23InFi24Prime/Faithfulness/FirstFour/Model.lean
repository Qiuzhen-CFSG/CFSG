module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.InverseA
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.InverseB
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.Words
public import Theory.GroupAction.GeneratorStabilizerReduction

/-!
# A checked permutation model for the first four stabilizer reductions

The two packed functions are genuine permutations by their kernel-checked
square and cube identities. The stage groups use exactly the shared word
formulas. The four points are evaluated from the shared base words.
`WordBridge` transports a stabilizer certificate only after comparison with
the original candidate words on the entire ambient set.

This module does not assert that the model is the original lift, or that its
listed subgroups are point stabilizers. Source: ATLAS F24G1-p306936B0,
GLS3 Table 5.3v; reproducible packed data in `source/generate_model.py`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel

/-- The first packed function, with its checked inverse. -/
def aPerm : Equiv.Perm (Fin 306936) where
  toFun := imageA
  invFun := imageA
  left_inv := imageA_involutive
  right_inv := imageA_involutive

/-- The second packed function; its square is its checked inverse. -/
def bPerm : Equiv.Perm (Fin 306936) where
  toFun := imageB
  invFun := fun x => imageB (imageB x)
  left_inv := imageB_cube
  right_inv := imageB_cube

/-- The actual word-generated subgroups of the finite model. -/
abbrev stage (i : Fin 5) : Subgroup (Equiv.Perm (Fin 306936)) :=
  Word.stage aPerm bPerm i

/-- The model points are given by the same four orbit words. -/
def point (i : Fin 4) : Fin 306936 :=
  Word.evaluate aPerm bPerm (Word.baseWord i) 508

/-- The two generators at each of the first four stages. -/
def generators : Fin 4 → Fin 2 → Equiv.Perm (Fin 306936)
  | 0, 0 => aPerm
  | 0, 1 => bPerm
  | 1, 0 => Word.word5 aPerm bPerm
  | 1, 1 => Word.word8 aPerm bPerm
  | 2, 0 => Word.word11 aPerm bPerm
  | 2, 1 => Word.word14 aPerm bPerm
  | 3, 0 => Word.word17 aPerm bPerm
  | 3, 1 => Word.word20 aPerm bPerm

/-- The generator-indexing convention agrees with the literal stage lists. -/
theorem stage_generated (i : Fin 4) :
    Subgroup.closure (Set.range (generators i)) = stage i.castSucc := by
  fin_cases i <;> apply congrArg Subgroup.closure <;> ext g <;>
    simp [generators, Word.generators, Fin.exists_fin_two, eq_comm]

/-- An actual Schreier certificate supplies the required model inclusion. -/
theorem reduction_of_certificate {i : Fin 4} {I : Type*}
    (C : Subgroup.GeneratorStabilizerReduction (generators i) (stage i.succ) (point i) I)
    (g : Equiv.Perm (Fin 306936)) (hg : g ∈ stage i.castSucc)
    (hfix : g (point i) = point i) : g ∈ stage i.succ := by
  apply C.mem_next
  · rwa [stage_generated]
  · exact hfix

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
