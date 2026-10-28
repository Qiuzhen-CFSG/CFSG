module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Base
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.StabilizerWords
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Data
public import Theory.GroupAction.GeneratorStabilizerReduction

/-!
# Literal word semantics for the final four Fi₂₃ lift certificates

The stage generators are exactly the shared `StabilizerWords` elements, with
identity padding. We prove generation, membership of every factor word, and
the action of each representative from the finite generator-action checks.
Every next-stage generator occurs as a singleton factor in a checked table
position. The transition equality at that position proves it fixes the base.

`StepIdentities`, `BaseIdentities`, and `PointIdentities` are the remaining
finite computations, not assumed stabilizer conclusions. Source: ATLAS
F24G1-p306936B0 and GLS3 Table 5.3v; see `LastFour/source/README.md`.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour
open StabilizerWords

def generator : Fin 5 → Fin 4 → Carrier
  | 0 => ![word23.val, word26.val, word29.val, word32.val]
  | 1 => ![word35.val, word38.val, word41.val, 1]
  | 2 => ![word44.val, word47.val, 1, 1]
  | 3 => ![word50.val, 1, 1, 1]
  | 4 => ![1, 1, 1, 1]

private theorem mem_wordStage (i : Fin 9) (w : liftedGroup)
    (h : w ∈ StabilizerWords.generators i) : w.val ∈ wordStage i :=
  Subgroup.subset_closure (List.mem_map.mpr ⟨w, h, rfl⟩)

theorem generator_mem (i : Fin 5) (a : Fin 4) :
    generator i a ∈ wordStage (i.natAdd 4) := by
  fin_cases i <;> fin_cases a
  · exact mem_wordStage _ _ List.mem_cons_self
  · exact mem_wordStage _ _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact mem_wordStage _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact mem_wordStage _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact mem_wordStage _ _ List.mem_cons_self
  · exact mem_wordStage _ _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact mem_wordStage _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact Subgroup.one_mem _
  · exact mem_wordStage _ _ List.mem_cons_self
  · exact mem_wordStage _ _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact Subgroup.one_mem _
  · exact Subgroup.one_mem _
  · exact mem_wordStage _ _ List.mem_cons_self
  · exact Subgroup.one_mem _
  · exact Subgroup.one_mem _
  · exact Subgroup.one_mem _
  · exact Subgroup.one_mem _
  · exact Subgroup.one_mem _
  · exact Subgroup.one_mem _
  · exact Subgroup.one_mem _

theorem generated (i : Fin 5) :
    Subgroup.closure (Set.range (generator i)) = wordStage (i.natAdd 4) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    exact generator_mem i a
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    fin_cases i <;>
      simp only [StabilizerWords.generators, Fin.natAdd, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
    · rcases hg with rfl | rfl | rfl | rfl
      · exact Subgroup.subset_closure ⟨0, rfl⟩
      · exact Subgroup.subset_closure ⟨1, rfl⟩
      · exact Subgroup.subset_closure ⟨2, rfl⟩
      · exact Subgroup.subset_closure ⟨3, rfl⟩
    · rcases hg with rfl | rfl | rfl
      · exact Subgroup.subset_closure ⟨0, rfl⟩
      · exact Subgroup.subset_closure ⟨1, rfl⟩
      · exact Subgroup.subset_closure ⟨2, rfl⟩
    · rcases hg with rfl | rfl
      · exact Subgroup.subset_closure ⟨0, rfl⟩
      · exact Subgroup.subset_closure ⟨1, rfl⟩
    · rcases hg with rfl
      exact Subgroup.subset_closure ⟨0, rfl⟩

def evaluate (i : Fin 5) (w : List (Fin 4)) : Carrier :=
  (w.map (generator i)).prod

theorem evaluate_mem (i : Fin 5) (w : List (Fin 4)) :
    evaluate i w ∈ wordStage (i.natAdd 4) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
  exact generator_mem i a

def representative (i : Fin 4) (j : Fin (orbitSize i)) : Carrier :=
  evaluate i.castSucc (representativeWord i j)

def factor (i : Fin 4) (a : Fin 4) (j : Fin (orbitSize i)) : Carrier :=
  evaluate i.succ (factorWord i a j)

theorem factor_mem (i : Fin 4) (a : Fin 4) (j : Fin (orbitSize i)) :
    factor i a j ∈ wordStage (i.natAdd 4).succ := evaluate_mem i.succ _

theorem representative_initial (i : Fin 4) : representative i (initial i) = 1 := by
  simp [representative, representativeWord_initial, evaluate]

theorem evaluate_nextLetterWord (i : Fin 4) (a : Fin 4) :
    evaluate i.succ (nextLetterWord i a) = generator i.succ a := by
  fin_cases i <;> fin_cases a <;> simp [nextLetterWord, evaluate, generator]

/-- The remaining global permutation equalities; no action restriction is used. -/
def StepIdentities : Prop := ∀ i a j,
  generator i.castSucc a * representative i j =
    representative i (transitionIndex i a j) * factor i a j

/-- The four word-defined points have these numerical labels. -/
def BaseIdentities : Prop := ∀ i : Fin 4,
  basePoint (i.natAdd 4) = orbitPoint i (initial i)

/-- Only the displayed finite orbit sets enter these point checks. -/
def PointIdentities : Prop := ∀ i a j,
  (generator i.castSucc a).val (orbitPoint i j) =
    orbitPoint i (transitionIndex i a j)

theorem evaluate_apply_orbitPoint (points : PointIdentities) (i : Fin 4)
    (w : List (Fin 4)) (j : Fin (orbitSize i)) :
    (evaluate i.castSucc w).val (orbitPoint i j) = orbitPoint i (walk i w j) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (generator i.castSucc a).val ((evaluate i.castSucc w).val (orbitPoint i j)) = _
    rw [ih]
    exact points i a (walk i w j)

theorem representative_apply (bases : BaseIdentities) (points : PointIdentities)
    (i : Fin 4) (j : Fin (orbitSize i)) :
    (representative i j).val (basePoint (i.natAdd 4)) = orbitPoint i j := by
  rw [bases i]
  exact (evaluate_apply_orbitPoint points i _ _).trans
    (congrArg (orbitPoint i) (representativeWord_walk i j))

theorem generator_next_fixes (steps : StepIdentities) (bases : BaseIdentities)
    (points : PointIdentities) (i : Fin 4) (a : Fin 4) :
    (generator i.succ a).val (basePoint (i.natAdd 4)) = basePoint (i.natAdd 4) := by
  let b := factorSourceGenerator i a
  let j := factorSourceIndex i a
  have hf : factor i b j = generator i.succ a := by
    exact (congrArg (evaluate i.succ) (factorSource_spec i a)).trans
      (evaluate_nextLetterWord i a)
  have he := congrArg (fun g : Carrier => g.val (basePoint (i.natAdd 4))) (steps i b j)
  change (generator i.castSucc b).val ((representative i j).val (basePoint (i.natAdd 4))) =
    (representative i (transitionIndex i b j)).val
      ((factor i b j).val (basePoint (i.natAdd 4))) at he
  rw [representative_apply bases points, points i b j, hf] at he
  apply (representative i (transitionIndex i b j)).val.injective
  exact he.symm.trans (representative_apply bases points i _).symm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour
