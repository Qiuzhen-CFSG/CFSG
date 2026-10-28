module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Data
public import Theory.GroupTheory.CosetWordCertificate

/-!
# Explicit auxiliary presentations for the max2 finite bound

GAP's multistage presentation run gives a seven-generator candidate stabilizer
with 16 short relators, followed by presentations on three and two generators.
The top run reproduces the 29 published words exactly. Every word below retains
ordinary multiplication order, without reversal. See `source/levels.json` and
`source/README.md` for the untrusted discovery and its source attribution.

The subgroup generators live in the actual abstract parent presentations.
The relation-lifting predicates and coset covers are independent proof obligations;
no permutation order or presentation claim from GAP is used as a hypothesis.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound
open Subgroup.CosetWordCertificate

abbrev Level0 := Group

def level0Relator : Fin 29 → Word Bool := relatorLetters

private theorem defining_relator {α β : Type*} (r : β → Word α) (i : β) :
    eval (PresentedGroup.of : α → PresentedGroup (Set.range (fun j => FreeGroup.mk (r j))))
      (r i) = 1 := by
  have h := FreeGroup.lift_unique
    (f := (PresentedGroup.of : α → PresentedGroup (Set.range (fun j => FreeGroup.mk (r j)))))
    (PresentedGroup.mk (Set.range (fun j => FreeGroup.mk (r j))))
    (fun _ => rfl) (x := FreeGroup.mk (r i))
  change FreeGroup.lift PresentedGroup.of (FreeGroup.mk (r i)) = 1
  rw [← h]
  exact PresentedGroup.one_of_mem (Set.mem_range_self i)

theorem level0_relator (i : Fin 29) :
    eval (PresentedGroup.of : Bool → Level0) (level0Relator i) = 1 :=
  defining_relator level0Relator i

def level1Relator0 : Word (Fin 7) :=
  [(5, true), (5, true)]

def level1Relator1 : Word (Fin 7) :=
  [(6, true), (6, true)]

def level1Relator2 : Word (Fin 7) :=
  [(0, false), (1, true)]

def level1Relator3 : Word (Fin 7) :=
  [(0, false), (1, false), (0, false)]

def level1Relator4 : Word (Fin 7) :=
  [(3, false), (0, true), (3, false), (0, true)]

def level1Relator5 : Word (Fin 7) :=
  [(0, true), (5, true), (1, true), (5, true)]

def level1Relator6 : Word (Fin 7) :=
  [(0, true), (6, true), (1, false), (6, true)]

def level1Relator7 : Word (Fin 7) :=
  [(4, true), (4, true), (4, true), (4, true)]

def level1Relator8 : Word (Fin 7) :=
  [(2, false), (5, true), (2, false), (5, true)]

def level1Relator9 : Word (Fin 7) :=
  [(5, true), (6, true), (5, true), (6, true)]

def level1Relator10 : Word (Fin 7) :=
  [(2, false), (0, true), (2, false), (0, true)]

def level1Relator11 : Word (Fin 7) :=
  [(4, false), (3, true), (5, true), (2, false), (6, true)]

def level1Relator12 : Word (Fin 7) :=
  [(2, false), (3, true), (2, false), (3, false), (0, false)]

def level1Relator13 : Word (Fin 7) :=
  [(2, true), (0, true), (4, true), (3, true), (6, true), (5, true)]

def level1Relator14 : Word (Fin 7) :=
  [(3, true), (4, false), (2, true), (3, true), (0, false), (2, true), (6, true)]

def level1Relator15 : Word (Fin 7) :=
  [(2, true), (4, false), (5, true), (1, false), (4, true), (2, false), (6, true)]

def level1Relator (i : Fin 16) : Word (Fin 7) :=
  Vector.get #v[level1Relator0, level1Relator1, level1Relator2, level1Relator3, level1Relator4, level1Relator5, level1Relator6, level1Relator7, level1Relator8, level1Relator9, level1Relator10, level1Relator11, level1Relator12, level1Relator13, level1Relator14, level1Relator15] i

def level1RelatorWord (i : Fin 16) : FreeGroup (Fin 7) :=
  FreeGroup.mk (level1Relator i)

abbrev Level1 := PresentedGroup (Set.range level1RelatorWord)

theorem level1_relator (i : Fin 16) :
    eval (PresentedGroup.of : Fin 7 → Level1) (level1Relator i) = 1 :=
  defining_relator level1Relator i

def level2Relator0 : Word (Fin 3) :=
  [(1, true), (1, true)]

def level2Relator1 : Word (Fin 3) :=
  [(2, true), (2, true)]

def level2Relator2 : Word (Fin 3) :=
  [(0, true), (0, true), (0, true)]

def level2Relator3 : Word (Fin 3) :=
  [(0, true), (2, true), (0, false), (2, true)]

def level2Relator4 : Word (Fin 3) :=
  [(0, false), (1, true), (0, false), (1, true)]

def level2Relator5 : Word (Fin 3) :=
  [(1, true), (2, true), (1, true), (2, true)]

def level2Relator (i : Fin 6) : Word (Fin 3) :=
  Vector.get #v[level2Relator0, level2Relator1, level2Relator2, level2Relator3, level2Relator4, level2Relator5] i

def level2RelatorWord (i : Fin 6) : FreeGroup (Fin 3) :=
  FreeGroup.mk (level2Relator i)

abbrev Level2 := PresentedGroup (Set.range level2RelatorWord)

theorem level2_relator (i : Fin 6) :
    eval (PresentedGroup.of : Fin 3 → Level2) (level2Relator i) = 1 :=
  defining_relator level2Relator i

def level3Relator0 : Word (Fin 2) :=
  [(0, true), (0, true)]

def level3Relator1 : Word (Fin 2) :=
  [(1, true), (1, true)]

def level3Relator2 : Word (Fin 2) :=
  [(0, true), (1, true), (0, true), (1, true)]

def level3Relator (i : Fin 3) : Word (Fin 2) :=
  Vector.get #v[level3Relator0, level3Relator1, level3Relator2] i

def level3RelatorWord (i : Fin 3) : FreeGroup (Fin 2) :=
  FreeGroup.mk (level3Relator i)

abbrev Level3 := PresentedGroup (Set.range level3RelatorWord)

theorem level3_relator (i : Fin 3) :
    eval (PresentedGroup.of : Fin 2 → Level3) (level3Relator i) = 1 :=
  defining_relator level3Relator i

def level0ChildWord0 : Word (Bool) :=
  [(true, true)]

def level0ChildWord1 : Word (Bool) :=
  [(true, true), (false, true), (false, true)]

def level0ChildWord2 : Word (Bool) :=
  [(true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false)]

def level0ChildWord3 : Word (Bool) :=
  [(true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false)]

def level0ChildWord4 : Word (Bool) :=
  [(false, true), (false, true), (true, true), (false, true), (false, true), (false, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true)]

def level0ChildWord5 : Word (Bool) :=
  [(true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true)]

def level0ChildWord6 : Word (Bool) :=
  [(true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false)]

def level0ChildWord (i : Fin 7) : Word (Bool) :=
  Vector.get #v[level0ChildWord0, level0ChildWord1, level0ChildWord2, level0ChildWord3, level0ChildWord4, level0ChildWord5, level0ChildWord6] i

def level0Generator (i : Fin 7) : Level0 :=
  eval PresentedGroup.of (level0ChildWord i)

def level0Subgroup : Subgroup Level0 := Subgroup.closure (Set.range level0Generator)

theorem level0Generator_mem (i : Fin 7) : level0Generator i ∈ level0Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- The next presentation maps to the named subgroup once these equations are proved. -/
def LiftedRelations01 : Prop :=
  ∀ i : Fin 16, eval level0Generator (level1Relator i) = 1

def level1ChildWord0 : Word (Fin 7) :=
  [(0, true)]

def level1ChildWord1 : Word (Fin 7) :=
  [(5, true)]

def level1ChildWord2 : Word (Fin 7) :=
  [(6, true)]

def level1ChildWord (i : Fin 3) : Word (Fin 7) :=
  Vector.get #v[level1ChildWord0, level1ChildWord1, level1ChildWord2] i

def level1Generator (i : Fin 3) : Level1 :=
  eval PresentedGroup.of (level1ChildWord i)

def level1Subgroup : Subgroup Level1 := Subgroup.closure (Set.range level1Generator)

theorem level1Generator_mem (i : Fin 3) : level1Generator i ∈ level1Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- The next presentation maps to the named subgroup once these equations are proved. -/
def LiftedRelations12 : Prop :=
  ∀ i : Fin 6, eval level1Generator (level2Relator i) = 1

def level2ChildWord0 : Word (Fin 3) :=
  [(1, true)]

def level2ChildWord1 : Word (Fin 3) :=
  [(2, true)]

def level2ChildWord (i : Fin 2) : Word (Fin 3) :=
  Vector.get #v[level2ChildWord0, level2ChildWord1] i

def level2Generator (i : Fin 2) : Level2 :=
  eval PresentedGroup.of (level2ChildWord i)

def level2Subgroup : Subgroup Level2 := Subgroup.closure (Set.range level2Generator)

theorem level2Generator_mem (i : Fin 2) : level2Generator i ∈ level2Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- The next presentation maps to the named subgroup once these equations are proved. -/
def LiftedRelations23 : Prop :=
  ∀ i : Fin 3, eval level2Generator (level3Relator i) = 1

def level3Subgroup : Subgroup Level3 := ⊥

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound
