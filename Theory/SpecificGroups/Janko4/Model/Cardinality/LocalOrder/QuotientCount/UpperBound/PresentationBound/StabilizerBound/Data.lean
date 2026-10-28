module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.FirstStabilizer

/-!
# Recursive presentations below the ten-generator stabilizer

The data come from `../source/levels.json`, entries 1 through 5, produced by
GAP's multistage presentation algorithm; see that directory's README and
`extract.g` for provenance. Each GAP word is reversed, retaining its signs.
`source/generate_data.py` reproduces this module.

These are abstract presentations and subgroups of them. The permutation images
and their computed orders supply no mathematical assumptions. The relation
lifting contracts and coset covers are independent obligations. Together they
permit descending bounds along the proposed indices 23, 22, 21, 20, and 16.
-/

@[expose] public section
namespace Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.StabilizerChain
open Subgroup.CosetWordCertificate

abbrev Level1 := StabilizerPresentation

/-- Defining words vanish in their abstract presentation. -/
theorem defining_relator {α β : Type*} (r : β → Word α) (i : β) :
    eval (PresentedGroup.of : α → PresentedGroup (Set.range (fun j => FreeGroup.mk (r j))))
      (r i) = 1 := by
  have h := FreeGroup.lift_unique
    (f := (PresentedGroup.of : α → PresentedGroup (Set.range (fun j => FreeGroup.mk (r j)))))
    (PresentedGroup.mk (Set.range (fun j => FreeGroup.mk (r j))))
    (fun _ => rfl) (x := FreeGroup.mk (r i))
  change FreeGroup.lift PresentedGroup.of (FreeGroup.mk (r i)) = 1
  rw [← h]
  exact PresentedGroup.one_of_mem (Set.mem_range_self i)

theorem level1_relator (i : Fin 43) :
    eval (PresentedGroup.of : Fin 10 → Level1) (stabilizerRelator i) = 1 :=
  defining_relator stabilizerRelator i

def level2Relator0 : Word (Fin 8) :=
  [(6, true), (6, true)]

def level2Relator1 : Word (Fin 8) :=
  [(2, false), (0, true)]

def level2Relator2 : Word (Fin 8) :=
  [(5, true), (5, true), (5, true)]

def level2Relator3 : Word (Fin 8) :=
  [(7, true), (7, true), (7, true)]

def level2Relator4 : Word (Fin 8) :=
  [(0, true), (2, true), (0, true), (2, true)]

def level2Relator5 : Word (Fin 8) :=
  [(5, true), (3, false), (4, false), (4, false)]

def level2Relator6 : Word (Fin 8) :=
  [(7, true), (5, false), (7, true), (5, false)]

def level2Relator7 : Word (Fin 8) :=
  [(4, true), (4, true), (4, true), (5, true), (3, false)]

def level2Relator8 : Word (Fin 8) :=
  [(6, true), (4, false), (6, true), (7, false), (0, true), (2, true)]

def level2Relator9 : Word (Fin 8) :=
  [(7, false), (5, true), (6, true), (5, false), (7, true), (6, true)]

def level2Relator10 : Word (Fin 8) :=
  [(5, true), (7, false), (6, true), (7, true), (5, false), (6, true)]

def level2Relator11 : Word (Fin 8) :=
  [(6, true), (7, true), (0, true), (2, true), (5, false), (3, false)]

def level2Relator12 : Word (Fin 8) :=
  [(4, false), (0, true), (2, true), (7, true), (4, false), (6, true)]

def level2Relator13 : Word (Fin 8) :=
  [(7, false), (0, true), (1, true), (7, false), (0, true), (1, true)]

def level2Relator14 : Word (Fin 8) :=
  [(6, true), (5, false), (6, true), (5, false), (6, true), (5, false)]

def level2Relator15 : Word (Fin 8) :=
  [(0, true), (2, true), (6, true), (5, false), (7, true), (3, true), (4, true)]

def level2Relator16 : Word (Fin 8) :=
  [(6, true), (5, false), (0, true), (1, true), (5, false), (0, true), (1, true)]

def level2Relator17 : Word (Fin 8) :=
  [(3, false), (3, false), (7, false), (0, false), (5, true), (4, false), (0, true)]

def level2Relator18 : Word (Fin 8) :=
  [(0, false), (5, false), (7, true), (6, true), (0, false), (3, true), (0, true), (5, true)]

def level2Relator19 : Word (Fin 8) :=
  [(7, false), (6, true), (0, true), (3, false), (1, false), (7, true), (1, true), (1, true)]

def level2Relator20 : Word (Fin 8) :=
  [(7, false), (5, false), (6, true), (0, true), (3, false), (5, false), (3, true), (0, true)]

def level2Relator21 : Word (Fin 8) :=
  [(6, true), (0, true), (3, false), (2, false), (1, true), (5, false), (0, false), (3, true), (1, true)]

def level2Relator22 : Word (Fin 8) :=
  [(3, false), (5, true), (7, false), (0, false), (3, false), (4, false), (1, true), (7, true), (5, false), (1, false)]

def level2Relator23 : Word (Fin 8) :=
  [(5, false), (6, true), (7, false), (3, false), (0, true), (3, false), (0, true), (2, true), (4, false), (0, true)]

def level2Relator24 : Word (Fin 8) :=
  [(7, false), (6, true), (7, false), (3, false), (0, false), (6, true), (1, true), (3, false), (0, true), (1, false)]

def level2Relator25 : Word (Fin 8) :=
  [(4, false), (0, true), (3, true), (6, true), (4, false), (6, true), (5, false), (1, false), (6, true), (4, false), (1, true)]

def level2Relator26 : Word (Fin 8) :=
  [(7, false), (5, false), (7, false), (4, false), (0, false), (4, true), (7, false), (1, false), (5, false), (0, false), (1, true)]

def level2Relator27 : Word (Fin 8) :=
  [(5, true), (3, false), (0, true), (3, false), (3, false), (7, true), (6, true), (5, false), (1, true), (4, true), (5, false), (1, true)]

def level2Relator28 : Word (Fin 8) :=
  [(6, true), (7, false), (2, false), (0, false), (3, true), (5, true), (0, false), (6, true), (1, false), (7, false), (3, false), (1, true)]

def level2Relator (i : Fin 29) : Word (Fin 8) :=
  Vector.get #v[level2Relator0, level2Relator1, level2Relator2, level2Relator3, level2Relator4, level2Relator5, level2Relator6, level2Relator7, level2Relator8, level2Relator9, level2Relator10, level2Relator11, level2Relator12, level2Relator13, level2Relator14, level2Relator15, level2Relator16, level2Relator17, level2Relator18, level2Relator19, level2Relator20, level2Relator21, level2Relator22, level2Relator23, level2Relator24, level2Relator25, level2Relator26, level2Relator27, level2Relator28] i

def level2RelatorWord (i : Fin 29) : FreeGroup (Fin 8) :=
  FreeGroup.mk (level2Relator i)

abbrev Level2 := PresentedGroup (Set.range level2RelatorWord)

theorem level2_relator (i : Fin 29) :
    eval (PresentedGroup.of : Fin 8 → Level2) (level2Relator i) = 1 :=
  defining_relator level2Relator i

def level3Relator0 : Word (Fin 7) :=
  [(5, true), (5, true)]

def level3Relator1 : Word (Fin 7) :=
  [(1, true), (1, true)]

def level3Relator2 : Word (Fin 7) :=
  [(0, true), (0, true), (1, true)]

def level3Relator3 : Word (Fin 7) :=
  [(4, true), (4, true), (4, true)]

def level3Relator4 : Word (Fin 7) :=
  [(6, true), (6, true), (6, true)]

def level3Relator5 : Word (Fin 7) :=
  [(4, true), (2, false), (3, false), (3, false)]

def level3Relator6 : Word (Fin 7) :=
  [(6, true), (4, false), (6, true), (4, false)]

def level3Relator7 : Word (Fin 7) :=
  [(3, true), (3, true), (3, true), (4, true), (2, false)]

def level3Relator8 : Word (Fin 7) :=
  [(5, true), (6, false), (1, true), (5, true), (3, false)]

def level3Relator9 : Word (Fin 7) :=
  [(5, true), (6, true), (1, true), (4, false), (2, false)]

def level3Relator10 : Word (Fin 7) :=
  [(3, false), (1, true), (6, true), (3, false), (5, true)]

def level3Relator11 : Word (Fin 7) :=
  [(6, false), (4, true), (5, true), (1, true), (3, false), (2, false)]

def level3Relator12 : Word (Fin 7) :=
  [(1, true), (6, false), (4, true), (5, true), (2, true), (3, true)]

def level3Relator13 : Word (Fin 7) :=
  [(1, true), (6, true), (4, true), (1, true), (3, true), (2, true)]

def level3Relator14 : Word (Fin 7) :=
  [(4, true), (6, false), (5, true), (6, true), (4, false), (5, true)]

def level3Relator15 : Word (Fin 7) :=
  [(5, true), (4, false), (5, true), (4, false), (5, true), (4, false)]

def level3Relator16 : Word (Fin 7) :=
  [(2, false), (2, false), (6, false), (0, false), (4, true), (3, false), (0, true)]

def level3Relator17 : Word (Fin 7) :=
  [(0, false), (5, true), (6, false), (4, true), (0, false), (2, true), (0, true), (4, true)]

def level3Relator18 : Word (Fin 7) :=
  [(6, false), (4, false), (5, true), (0, true), (2, false), (4, false), (2, true), (0, true)]

def level3Relator19 : Word (Fin 7) :=
  [(4, false), (5, true), (6, false), (2, false), (0, true), (2, false), (1, true), (3, false), (0, true)]

def level3Relator (i : Fin 20) : Word (Fin 7) :=
  Vector.get #v[level3Relator0, level3Relator1, level3Relator2, level3Relator3, level3Relator4, level3Relator5, level3Relator6, level3Relator7, level3Relator8, level3Relator9, level3Relator10, level3Relator11, level3Relator12, level3Relator13, level3Relator14, level3Relator15, level3Relator16, level3Relator17, level3Relator18, level3Relator19] i

def level3RelatorWord (i : Fin 20) : FreeGroup (Fin 7) :=
  FreeGroup.mk (level3Relator i)

abbrev Level3 := PresentedGroup (Set.range level3RelatorWord)

theorem level3_relator (i : Fin 20) :
    eval (PresentedGroup.of : Fin 7 → Level3) (level3Relator i) = 1 :=
  defining_relator level3Relator i

def level4Relator0 : Word (Fin 6) :=
  [(4, true), (4, true)]

def level4Relator1 : Word (Fin 6) :=
  [(0, true), (0, true)]

def level4Relator2 : Word (Fin 6) :=
  [(3, true), (3, true), (3, true)]

def level4Relator3 : Word (Fin 6) :=
  [(5, true), (5, true), (5, true)]

def level4Relator4 : Word (Fin 6) :=
  [(3, true), (1, false), (2, false), (2, false)]

def level4Relator5 : Word (Fin 6) :=
  [(5, true), (3, false), (5, true), (3, false)]

def level4Relator6 : Word (Fin 6) :=
  [(2, true), (2, true), (2, true), (2, true), (2, true)]

def level4Relator7 : Word (Fin 6) :=
  [(4, true), (5, false), (0, true), (4, true), (2, false)]

def level4Relator8 : Word (Fin 6) :=
  [(4, true), (5, true), (0, true), (3, false), (1, false)]

def level4Relator9 : Word (Fin 6) :=
  [(2, false), (0, true), (5, true), (2, false), (4, true)]

def level4Relator10 : Word (Fin 6) :=
  [(5, true), (3, true), (0, true), (2, false), (3, true), (0, true)]

def level4Relator11 : Word (Fin 6) :=
  [(3, true), (5, false), (4, true), (3, true), (5, false), (4, true)]

def level4Relator12 : Word (Fin 6) :=
  [(3, false), (5, true), (4, true), (0, true), (2, false), (1, false)]

def level4Relator13 : Word (Fin 6) :=
  [(1, true), (2, true), (0, true), (1, true), (2, true), (0, true)]

def level4Relator14 : Word (Fin 6) :=
  [(4, true), (3, false), (4, true), (3, false), (4, true), (3, false)]

def level4Relator (i : Fin 15) : Word (Fin 6) :=
  Vector.get #v[level4Relator0, level4Relator1, level4Relator2, level4Relator3, level4Relator4, level4Relator5, level4Relator6, level4Relator7, level4Relator8, level4Relator9, level4Relator10, level4Relator11, level4Relator12, level4Relator13, level4Relator14] i

def level4RelatorWord (i : Fin 15) : FreeGroup (Fin 6) :=
  FreeGroup.mk (level4Relator i)

abbrev Level4 := PresentedGroup (Set.range level4RelatorWord)

theorem level4_relator (i : Fin 15) :
    eval (PresentedGroup.of : Fin 6 → Level4) (level4Relator i) = 1 :=
  defining_relator level4Relator i

def level5Relator0 : Word (Fin 3) :=
  [(1, true), (1, true)]

def level5Relator1 : Word (Fin 3) :=
  [(0, true), (0, true), (0, true)]

def level5Relator2 : Word (Fin 3) :=
  [(2, true), (2, true), (2, true)]

def level5Relator3 : Word (Fin 3) :=
  [(2, true), (0, false), (2, true), (0, false)]

def level5Relator4 : Word (Fin 3) :=
  [(2, false), (0, true), (1, true), (2, false), (0, true), (1, true)]

def level5Relator5 : Word (Fin 3) :=
  [(0, true), (2, false), (1, true), (2, true), (0, false), (1, true)]

def level5Relator6 : Word (Fin 3) :=
  [(1, true), (0, false), (1, true), (0, false), (1, true), (0, false)]

def level5Relator (i : Fin 7) : Word (Fin 3) :=
  Vector.get #v[level5Relator0, level5Relator1, level5Relator2, level5Relator3, level5Relator4, level5Relator5, level5Relator6] i

def level5RelatorWord (i : Fin 7) : FreeGroup (Fin 3) :=
  FreeGroup.mk (level5Relator i)

abbrev Level5 := PresentedGroup (Set.range level5RelatorWord)

theorem level5_relator (i : Fin 7) :
    eval (PresentedGroup.of : Fin 3 → Level5) (level5Relator i) = 1 :=
  defining_relator level5Relator i

def level1ChildWord (i : Fin 8) : Word (Fin 10) :=
  Vector.get #v[[(2, true)], [(3, true)], [(4, true)], [(5, true)], [(6, true)], [(7, true)], [(8, true)], [(9, true)]] i

def level1Generator (i : Fin 8) : Level1 :=
  eval PresentedGroup.of (level1ChildWord i)

def level1Subgroup : Subgroup Level1 := Subgroup.closure (Set.range level1Generator)

theorem level1Generator_mem (i : Fin 8) : level1Generator i ∈ level1Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- Relations required to map the next presentation into this subgroup. -/
def LiftedRelations12 : Prop :=
  ∀ i : Fin 29, eval level1Generator (level2Relator i) = 1

def level2ChildWord (i : Fin 7) : Word (Fin 8) :=
  Vector.get #v[[(0, true)], [(0, true), (2, true)], [(3, true)], [(4, true)], [(5, true)], [(6, true)], [(7, true)]] i

def level2Generator (i : Fin 7) : Level2 :=
  eval PresentedGroup.of (level2ChildWord i)

def level2Subgroup : Subgroup Level2 := Subgroup.closure (Set.range level2Generator)

theorem level2Generator_mem (i : Fin 7) : level2Generator i ∈ level2Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- Relations required to map the next presentation into this subgroup. -/
def LiftedRelations23 : Prop :=
  ∀ i : Fin 20, eval level2Generator (level3Relator i) = 1

def level3ChildWord (i : Fin 6) : Word (Fin 7) :=
  Vector.get #v[[(0, true), (0, true)], [(2, true)], [(3, true)], [(4, true)], [(5, true)], [(6, true)]] i

def level3Generator (i : Fin 6) : Level3 :=
  eval PresentedGroup.of (level3ChildWord i)

def level3Subgroup : Subgroup Level3 := Subgroup.closure (Set.range level3Generator)

theorem level3Generator_mem (i : Fin 6) : level3Generator i ∈ level3Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- Relations required to map the next presentation into this subgroup. -/
def LiftedRelations34 : Prop :=
  ∀ i : Fin 15, eval level3Generator (level4Relator i) = 1

def level4ChildWord (i : Fin 3) : Word (Fin 6) :=
  Vector.get #v[[(3, true)], [(4, true)], [(5, true)]] i

def level4Generator (i : Fin 3) : Level4 :=
  eval PresentedGroup.of (level4ChildWord i)

def level4Subgroup : Subgroup Level4 := Subgroup.closure (Set.range level4Generator)

theorem level4Generator_mem (i : Fin 3) : level4Generator i ∈ level4Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- Relations required to map the next presentation into this subgroup. -/
def LiftedRelations45 : Prop :=
  ∀ i : Fin 7, eval level4Generator (level5Relator i) = 1

def level5ChildWord (i : Fin 1) : Word (Fin 3) :=
  Vector.get #v[[(2, true)]] i

def level5Generator (i : Fin 1) : Level5 :=
  eval PresentedGroup.of (level5ChildWord i)

def level5Subgroup : Subgroup Level5 := Subgroup.closure (Set.range level5Generator)

theorem level5Generator_mem (i : Fin 1) : level5Generator i ∈ level5Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

end Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.StabilizerChain
