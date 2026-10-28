module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.Data

/-!
# Recursive presentations below the twelve-relator M₁ presentation

The data come from `../source/levels.json`, entries 0 through 2, produced by
GAP's multistage presentation algorithm; see that directory's README and
`extract.g` for provenance. Each GAP word retains its order and signs.
`source/generate_data.py` reproduces this module.

These are abstract presentations and subgroups of them. The permutation images
and their computed orders supply no mathematical assumptions. The relation
lifting contracts and coset covers are independent obligations. Together they
permit descending bounds along the proposed indices 1360, 90, and 8.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBoundChain
open Subgroup.CosetWordCertificate

abbrev Level0 := LocalPresentation

abbrev level0Relator := relationLetters

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

theorem level0_relator (i : Fin 12) :
    eval (PresentedGroup.of : Fin 3 → Level0) (level0Relator i) = 1 :=
  defining_relator level0Relator i

def level1Relator0 : Word (Fin 7) :=
  [(4, true), (4, true)]

def level1Relator1 : Word (Fin 7) :=
  [(0, true), (0, true)]

def level1Relator2 : Word (Fin 7) :=
  [(2, true), (2, true)]

def level1Relator3 : Word (Fin 7) :=
  [(3, true), (3, true)]

def level1Relator4 : Word (Fin 7) :=
  [(5, true), (5, true)]

def level1Relator5 : Word (Fin 7) :=
  [(6, true), (6, true)]

def level1Relator6 : Word (Fin 7) :=
  [(1, true), (1, true)]

def level1Relator7 : Word (Fin 7) :=
  [(0, true), (3, true)]

def level1Relator8 : Word (Fin 7) :=
  [(0, true), (2, true)]

def level1Relator9 : Word (Fin 7) :=
  [(6, true), (5, true), (6, true), (5, true)]

def level1Relator10 : Word (Fin 7) :=
  [(0, true), (4, true), (0, true), (4, true)]

def level1Relator11 : Word (Fin 7) :=
  [(6, true), (4, true), (6, true), (4, true)]

def level1Relator12 : Word (Fin 7) :=
  [(5, true), (0, true), (5, true), (6, true), (4, true)]

def level1Relator13 : Word (Fin 7) :=
  [(1, true), (6, true), (1, true), (4, true), (1, true), (4, true)]

def level1Relator14 : Word (Fin 7) :=
  [(1, true), (0, true), (6, true), (1, true), (4, true), (0, true), (1, true), (0, true), (6, true), (1, true), (4, true), (0, true)]

def level1Relator15 : Word (Fin 7) :=
  [(6, true), (1, true), (5, true), (1, true), (6, true), (5, true), (1, true), (5, true), (4, true), (1, true), (5, true), (0, true), (1, true)]

def level1Relator16 : Word (Fin 7) :=
  [(1, true), (0, true), (1, true), (0, true), (1, true), (5, true), (1, true), (0, true), (1, true), (0, true), (1, true), (4, true), (5, true), (4, true)]

def level1Relator17 : Word (Fin 7) :=
  [(1, true), (0, true), (5, true), (1, true), (0, true), (5, true), (1, true), (5, true), (1, true), (5, true), (0, true), (1, true), (4, true), (5, true), (4, true)]

def level1Relator (i : Fin 18) : Word (Fin 7) :=
  Vector.get #v[level1Relator0, level1Relator1, level1Relator2, level1Relator3, level1Relator4, level1Relator5, level1Relator6, level1Relator7, level1Relator8, level1Relator9, level1Relator10, level1Relator11, level1Relator12, level1Relator13, level1Relator14, level1Relator15, level1Relator16, level1Relator17] i

def level1RelatorWord (i : Fin 18) : FreeGroup (Fin 7) :=
  FreeGroup.mk (level1Relator i)

abbrev Level1 := PresentedGroup (Set.range level1RelatorWord)

theorem level1_relator (i : Fin 18) :
    eval (PresentedGroup.of : Fin 7 → Level1) (level1Relator i) = 1 :=
  defining_relator level1Relator i

def level2Relator0 : Word (Fin 6) :=
  [(3, true), (3, true)]

def level2Relator1 : Word (Fin 6) :=
  [(0, true), (0, true)]

def level2Relator2 : Word (Fin 6) :=
  [(1, true), (1, true)]

def level2Relator3 : Word (Fin 6) :=
  [(2, true), (2, true)]

def level2Relator4 : Word (Fin 6) :=
  [(4, true), (4, true)]

def level2Relator5 : Word (Fin 6) :=
  [(5, true), (5, true)]

def level2Relator6 : Word (Fin 6) :=
  [(0, true), (2, true)]

def level2Relator7 : Word (Fin 6) :=
  [(0, true), (1, true)]

def level2Relator8 : Word (Fin 6) :=
  [(5, true), (4, true), (5, true), (4, true)]

def level2Relator9 : Word (Fin 6) :=
  [(5, true), (3, true), (5, true), (3, true)]

def level2Relator10 : Word (Fin 6) :=
  [(0, true), (3, true), (0, true), (3, true)]

def level2Relator11 : Word (Fin 6) :=
  [(4, true), (0, true), (5, true), (4, true), (3, true)]

def level2Relator (i : Fin 12) : Word (Fin 6) :=
  Vector.get #v[level2Relator0, level2Relator1, level2Relator2, level2Relator3, level2Relator4, level2Relator5, level2Relator6, level2Relator7, level2Relator8, level2Relator9, level2Relator10, level2Relator11] i

def level2RelatorWord (i : Fin 12) : FreeGroup (Fin 6) :=
  FreeGroup.mk (level2Relator i)

abbrev Level2 := PresentedGroup (Set.range level2RelatorWord)

theorem level2_relator (i : Fin 12) :
    eval (PresentedGroup.of : Fin 6 → Level2) (level2Relator i) = 1 :=
  defining_relator level2Relator i

def level0ChildWord (i : Fin 7) : Word (Fin 3) :=
  Vector.get #v[[(0, true)], [(1, true)], [(0, true), (2, true), (2, true)], [(0, true)], [(2, true), (0, true), (2, true), (0, true), (2, true)], [(2, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (2, true)], [(1, true), (1, true), (2, true), (0, true), (2, true), (0, true), (1, true), (2, true), (0, true), (0, true), (0, true), (0, true), (2, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (2, true), (0, true), (2, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (2, true)]] i

def level0Generator (i : Fin 7) : Level0 :=
  eval PresentedGroup.of (level0ChildWord i)

def level0Subgroup : Subgroup Level0 := Subgroup.closure (Set.range level0Generator)

theorem level0Generator_mem (i : Fin 7) : level0Generator i ∈ level0Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- Relations required to map the next presentation into this subgroup. -/
def LiftedRelations01 : Prop :=
  ∀ i : Fin 18, eval level0Generator (level1Relator i) = 1

def level1ChildWord (i : Fin 6) : Word (Fin 7) :=
  Vector.get #v[[(0, true)], [(2, true)], [(3, true)], [(4, true)], [(5, true)], [(6, true)]] i

def level1Generator (i : Fin 6) : Level1 :=
  eval PresentedGroup.of (level1ChildWord i)

def level1Subgroup : Subgroup Level1 := Subgroup.closure (Set.range level1Generator)

theorem level1Generator_mem (i : Fin 6) : level1Generator i ∈ level1Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- Relations required to map the next presentation into this subgroup. -/
def LiftedRelations12 : Prop :=
  ∀ i : Fin 12, eval level1Generator (level2Relator i) = 1

def level2ChildWord (i : Fin 1) : Word (Fin 6) :=
  Vector.get #v[[(3, true)]] i

def level2Generator (i : Fin 1) : Level2 :=
  eval PresentedGroup.of (level2ChildWord i)

def level2Subgroup : Subgroup Level2 := Subgroup.closure (Set.range level2Generator)

theorem level2Generator_mem (i : Fin 1) : level2Generator i ∈ level2Subgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBoundChain
