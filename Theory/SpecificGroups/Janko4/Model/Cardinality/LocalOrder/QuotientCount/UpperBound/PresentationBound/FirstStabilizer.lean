module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.Data
public import Theory.GroupTheory.CosetWordCertificate

/-!
# A short presentation for the first proposed stabilizer

These words record the first step of GAP's multistage presentation algorithm
on the permutations in `../source/presentation.g`. The full run reproduces the
47 fixed relators exactly. Its first stabilizer has ten named generators and
43 short relators. All words below are reversed from GAP multiplication order.

This module defines the candidate subgroup and its auxiliary presentation.
It does not identify either with a permutation group. The two remaining
obligations are a bound for `StabilizerPresentation` and the vanishing of its
relators on `subgroupGenerator` in the original `Presentation`.
The adjacent `source/extract.g` and `levels.json` retain the untrusted discovery
inputs and all recursive levels; GAP computations are not proof assumptions.
-/

@[expose] public section
namespace Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound
open Subgroup.CosetWordCertificate

def subgroupWord0 : List (Bool × Bool) :=
  [(false, true), (true, true)]

def subgroupWord1 : List (Bool × Bool) :=
  [(true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (false, true)]

def subgroupWord2 : List (Bool × Bool) :=
  [(true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)]

def subgroupWord3 : List (Bool × Bool) :=
  [(false, false), (true, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true), (false, true), (false, true), (false, true), (true, true), (false, true), (false, true), (false, true)]

def subgroupWord4 : List (Bool × Bool) :=
  [(true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)]

def subgroupWord5 : List (Bool × Bool) :=
  [(true, true), (false, true), (true, true), (false, true), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)]

def subgroupWord6 : List (Bool × Bool) :=
  [(false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)]

def subgroupWord7 : List (Bool × Bool) :=
  [(true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true), (true, true), (true, true)]

def subgroupWord8 : List (Bool × Bool) :=
  [(false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (false, false), (true, false), (false, false), (true, false), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)]

def subgroupWord9 : List (Bool × Bool) :=
  [(true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false), (true, false), (false, true), (true, false), (false, true), (false, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)]

def subgroupWord (i : Fin 10) : List (Bool × Bool) :=
  Vector.get #v[subgroupWord0, subgroupWord1, subgroupWord2, subgroupWord3, subgroupWord4, subgroupWord5, subgroupWord6, subgroupWord7, subgroupWord8, subgroupWord9] i

def subgroupGenerator (i : Fin 10) : Presentation :=
  eval PresentedGroup.of (subgroupWord i)

def firstSubgroup : Subgroup Presentation := Subgroup.closure (Set.range subgroupGenerator)

theorem subgroupGenerator_mem (i : Fin 10) : subgroupGenerator i ∈ firstSubgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

def stabilizerRelator0 : List (Fin 10 × Bool) :=
  [(8, true), (8, true)]

def stabilizerRelator1 : List (Fin 10 × Bool) :=
  [(4, false), (2, true)]

def stabilizerRelator2 : List (Fin 10 × Bool) :=
  [(7, true), (7, true), (7, true)]

def stabilizerRelator3 : List (Fin 10 × Bool) :=
  [(9, true), (9, true), (9, true)]

def stabilizerRelator4 : List (Fin 10 × Bool) :=
  [(2, true), (4, true), (2, true), (4, true)]

def stabilizerRelator5 : List (Fin 10 × Bool) :=
  [(7, true), (5, false), (6, false), (6, false)]

def stabilizerRelator6 : List (Fin 10 × Bool) :=
  [(9, true), (7, false), (9, true), (7, false)]

def stabilizerRelator7 : List (Fin 10 × Bool) :=
  [(6, true), (6, true), (6, true), (6, true), (6, true)]

def stabilizerRelator8 : List (Fin 10 × Bool) :=
  [(6, false), (4, false), (2, false), (9, true), (6, false), (8, true)]

def stabilizerRelator9 : List (Fin 10 × Bool) :=
  [(8, true), (6, false), (8, true), (9, false), (4, false), (2, false)]

def stabilizerRelator10 : List (Fin 10 × Bool) :=
  [(9, false), (7, true), (8, true), (9, false), (7, true), (8, true)]

def stabilizerRelator11 : List (Fin 10 × Bool) :=
  [(7, true), (9, false), (8, true), (7, true), (9, false), (8, true)]

def stabilizerRelator12 : List (Fin 10 × Bool) :=
  [(8, true), (9, true), (4, false), (2, false), (7, false), (5, false)]

def stabilizerRelator13 : List (Fin 10 × Bool) :=
  [(9, true), (5, true), (0, false), (9, false), (5, false), (0, true)]

def stabilizerRelator14 : List (Fin 10 × Bool) :=
  [(9, false), (2, true), (3, true), (9, false), (2, true), (3, true)]

def stabilizerRelator15 : List (Fin 10 × Bool) :=
  [(8, true), (7, false), (8, true), (7, false), (8, true), (7, false)]

def stabilizerRelator16 : List (Fin 10 × Bool) :=
  [(2, true), (4, true), (9, false), (7, true), (8, true), (5, true), (6, true)]

def stabilizerRelator17 : List (Fin 10 × Bool) :=
  [(8, true), (7, false), (2, true), (3, true), (7, false), (2, true), (3, true)]

def stabilizerRelator18 : List (Fin 10 × Bool) :=
  [(5, false), (5, false), (9, false), (2, false), (7, true), (6, false), (2, true)]

def stabilizerRelator19 : List (Fin 10 × Bool) :=
  [(9, true), (6, false), (7, true), (2, false), (8, true), (0, false), (7, true), (1, false)]

def stabilizerRelator20 : List (Fin 10 × Bool) :=
  [(2, false), (8, true), (9, false), (7, true), (2, false), (5, true), (2, true), (7, true)]

def stabilizerRelator21 : List (Fin 10 × Bool) :=
  [(9, false), (8, true), (2, true), (5, false), (3, false), (9, true), (3, true), (3, true)]

def stabilizerRelator22 : List (Fin 10 × Bool) :=
  [(9, false), (7, false), (8, true), (2, true), (5, false), (7, false), (5, true), (2, true)]

def stabilizerRelator23 : List (Fin 10 × Bool) :=
  [(8, true), (9, false), (6, false), (2, false), (5, false), (3, true), (0, true), (1, false), (0, false)]

def stabilizerRelator24 : List (Fin 10 × Bool) :=
  [(8, true), (2, true), (5, false), (4, false), (3, true), (7, false), (2, false), (5, true), (3, true)]

def stabilizerRelator25 : List (Fin 10 × Bool) :=
  [(5, false), (3, false), (5, true), (2, true), (8, true), (5, false), (5, false), (0, true), (9, true), (0, false)]

def stabilizerRelator26 : List (Fin 10 × Bool) :=
  [(5, false), (7, true), (9, false), (2, false), (5, false), (6, false), (3, true), (7, true), (9, false), (3, false)]

def stabilizerRelator27 : List (Fin 10 × Bool) :=
  [(2, false), (3, true), (2, false), (2, false), (7, false), (8, true), (0, false), (6, false), (7, true), (0, true)]

def stabilizerRelator28 : List (Fin 10 × Bool) :=
  [(7, false), (8, true), (9, false), (5, false), (2, true), (5, false), (4, false), (2, false), (6, false), (2, true)]

def stabilizerRelator29 : List (Fin 10 × Bool) :=
  [(9, false), (8, true), (9, false), (5, false), (2, false), (8, true), (3, true), (5, false), (2, true), (3, false)]

def stabilizerRelator30 : List (Fin 10 × Bool) :=
  [(6, false), (2, true), (3, true), (5, true), (2, true), (8, true), (0, false), (9, false), (5, false), (8, true), (1, true)]

def stabilizerRelator31 : List (Fin 10 × Bool) :=
  [(6, false), (2, true), (5, true), (2, true), (4, true), (9, true), (7, false), (3, false), (8, true), (6, false), (3, true)]

def stabilizerRelator32 : List (Fin 10 × Bool) :=
  [(2, true), (3, true), (9, true), (6, false), (2, true), (6, false), (9, false), (7, false), (0, true), (6, false), (0, false)]

def stabilizerRelator33 : List (Fin 10 × Bool) :=
  [(9, false), (7, false), (9, false), (6, false), (2, false), (6, true), (9, false), (3, false), (7, false), (2, false), (3, true)]

def stabilizerRelator34 : List (Fin 10 × Bool) :=
  [(3, true), (9, true), (2, true), (5, true), (5, true), (9, false), (7, true), (8, true), (0, true), (2, true), (9, false), (0, true)]

def stabilizerRelator35 : List (Fin 10 × Bool) :=
  [(6, true), (6, true), (2, true), (5, false), (5, false), (9, true), (8, true), (7, false), (3, true), (6, true), (7, false), (3, true)]

def stabilizerRelator36 : List (Fin 10 × Bool) :=
  [(9, false), (8, true), (6, true), (6, true), (7, false), (2, true), (3, true), (7, true), (0, false), (3, false), (2, false), (0, true)]

def stabilizerRelator37 : List (Fin 10 × Bool) :=
  [(6, true), (3, true), (2, false), (8, true), (5, false), (8, true), (7, true), (8, true), (0, false), (3, true), (1, true), (0, true)]

def stabilizerRelator38 : List (Fin 10 × Bool) :=
  [(8, true), (6, false), (8, true), (6, false), (5, true), (7, true), (2, false), (8, true), (3, false), (9, false), (5, false), (3, true)]

def stabilizerRelator39 : List (Fin 10 × Bool) :=
  [(3, true), (3, true), (7, true), (6, true), (2, true), (5, true), (5, true), (8, true), (0, true), (2, false), (9, false), (0, true)]

def stabilizerRelator40 : List (Fin 10 × Bool) :=
  [(2, false), (3, true), (6, true), (2, true), (7, false), (5, true), (6, false), (6, false), (9, false), (0, true), (0, true), (2, true), (0, true)]

def stabilizerRelator41 : List (Fin 10 × Bool) :=
  [(9, false), (7, true), (6, true), (7, true), (2, false), (7, false), (6, true), (3, true), (2, true), (0, false), (6, false), (2, true), (0, true)]

def stabilizerRelator42 : List (Fin 10 × Bool) :=
  [(9, false), (8, true), (5, false), (7, false), (5, false), (2, false), (5, false), (2, true), (3, false), (0, true), (3, false), (9, false), (0, true)]

def stabilizerRelator (i : Fin 43) : List (Fin 10 × Bool) :=
  Vector.get #v[stabilizerRelator0, stabilizerRelator1, stabilizerRelator2, stabilizerRelator3, stabilizerRelator4, stabilizerRelator5, stabilizerRelator6, stabilizerRelator7, stabilizerRelator8, stabilizerRelator9, stabilizerRelator10, stabilizerRelator11, stabilizerRelator12, stabilizerRelator13, stabilizerRelator14, stabilizerRelator15, stabilizerRelator16, stabilizerRelator17, stabilizerRelator18, stabilizerRelator19, stabilizerRelator20, stabilizerRelator21, stabilizerRelator22, stabilizerRelator23, stabilizerRelator24, stabilizerRelator25, stabilizerRelator26, stabilizerRelator27, stabilizerRelator28, stabilizerRelator29, stabilizerRelator30, stabilizerRelator31, stabilizerRelator32, stabilizerRelator33, stabilizerRelator34, stabilizerRelator35, stabilizerRelator36, stabilizerRelator37, stabilizerRelator38, stabilizerRelator39, stabilizerRelator40, stabilizerRelator41, stabilizerRelator42] i

def stabilizerRelatorWord (i : Fin 43) : FreeGroup (Fin 10) :=
  FreeGroup.mk (stabilizerRelator i)

abbrev StabilizerPresentation := PresentedGroup (Set.range stabilizerRelatorWord)

/-- The precise relation-lifting obligation, independent of any cardinal bound. -/
def StabilizerRelations : Prop :=
  ∀ i : Fin 43, eval subgroupGenerator (stabilizerRelator i) = 1

/-- The defining relations vanish in the original presented group. -/
theorem presentation_relator (i : Fin 47) :
    eval (PresentedGroup.of : Bool → Presentation) (relatorLetters i) = 1 := by
  have h := FreeGroup.lift_unique (f := (PresentedGroup.of : Bool → Presentation))
    (PresentedGroup.mk (Set.range relatorWord))
    (fun _ => rfl) (x := relatorWord i)
  change FreeGroup.lift PresentedGroup.of (relatorWord i) = 1
  rw [← h]
  exact PresentedGroup.one_of_mem (Set.mem_range_self i)

end Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound
