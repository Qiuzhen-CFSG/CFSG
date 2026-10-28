module
public import Theory.GroupTheory.CosetWordCertificate.RelatorScan
public import Theory.GroupTheory.GeneratorCosetCoverFiniteIndex
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The literal six-generator rank-three J₃ amalgam presentation

The twenty-two words are the six, five and five defining local relations,
followed by the two marked overlap identifications for each pair of locals.
These data are the frozen signed words in
`Scratch/J3AmalgamComparison/Algebra/universal-relators.json`.
This module defines the universal relation carrier and its evaluation maps;
it asserts neither finiteness nor a coset bound before the checked producer.
The expected full universal order is 3·50232960, rather than the simple J₃ order.
Source: Baumeister's J₃-type rank-three amalgam, local groups of orders
8160,2880,2160, as recorded in `refs/baumeister-j3.pdf`, printed pp.492–493.
-/

@[expose] public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation
open Subgroup Subgroup.CosetWordCertificate

/-- Exact original local and overlap words; signed letters use the Mathlib convention. -/
def relatorWord : Fin 22 → Word (Fin 6)
  | 0 => [(0, true), (0, true), (0, true), (0, true), (0, true)]
  | 1 => [(1, true), (1, true), (0, false), (0, false), (1, true), (1, true), (0, false), (0, false)]
  | 2 => [(0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false)]
  | 3 => [(1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true)]
  | 4 => [(0, true), (1, true), (0, false), (1, true), (0, true), (0, true), (1, true), (0, false), (1, true), (0, true)]
  | 5 => [(0, true), (1, false), (0, true), (1, true), (0, false), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false)]
  | 6 => [(3, true), (3, true), (3, true)]
  | 7 => [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]
  | 8 => [(3, true), (2, true), (3, true), (2, true), (2, true), (3, true), (2, true), (3, true), (2, true), (2, true)]
  | 9 => [(2, true), (3, false), (2, false), (2, false), (2, false), (3, false), (2, false), (2, false), (2, false), (3, false), (2, true), (2, true)]
  | 10 => [(2, false), (3, true), (2, false), (3, true), (2, false), (3, true), (2, true), (3, true), (2, false), (3, true), (2, false), (3, false), (2, false), (2, false)]
  | 11 => [(4, true), (5, true), (4, true), (5, true), (4, true), (5, true)]
  | 12 => [(5, true), (5, true), (5, true), (5, true), (5, true), (5, true), (5, true), (5, true)]
  | 13 => [(5, false), (4, true), (4, true), (5, false), (5, false), (4, true), (4, true), (5, false)]
  | 14 => [(4, true), (4, true), (4, true), (4, true), (4, true), (4, true), (4, true), (4, true), (4, true), (4, true)]
  | 15 => [(4, false), (4, false), (4, false), (5, false), (4, true), (5, true), (5, true), (4, true), (5, false), (4, false)]
  | 16 => [(1, false), (0, false), (1, false), (2, false), (2, false), (3, false), (2, true), (3, false), (2, false), (2, false), (3, false)]
  | 17 => [(1, true), (0, true), (1, true), (0, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (2, false), (2, false), (2, false), (3, false), (2, true), (3, false), (2, false), (3, false), (3, false), (2, false), (2, false)]
  | 18 => [(1, true), (0, true), (1, true), (1, true), (0, true), (0, true), (1, true), (0, true), (1, false), (0, false), (0, false), (5, false), (4, false), (4, false), (5, false), (4, false), (5, true), (4, false), (5, false)]
  | 19 => [(0, true), (1, true), (0, true), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (5, true), (4, false), (5, false), (4, true), (4, true), (4, true), (5, true)]
  | 20 => [(2, true), (2, true), (3, false), (2, false), (3, false), (2, false), (3, false), (2, false), (3, false), (3, false), (2, false), (2, false), (5, false), (4, true), (5, false), (5, false), (4, true), (5, true)]
  | _ => [(2, true), (3, false), (2, false), (2, false), (3, true), (2, false), (3, false), (3, false), (2, false), (2, false), (3, false), (2, false), (4, true), (4, true), (4, true), (4, true), (4, true), (4, true), (5, true), (4, true), (5, false), (4, false)]

/-- The actual twenty-two identities under an arbitrary six-generator marking. -/
def Satisfies {G : Type*} [Group G] (g : Fin 6 → G) : Prop :=
  ∀ i, eval g (relatorWord i) = 1

def rels : Set (FreeGroup (Fin 6)) := Set.range (fun i => FreeGroup.mk (relatorWord i))

abbrev Carrier := PresentedGroup rels

def generator (i : Fin 6) : Carrier := PresentedGroup.of i

theorem generator_satisfies : Satisfies generator := by
  intro i
  change FreeGroup.lift (fun a => PresentedGroup.of a) (FreeGroup.mk (relatorWord i)) = 1
  have he : FreeGroup.lift (fun a => PresentedGroup.of a) = PresentedGroup.mk rels := by
    apply FreeGroup.ext_hom
    intro a
    rfl
  rw [he]
  exact PresentedGroup.one_of_mem ⟨i,rfl⟩

/-- The defining six generators generate the relation carrier. -/
theorem generator_generates : closure (Set.range generator) = ⊤ :=
  PresentedGroup.closure_range_of rels

/-- The literal subgroup represented by the first local pair. -/
def firstLocal : Subgroup Carrier := closure ({generator 0,generator 1} : Set Carrier)

/-- Evaluation retains the actual marked six generators. -/
def evaluation {G : Type*} [Group G] {g : Fin 6 → G} (h : Satisfies g) : Carrier →* G :=
  PresentedGroup.toGroup (f := g) (by
    rintro r ⟨i,rfl⟩
    exact h i)

@[simp] theorem evaluation_generator {G : Type*} [Group G] {g : Fin 6 → G}
    (h : Satisfies g) (i : Fin 6) : evaluation h (generator i) = g i :=
  PresentedGroup.toGroup.of _

theorem evaluation_surjective {G : Type*} [Group G] {g : Fin 6 → G}
    (h : Satisfies g) (hg : closure (Set.range g) = ⊤) :
    Function.Surjective (evaluation h) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hg, closure_le]
  rintro _ ⟨i,rfl⟩
  exact ⟨generator i,evaluation_generator h i⟩

end Sporadic.Janko3.AmalgamPresentation
