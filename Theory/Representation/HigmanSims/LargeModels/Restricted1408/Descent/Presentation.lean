module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Words
public import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.FinCases

/-!
# The universal group for the sourced HS relators

Evaluate the thirteen signed words of `HSG1-P1.M` in any group. Their
quotient of the free group has a homomorphism to every pair satisfying the
relations, with both generator images fixed. This constructs a universal
group, not an identification with the permutation-defined HS carrier.
The latter requires the separate faithfulness theorem.

Source: ATLAS HSG1-P1.M, retained under `source/` with attribution.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation

/-- The signed alphabet uses the source's ordinary multiplication. -/
def letter {G : Type*} [Group G] (a b : G) : Fin 4 → G := ![a, b, a⁻¹, b⁻¹]

/-- Evaluate one of the thirteen literal relators. -/
def word {G : Type*} [Group G] (a b : G) (i : Fin 13) : G :=
  ((relatorLetters i).map (letter a b)).prod

theorem map_letter {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (i : Fin 4) :
    f (letter a b i) = letter (f a) (f b) i := by
  fin_cases i <;> simp [letter]

theorem map_word {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (i : Fin 13) :
    f (word a b i) = word (f a) (f b) i := by
  simp only [word, map_list_prod, List.map_map]
  congr 2
  funext j
  exact map_letter f a b j

/-- The relations, in the free group on two marked generators. -/
def relator : Fin 13 → FreeGroup Bool :=
  word (FreeGroup.of false) (FreeGroup.of true)

/-- All thirteen relations are imposed, including the three source extras. -/
def Universal := PresentedGroup (Set.range relator)
  deriving Group

def generator (i : Bool) : Universal := PresentedGroup.of i

/-- The universal homomorphism with the specified two images. -/
def pairHom {G : Type*} [Group G] (a b : G)
    (h : ∀ i, word a b i = 1) : Universal →* G :=
  PresentedGroup.toGroup (f := fun i => if i then b else a) (by
    rintro _ ⟨i, rfl⟩
    rw [relator, map_word, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    exact h i)

@[simp] theorem pairHom_generator_false {G : Type*} [Group G] (a b : G)
    (h : ∀ i, word a b i = 1) : pairHom a b h (generator false) = a :=
  PresentedGroup.toGroup.of _

@[simp] theorem pairHom_generator_true {G : Type*} [Group G] (a b : G)
    (h : ∀ i, word a b i = 1) : pairHom a b h (generator true) = b :=
  PresentedGroup.toGroup.of _

/-- The universal group itself satisfies every relation. -/
theorem universal_word (i : Fin 13) :
    word (generator false) (generator true) i = 1 := by
  have h := PresentedGroup.one_of_mem (rels := Set.range relator) ⟨i, rfl⟩
  rw [relator, map_word] at h
  exact h

end Sporadic.LeechRelated.HS.AtlasPresentation
