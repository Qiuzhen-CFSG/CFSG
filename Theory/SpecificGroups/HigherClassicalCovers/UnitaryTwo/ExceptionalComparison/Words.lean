module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Data.Fin.VecNotation

/-!
# An explicit two-generator presentation for the exceptional comparison

The eleven signed words are candidates obtained from GAP's two generators
of SU₄(2). They define an abstract presented group; this file does not assert
its order or identify it with either matrix group. Positive signs mean the
generator, negative signs its inverse, with multiplication from left to right.
The companion `Relations` module checks their evaluations on actual matrices.

Source purpose: the exceptional comparison in Aschbacher–Smith I.1.4(1),
printed p.408; GLS3 §2.2 and §2.7. The generating script and raw words are
retained in `source/`; GAP output is not a proof of presentation exactness.
-/

@[expose] public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison

def relatorWord : Fin 11 → List (Fin 2 × Bool) :=
  ![[(0, true), (0, true), (0, true)],
    [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true)],
    [(0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true)],
    [(0, false), (1, false), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (1, true)],
    [(1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, false), (1, false), (1, false), (1, false), (0, true), (1, false), (1, false), (1, false), (0, false)],
    [(1, false), (0, true), (1, false), (0, false), (1, false), (1, false), (0, true), (1, false), (0, false), (1, false), (0, true), (1, false), (0, false), (1, false), (1, false), (0, true), (1, false), (0, false)],
    [(1, true), (1, true), (0, false), (1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, true), (0, false), (1, true), (1, true), (0, false), (1, true), (1, true), (0, false)],
    [(1, true), (0, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (1, true), (0, false), (1, false), (0, true), (1, true), (1, true), (0, false)],
    [(0, true), (1, true), (1, true), (0, false), (1, true), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (0, true), (1, false), (1, false), (0, false), (1, false), (0, true), (1, false), (1, false), (1, false), (0, false), (1, true)],
    [(1, true), (0, false), (1, true), (0, false), (1, true), (0, true), (1, true), (1, true), (0, false), (1, true), (0, true), (1, false), (0, false), (1, true), (1, true), (0, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, false), (1, false), (0, true)],
    [(1, true), (0, true), (1, true), (1, true), (0, false), (1, true), (1, true), (0, true), (1, true), (1, true), (0, false), (1, true), (0, true), (1, false), (0, false), (1, false), (0, true), (1, false), (1, false), (0, false), (1, false), (0, true), (1, false), (0, false)]]

def relator (r : Fin 11) : FreeGroup (Fin 2) := FreeGroup.mk (relatorWord r)

abbrev Presentation := PresentedGroup (Set.range relator)

theorem relatorWord_length_le (r : Fin 11) : (relatorWord r).length ≤ 24 := by
  revert r
  decide +kernel

theorem presentation_relator (r : Fin 11) :
    FreeGroup.lift (PresentedGroup.of : Fin 2 → Presentation) (relator r) = 1 := by
  have h : FreeGroup.lift (PresentedGroup.of : Fin 2 → Presentation) =
      PresentedGroup.mk (Set.range relator) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [FreeGroup.lift_apply_of]
    rfl
  rw [h]
  exact PresentedGroup.one_of_mem ⟨r, rfl⟩

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
