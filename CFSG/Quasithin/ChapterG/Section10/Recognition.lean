module
public import CFSG.Quasithin.ChapterG.Section10.Axis
public import Theory.Representation.BinaryFullAxisRecognition

/-!
# Full linear action on the irreducible submodule in G.10.4

The full axis group is extracted from G.10.1 and its exact rank equation.
The dual directions argument then makes the literal restricted action
surjective onto GL(U), without a source-recognition premise.
-/

public section
open Module Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- The original G-action on a nonzero proper irreducible submodule is full. -/
theorem full_linear_on_irreducible_submodule (U : Subrepresentation ρ)
    [IsIrreducible U.toRepresentation] (hU0 : U.toSubmodule ≠ ⊥)
    (hUt : U.toSubmodule ≠ ⊤) :
    ∀ e : U.toSubmodule ≃ₗ[ZMod 2] U.toSubmodule,
      ∃ g : G, ∀ u : U.toSubmodule, U.toRepresentation g u = e u := by
  apply full_linear_action_of_irreducible_axis U.toRepresentation
    ((B v).comp U.toSubmodule.subtype) (h.axis_form_ne_zero U hU0)
  intro a
  obtain ⟨x, hx⟩ := (h.full_axis_on_submodule U hU0 hUt).2.2 a
  exact ⟨x, hx⟩

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
