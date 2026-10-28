module
public import CFSG.Quasithin.ChapterG.Section10.FittingSource
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.SourceCubic

/-!
# Removing the degree-six case from the original G.10 action

The actual degree-six Fitting branch now supplies a normal cubic subgroup.
Consequently the no-normal-cubic source premise and actor rank at least two
force the four-dimensional orthogonal alternative, without a separate bound
on the module degree.

Source: Aschbacher--Smith 14.3.15, using G.9.4 and G.10.2.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- A source actor of rank at least two, with no normal cubic subgroup,
forces the degree-four orthogonal alternative. -/
theorem orthogonal_case_of_actor_rank_and_no_normal_cubic {K : GroupClass.{u}}
    (cover : Nonempty (Section09.SQTKCover K G))
    (hs : Group.IsSolvable G) (hi : Representation.IsIrreducible ρ) (hX : X ≠ ⊥)
    (hr : 2 ≤ finrank (ZMod 2) (Additive X))
    (hno : ∀ C : Subgroup G, C.Normal → Nat.card C = 3 → False) :
    Section09.FittingRecognition.CaseFour ρ (finrank (ZMod 2) (Additive X)) := by
  rcases h.solvable_irreducible_cases cover hs hi hX with h1 | h2 | h3 | h4 | h6
  · have := h1.1; omega
  · have := h2.1; omega
  · have := h3.1; omega
  · exact h4
  · have d := h.fittingHypothesis_of_solvable cover hs hi
    have d2 : Section09.FittingHypothesis K ρ X 2 := h6.1 ▸ d
    have hc : IsPGroup 3 (⁅fittingSubgroup G,X⁆ : Subgroup G) := by
      by_contra hh
      have hh2 := Section09.FittingRecognition.caseTwo_from_source d2 (by decide) hh
      have := hh2.1
      omega
    obtain ⟨C,hCn,hCc⟩ :=
      Section09.FittingRecognition.Six.normal_cubic_of_source_degree_six d2 hc h6.2
    exact (hno C hCn hCc).elim

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
