module

public import CFSG.Quasithin.ChapterG.Section11.SourceSmallCases
public import CFSG.Quasithin.ChapterG.Section10.NonfaithfulFittingSource
public import CFSG.Quasithin.ChapterG.Section10.Components.Orthogonal

/-!
# The remaining source branches after small-degree recognition

The proved plane, four-dimensional and reducible results leave only
irreducible actions in dimension at least six. In the solvable branch the
G.9 Fitting reductions force dimension six and elementary-actor rank two.
In the nonsolvable branch the actor's Fitting centralizer is nontrivial,
and the existing G.10 construction supplies an actual moved component with
its constituent selection and orthogonal pairing data.

This is a reduction, not the exhaustive G.11.2 theorem: recognizing the
six-dimensional solvable group and the nonsolvable component actions is
still required. No classification conclusion is assumed in either branch.
Source: Aschbacher--Smith G.11.4--6, printed pp.365--366.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- Every unclassified low-rank source action has one of the two genuine
remaining structures. The component is constructed from the original action. -/
theorem conclusion_or_remaining_structure
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) :
    Conclusion ρ B X ∨
      (IsIrreducible ρ ∧ 6 ≤ finrank (ZMod 2) V ∧
        ((Group.IsSolvable G ∧ finrank (ZMod 2) (Additive X) = 2 ∧
            finrank (ZMod 2) V = 6) ∨
          (¬ Group.IsSolvable G ∧ X ⊓ centralizer (fittingSubgroup G : Set G) ≠ ⊥ ∧
            ∃ L : Subgroup G, IsComponent G L ∧ ⁅L, X⁆ ≠ ⊥ ∧
              ComponentOrbitSelection ρ B L X ∧ Section10.ComponentOrthogonalData ρ B L))) := by
  by_cases hd : finrank (ZMod 2) V ≤ 4
  · exact Or.inl (conclusion_of_degree_le_four h cover hw hd)
  by_cases hi : IsIrreducible ρ
  · right
    have hsix : 6 ≤ finrank (ZMod 2) V := by
      obtain ⟨k, hk⟩ := AlternatingForm.even_finrank B h.alternating h.nondegenerate
      omega
    refine ⟨hi, hsix, ?_⟩
    by_cases hs : Group.IsSolvable G
    · left
      have hX : X ≠ ⊥ := by
        intro he
        obtain ⟨a, ha, ho, _⟩ := hw.exists_involution h.point_ne_zero
        have ha1 : a = 1 := mem_bot.mp (he ▸ ha)
        simp [ha1] at ho
      rcases h.solvable_irreducible_cases cover hs hi hX with h1 | h2 | h3 | h4 | h6
      · have := h1.2.1; omega
      · have := h2.2.1; omega
      · have := h3.2.1; omega
      · have := h4.2.1; omega
      · exact ⟨hs, h6⟩
    · right
      have hF := h.fitting_centralizer_ne_bot_of_not_solvable cover hs
      exact ⟨hs, hF, h.exists_moved_component_orthogonal_selection hs hF⟩
  · have hred : ¬ IsIrreducible ρ := hi
    have hfour := (h.reducible_degree_and_solvable hred).1
    omega

end CFSG.Quasithin.ChapterG.Section11
