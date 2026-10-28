module

public import CFSG.Quasithin.ChapterG.Section11.Catalogue
public import CFSG.Quasithin.ChapterG.Section11.Four
public import Theory.LinearAlgebra.AlternatingFinrank
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The small-degree source branches of G.11.2

For the original G.10 action, the exact G.11.1(3ii) witness gives the plane
alternative in degree two. The four-dimensional theorem includes the
order-divisibility clause in both the solvable and nonsolvable branches.
Even dimension and the nonzero marked point exhaust degrees at most four.
The theorem makes no assertion in degrees six, eight or twelve.

Source: Aschbacher--Smith G.11.1(3ii), G.11.2(1--2), and G.10.5,
printed pp.359, 364--365.
-/

@[expose] public section
open Subgroup Module Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- The literal small-degree portion of G.11.2, under the original G.10
hypotheses and the paper's quotient-of-SQTK-group hypothesis. -/
theorem conclusion_of_degree_two_or_solvable_four
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X)
    (hd : finrank (ZMod 2) V = 2 ∨
      (finrank (ZMod 2) V = 4 ∧ Group.IsSolvable G)) :
    Conclusion ρ B X := by
  rcases hd with hd | ⟨hd, hs⟩
  · exact Or.inl (caseOne_of_degree_two h hw hd)
  · exact Or.inr (Or.inl (caseTwo_of_solvable_degree_four h cover hw hs hd))

/-- The complete small-dimensional specialization, with the full known-simple
class in the original SQTK-cover hypothesis. No classification input is added. -/
theorem conclusion_of_degree_le_four
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hd : finrank (ZMod 2) V ≤ 4) :
    Conclusion ρ B X := by
  let : Nontrivial V := ⟨⟨v, 0, h.point_ne_zero⟩⟩
  have hp : 0 < finrank (ZMod 2) V := Module.finrank_pos
  obtain ⟨k, hk⟩ := AlternatingForm.even_finrank B h.alternating h.nondegenerate
  by_cases htwo : finrank (ZMod 2) V = 2
  · exact Or.inl (caseOne_of_degree_two h hw htwo)
  · exact Or.inr (Or.inl (caseTwo_of_degree_four h cover hw (by omega)))

end CFSG.Quasithin.ChapterG.Section11
