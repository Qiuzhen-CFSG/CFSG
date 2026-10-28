module
public import CFSG.Quasithin.ChapterG.Section10.NumericalGeometry
public import Theory.Representation.BinarySymplecticFourActorBound

/-!
# The smaller actor on a binary symplectic four-space

The full elementary actor has order at most eight. G.10.2 makes its
quotient by the smaller actor nontrivial in dimension four, so the
smaller actor has order at most four. This is the numerical input to
the displaced-center calculation in original 14.3.14--15.
Source: Aschbacher--Smith G.10.1--2 and G.11.2(2), printed pp.357,364.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- The literal smaller actor has order at most four in degree four. -/
theorem smaller_card_le_four_of_dimension_four (h : Hypothesis ρ B v W X X₀)
    (hd : Module.finrank (ZMod 2) V = 4) : Nat.card X₀ ≤ 4 := by
  have hX : Nat.card X ≤ 8 := Representation.binarySymplecticFour_elementary_card_le_eight
    ρ h.faithful hd B h.alternating h.nondegenerate h.preserves X
  have hqpos : 0 < Group.rank (X ⧸ X₀) := by
    have hb := h.dimension_bound.1
    rw [hd] at hb
    omega
  have hqcard : 2 ≤ Nat.card (X ⧸ X₀) := by
    by_contra hh
    let : Subsingleton (X ⧸ X₀) := Finite.card_le_one_iff_subsingleton.mp (by omega)
    have hr := Group.rank_eq_zero (X ⧸ X₀)
    omega
  have hc := X₀.card_mul_index
  rw [index_eq_card] at hc
  nlinarith
end CFSG.Quasithin.ChapterG.Section10.Hypothesis
