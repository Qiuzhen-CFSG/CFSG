module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Fixed

/-!
# Cubic movement fixes precisely the standard point

Every subgroup of the standard symplectic Sylow fixes its isotropic point.
Movement above q squared therefore forces fixed dimension one and moving
index exactly q cubed. This uses the original coefficient field, without
assuming that the actor is linear over that field.

The literal neighboring-mover application is
NonbinarySymplectic.CriticalReduction.IndividualMovers, for MS93 (5.5).
-/

public noncomputable section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem standardPoint_le_fixed (E : Subgroup (unipotent (F := F))) : point F ≤ fixed E := by
  intro x hx
  obtain ⟨hx,hz⟩ := (mem_point_iff x).mp hx
  apply (mem_fixed_iff E x).mpr
  intro b u w v _
  simp [hx,hz]

theorem fixed_eq_point_and_movingIndex_of_square_lt (E : Subgroup (unipotent (F := F)))
    (hi : Nat.card F^2 < movingIndex E) :
    fixed E = point F ∧ movingIndex E = Nat.card F^3 := by
  have hd := (fixed E).finrank_quotient_add_finrank
  have hv : Module.finrank F (Vector (F := F)) = 4 := by simp [Vector]
  rw [hv] at hd
  change Module.finrank F (Vector (F := F) ⧸ fixed E) + Module.finrank F (fixed E) = 4 at hd
  have hlow := Submodule.finrank_mono (standardPoint_le_fixed E)
  rw [finrank_point] at hlow
  have hhigh : 2 < Module.finrank F (Vector (F := F) ⧸ fixed E) :=
    (pow_lt_pow_iff_right₀ (Finite.one_lt_card : 1 < Nat.card F)).mp hi
  have hu : Module.finrank F (fixed E) ≤ 1 := by
    have hh : 3 + Module.finrank F (fixed E) ≤ 4 :=
      (Nat.add_le_add_right hhigh _).trans_eq hd
    exact Nat.le_of_add_le_add_left hh
  have hf : Module.finrank F (fixed E) = 1 := le_antisymm hu hlow
  have hquot : Module.finrank F (Vector (F := F) ⧸ fixed E) = 3 := by
    exact Nat.add_right_cancel (show _ + 1 = 3 + 1 by simpa only [hf] using hd)
  refine ⟨?_,?_⟩
  · exact (Submodule.eq_of_le_of_finrank_eq (standardPoint_le_fixed E)
      (by rw [finrank_point,hf])).symm
  · rw [movingIndex,hquot]
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
