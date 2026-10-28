module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Classification

/-!
# Maximum small movers centralize root actors

An actor with natural moving index at most four lies in the standard plane
radical. A maximum small mover either lies there too, or forces the entire
ambient two-group into the other radical. In the latter case the actor lies
in the common Sylow center. Thus every maximum small mover, and their join,
centralizes the actor. This retains arbitrary binary subgroups.

Source: MS93 (5.4) and the kernel normalization in (5.7), pp.915 and919.
The quotient lift is SymplecticFour.SmallMoverKernel.
-/

public noncomputable section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem le_plane_wing_of_movingIndex_le_four (hF : Nat.card F = 4)
    (A : Subgroup (unipotent (F := F))) (hA : movingIndex A ≤ 4) : A ≤ wing true := by
  by_contra hn
  have h := movingIndex_eq_sixteen_of_not_le_wing hF A (by omega) hn
  omega

theorem maximal_centralizes_small_actor (hF : Nat.card F = 4)
    {T E A : Subgroup (unipotent (F := F))} (hE : E ∈ Maximal T)
    (hAT : A ≤ T) (hA : movingIndex A ≤ 4) : E ≤ centralizer (A : Set _) := by
  have hAw := le_plane_wing_of_movingIndex_le_four hF A hA
  rcases small_classification_nonstandard hF E hE.2.1 with hEw | ⟨l,rfl⟩
  · let := wing_elementary (F := F) true
    exact hEw.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hAw))
  · have hTw := le_point_wing_of_maximal_finitePlane hF T l hE
    have hAc : A ≤ center (unipotent (F := F)) :=
      (le_inf (hAT.trans hTw) hAw).trans_eq wings_inf
    intro e he a ha
    exact (mem_center_iff.mp (hAc ha) e).symm

theorem join_centralizes_small_actor (hF : Nat.card F = 4)
    (T A : Subgroup (unipotent (F := F))) (hAT : A ≤ T)
    (hA : movingIndex A ≤ 4) : join T ≤ centralizer (A : Set _) := by
  exact sSup_le (fun _ hE => maximal_centralizes_small_actor hF hE hAT hA)
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
