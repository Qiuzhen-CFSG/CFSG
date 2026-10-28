module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeQuotient
public import Theory.GroupTheory.FixedActionNormalizer

/-!
# Field-sized actors and maximum small movers

At every characteristic-two field degree, a field-sized natural fixed index
puts an actor in the plane radical. A maximum small mover outside that
radical forces the whole containing two-group into the point radical, whose
intersection with the plane radical is central. Thus the maximum family
centralizes the actor. Transport through the literal quotient kernel then
normalizes the full fixed subgroup, without assuming that the edge is Sylow
or splitting off the fixed central kernel.

Source: MS93 (5.4) and the fixed-kernel step of (5.7), pp.915 and919.
The actual replacement consumer is `CriticalReduction.SmallMoverKernels`.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem le_plane_wing_of_movingIndex_le_field
    (A : Subgroup (unipotent (F := F))) (hA : movingIndex A ≤ Nat.card F) : A ≤ wing true := by
  by_contra hn
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsq : Nat.card F < Nat.card F ^ 2 := by nlinarith
  have hh := movingIndex_eq_square_of_not_le_wing A (hA.trans hsq.le) hn
  omega

theorem maximal_centralizes_field_actor
    {T E A : Subgroup (unipotent (F := F))} (hE : E ∈ Maximal T)
    (hAT : A ≤ T) (hA : movingIndex A ≤ Nat.card F) : E ≤ centralizer (A : Set _) := by
  have hAw := le_plane_wing_of_movingIndex_le_field A hA
  rcases small_classification_nonstandard E hE.2.1 with hEw | ⟨l,rfl⟩
  · let := wing_elementary (F := F) true
    exact hEw.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hAw))
  · have hTw := le_point_wing_of_maximal_finitePlane T l hE
    have hAc : A ≤ center (unipotent (F := F)) :=
      (le_inf (hAT.trans hTw) hAw).trans_eq wings_inf
    intro e he a ha
    exact (mem_center_iff.mp (hAc ha) e).symm

theorem join_centralizes_field_actor
    (T A : Subgroup (unipotent (F := F))) (hAT : A ≤ T)
    (hA : movingIndex A ≤ Nat.card F) : join T ≤ centralizer (A : Set _) :=
  sSup_le (fun _ hE => maximal_centralizes_field_actor hE hAT hA)

namespace Quotient
variable {G D : Type*} [Group G] [Finite G] [Group D]
variable (U T : Subgroup G) (q : G →* D) (i : unipotent (F := F) →* D)
  (hi : Function.Injective i)
  (hkT : q.ker ≤ T) (hUT : U ≤ centralizer (q.ker : Set G))
  (hTi : T.map q ≤ i.range)
  (hindex : ∀ E : Subgroup G, E ≤ T →
    (centralizer (E : Set G)).relIndex U = movingIndex (coordinates q i E))
include hi hkT hUT hTi hindex in
theorem join_image_centralizes_field_actor
    (A : Subgroup G) (hAT : A ≤ T)
    (hA : (centralizer (A : Set G)).relIndex U ≤ Nat.card F) :
    (Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)).map q ≤
      centralizer (A.map q : Set D) := by
  let J := Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)
  have hJi : J.map q ≤ i.range := (map_mono (Subgroup.SmallMover.join_le _ _ _ _)).trans hTi
  have hAi : A.map q ≤ i.range := (map_mono hAT).trans hTi
  have hcentral := Degree.join_centralizes_field_actor (coordinates q i T) (coordinates q i A)
    (comap_mono (map_mono hAT)) (by rw [←hindex A hAT]; exact hA)
  rw [←coordinates_join U T q i hi hkT hUT hTi hindex] at hcentral
  have hm := (map_mono (f := i) hcentral).trans (map_centralizer_le_centralizer_image _ _)
  change (coordinates q i J).map i ≤ centralizer ((coordinates q i A).map i : Set D) at hm
  rwa [coordinates_map q i J hJi,coordinates_map q i A hAi] at hm

include hi hkT hUT hTi hindex in
theorem join_normalizes_field_fixed
    (hTU : T ≤ normalizer (U : Set G))
    (A : Subgroup G) (hAT : A ≤ T)
    (hA : (centralizer (A : Set G)).relIndex U ≤ Nat.card F) :
    Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2) ≤
      normalizer ((U ⊓ centralizer (A : Set G) : Subgroup G) : Set G) :=
  normalizes_fixed_of_commuting_action_images U _ A q
    ((Subgroup.SmallMover.join_le _ _ _ _).trans hTU) (le_centralizer_iff.mp hUT)
    (join_image_centralizes_field_actor U T q i hi hkT hUT hTi hindex A hAT hA)
end Quotient
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
