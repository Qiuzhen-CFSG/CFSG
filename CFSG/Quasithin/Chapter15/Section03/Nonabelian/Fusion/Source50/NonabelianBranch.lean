module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianBranch
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Intersections
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Index
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.MovementTransport
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Source50Model.Movement

/-!
# The actual nonabelian image and the commutator hyperplane

The elementary image of U is the other Klein four-group in the Sylow
orthogonal actor. Its displacement has order eight. Transporting that
literal action identifies [U,V] with both V∩U and V∩O₂(H), and gives the
order-two starred V and the index-two subgroup U C_T(V).

Source: Aschbacher–Smith, 15.3.51(2a), 15.3.53(2), printed pp.1145–1146.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open OrthogonalGeometry
variable {G : Type*} [Group G] [Finite G]
variable (d : CharacteristicTwo.LocalData G) (H : Subgroup G)
  (h : (localSetup d H).Hypothesis)
include h

private theorem image_outside_planePart
    (hu : ¬ IsMulCommutative (localSpan d.ZS H)) :
    ¬ d.action.image (localSpan d.ZS H) ≤
      OrthogonalGeometry.Source50Model.planePart (d.action.sylowImage d.T d.sylow_le) := by
  have he : d.action.image d.S = OrthogonalGeometry.Source50Model.planePart
      (d.action.sylowImage d.T d.sylow_le) := by
    rw [d.action.image_planeStabilizer,OrthogonalGeometry.setwise_plane_eq_ker]
    rfl
  rw [← he]
  exact nonabelian_image_outside_stabilizer d H h hu

theorem nonabelian_image_card
    (hu : ¬ IsMulCommutative (localSpan d.ZS H)) :
    Nat.card (d.action.image (localSpan d.ZS H)) = 4 := by
  let := span_image_elementary d H h
  exact OrthogonalGeometry.Source50Model.other_card_four
    (d.action.sylowImage d.T d.sylow_le) (d.action.image (localSpan d.ZS H))
    (span_image_le_sylow d H h) (sylow_normalizes_span_image d H h)
    (image_outside_planePart d H h hu)

theorem commutator_card_eight
    (hu : ¬ IsMulCommutative (localSpan d.ZS H)) :
    Nat.card (⁅localSpan d.ZS H,d.V⁆ : Subgroup G) = 8 := by
  let := span_image_elementary d H h
  rw [← d.action.map_displacement (localSpan d.ZS H)
    (h.UH_le_QH.trans (h.QH_le_T.trans d.sylow_le)),
    card_map_of_injective d.action.vectorEmbedding_injective]
  exact OrthogonalGeometry.Source50Model.movement_card_eight
    (d.action.sylowImage d.T d.sylow_le) (d.action.image (localSpan d.ZS H))
    (span_image_le_sylow d H h) (sylow_normalizes_span_image d H h)
    (image_outside_planePart d H h hu)

theorem nonabelian_intersections
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V H))
    (hu : ¬ IsMulCommutative (localSpan d.ZS H)) :
    d.V ⊓ H.pCoreIn 2 = ⁅localSpan d.ZS H,d.V⁆ ∧
      d.V ⊓ localSpan d.ZS H = ⁅localSpan d.ZS H,d.V⁆ ∧
      Nat.card ((d.V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
  exact intersections_of_commutator_card d H h.V_le_H h.UH_le_QH
    (module_not_le_core d H h hf hnon)
    (by rw [commutator_comm]; exact (module_commutator_bounds d H h).2)
    (commutator_card_eight d H h hu)

theorem nonabelian_span_centralizer_index
    (hu : ¬ IsMulCommutative (localSpan d.ZS H)) :
    (localSpan d.ZS H ⊔ ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G))).relIndex
      (d.T : Subgroup G) = 2 :=
  sylow_span_centralizer_index d (localSpan d.ZS H)
    (h.UH_le_QH.trans h.QH_le_T) (nonabelian_image_card d H h hu)

/-- The literal coordinates used by the G.2.6 application identify its
perpendicular with the actual ambient intersection. -/
theorem intersection_coordinates_movement
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V H))
    (hu : ¬ IsMulCommutative (localSpan d.ZS H)) :
    ((d.V ⊓ localSpan d.ZS H).subgroupOf d.V).map d.action.coordinates.toMonoidHom =
      OrthogonalGeometry.Source50Model.movement (d.action.image (localSpan d.ZS H)) := by
  have hc := (nonabelian_intersections d H h hf hnon hu).2.1
  apply map_injective d.action.vectorEmbedding_injective
  rw [map_map]
  have he : d.action.vectorEmbedding.comp d.action.coordinates.toMonoidHom = d.V.subtype := by
    ext v
    simp [NaturalOrthogonalAction.vectorEmbedding]
  rw [he,map_subgroupOf_eq_of_le inf_le_left,hc]
  exact (d.action.map_displacement (localSpan d.ZS H)
    (h.UH_le_QH.trans (h.QH_le_T.trans d.sylow_le))).symm

/-- The order-four displacement in U/Z is obtained by dividing the actual
order-eight commutator by its central line. It is not the order of U/Z. -/
theorem commutator_quotient_card
    [(d.Z.subgroupOf (localSpan d.ZS H)).Normal]
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V H))
    (hu : ¬ IsMulCommutative (localSpan d.ZS H)) :
    Nat.card ((⁅localSpan d.ZS H,d.V⁆.subgroupOf (localSpan d.ZS H)).map
      (QuotientGroup.mk' (d.Z.subgroupOf (localSpan d.ZS H)))) = 4 := by
  let U := localSpan d.ZS H
  let C := ⁅U,d.V⁆
  have hCU : C ≤ U := by
    change ⁅localSpan d.ZS H,d.V⁆ ≤ localSpan d.ZS H
    rw [commutator_comm]
    exact (module_commutator_bounds d H h).2.trans inf_le_right
  have hZU : d.Z ≤ U := h.point_lt.le.trans (le_conjugateSpanBy _ _)
  have hZC : d.Z ≤ C := by
    change d.Z ≤ ⁅localSpan d.ZS H,d.V⁆
    rw [← (nonabelian_intersections d H h hf hnon hu).2.1]
    exact le_inf (le_conjugateSpanBy _ _) hZU
  have hk : (C.subgroupOf U) ⊓ (QuotientGroup.mk' (d.Z.subgroupOf U)).ker =
      d.Z.subgroupOf U := by
    rw [QuotientGroup.ker_mk']
    exact inf_eq_right.mpr (comap_mono hZC)
  have hc : Nat.card (C.subgroupOf U) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCU).toEquiv).trans
      (commutator_card_eight d H h hu)
  have hz : Nat.card (d.Z.subgroupOf U) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv).trans h.point_card
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (C.subgroupOf U)
    (QuotientGroup.mk' (d.Z.subgroupOf U))
  rw [hk,hz,hc] at hh
  dsimp only [C,U] at hh
  omega

/-- The nonabelian U action fixes exactly the original Sylow-central line. -/
theorem module_centralizer_eq_point
    (hu : ¬ IsMulCommutative (localSpan d.ZS H)) :
    d.V ⊓ centralizer (localSpan d.ZS H : Set G) = d.Z := by
  let := span_image_elementary d H h
  have hf := OrthogonalGeometry.Source50Model.fixedVectors_other_eq
    (d.action.sylowImage d.T d.sylow_le) (d.action.image (localSpan d.ZS H))
    (span_image_le_sylow d H h) (sylow_normalizes_span_image d H h)
    (image_outside_planePart d H h hu)
  change fixedPlane d.V (localSpan d.ZS H) = d.Z
  rw [d.action.fixedPlane_eq_map (X := localSpan d.ZS H) (h.UH_le_QH.trans (h.QH_le_T.trans d.sylow_le)),hf,d.action.coe_sylowImage,
    ← d.action.fixedPlane_eq_map (X := (d.T : Subgroup G)) d.sylow_le]
  exact (NaturalOrthogonalAction.centralInvolutions_eq_fixedPlane d.T d.sylow_le d.action).symm

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
