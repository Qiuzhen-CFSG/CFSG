module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Uniqueness
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.PlaneGeometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry

/-!
# Both definite-plane bounds from original local uniqueness

The actual orthogonal coordinates construct the plane interchange inside
T, identify both plane stabilizers, and give a fixed line of order two in
each plane. Thus 15.3.44 supplies all three conclusions of 15.3.45, including
the literal first-plane centralizer bound used by the original E endgame.

Source: Aschbacher--Smith 15.3.44--45, printed pp.1139--1140.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

/-- The original natural coordinates supply every plane premise of15.3.45.
Only the preceding uniqueness conclusion remains as an input. -/
theorem planes_control_of_local_uniqueness (d : CharacteristicTwo.LocalData G)
    (h44 : ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      Chapter4.UniqueMaximalOvergroup (Yplus ⊔ d.S) d.M) :
    ∀ V ∈ ({d.V₁, d.V₂} : Set (Subgroup G)),
      Chapter4.UniqueMaximalOvergroup ((d.Y ⊓ centralizer (V : Set G)) ⊔ d.S) d.M ∧
      normalizer (V : Set G) ≤ d.M ∧ centralizer (fixedPlane V d.S : Set G) ≤ d.M := by
  have hStab (i : OrthogonalPlaneIndex) : planeStabilizer d.T (d.action.plane i) = d.S := by
    have he : (normalizer (d.action.plane i : Set G)).subgroupOf d.M =
        (normalizer (d.action.plane 1 : Set G)).subgroupOf d.M := by
      rw [d.action.plane_normalizer_eq_comap, d.action.plane_normalizer_eq_comap,
        OrthogonalGeometry.setwise_plane_eq_ker, OrthogonalGeometry.setwise_plane_eq_ker]
    apply le_antisymm
    · intro x hx
      have hn : (⟨x, d.sylow_le hx.1⟩ : d.M) ∈
          (normalizer (d.action.plane i : Set G)).subgroupOf d.M := hx.2
      rw [he] at hn
      exact ⟨hx.1, hn⟩
    · exact le_inf inf_le_left (OutsideStructure.LocalBranches.s_normalizes_plane d i)
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two (d.action.planeStabilizer_index_two d.T d.sylow_le 1))
  obtain ⟨t, ht, _, ht12, _⟩ := RankOne.PlaneGeometry.exists_plane_interchanger
    d.action d.T d.sylow_le
    (show (1 : OrthogonalPlaneIndex) ≠ Multiplicative.ofAdd (1 : ZMod 2) by decide)
  apply lemma_15_3_45_of_uniqueness
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
    (inf_le_left.trans d.sylow_le) h44 t (d.sylow_le ht)
    (OutsideStructure.LocalBranches.m_normalizes_y d (d.sylow_le ht)) (hTS ht) ht12
  intro V hV
  have hex : ∃ i : OrthogonalPlaneIndex, V = d.action.plane i := by
    rcases Set.mem_insert_iff.mp hV with rfl | he
    · exact ⟨1, rfl⟩
    · exact ⟨Multiplicative.ofAdd (1 : ZMod 2), Set.mem_singleton_iff.mp he⟩
  obtain ⟨i, rfl⟩ := hex
  have hcard := d.action.card_plane i
  have hfix := d.action.card_plane_fixed_planeStabilizer d.T d.sylow_le i
  rw [hStab] at hfix
  refine ⟨IsPGroup.of_card (n := 2) hcard, ?_,
    OutsideStructure.LocalBranches.ys_normalizes_plane d i, ?_⟩
  · intro he
    simp [he] at hcard
  · intro he
    have hh : Nat.card (fixedPlane (d.action.plane i) d.S) = 1 := Subgroup.card_eq_one.mpr he
    omega

/-- Literal first-plane centralizer bound used by the original E endgame. -/
theorem fixedPlane_centralizer_le_of_local_uniqueness (d : CharacteristicTwo.LocalData G)
    (h44 : ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      Chapter4.UniqueMaximalOvergroup (Yplus ⊔ d.S) d.M) :
    centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M :=
  (planes_control_of_local_uniqueness d h44 d.V₁ (Set.mem_insert _ _)).2.2

end CFSG.Quasithin.Chapter15.Section03
