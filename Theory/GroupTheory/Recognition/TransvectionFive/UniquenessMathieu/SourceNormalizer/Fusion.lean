module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Orientation
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Transport
public import Theory.GroupTheory.WeakClosureSetFusion

/-!
# Mathieu fusion control from the source Sylow elementary catalogue

The unequal 21/45 counts prevent the two rectangles from being conjugate.
If the source 39.1(3) catalogue of order-64 elementary subgroups of the marked
Sylow is supplied, each rectangle is consequently weakly closed. Their proved
self-centralization lets Burnside fusion produce conjugators in their actual
ambient normalizers. Orbit–stabilizer then gives the relative indices 21 and 45.

The local catalogue remains an explicit premise. This module does not assert
that 39.1(3), or the full 40.3–40.4 normalizer classification, has been proved.
The final application discharges the literal fusion-control premise of the
previously proved obstruction to the legacy relative/full-normalizer interface.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(3), 39.6(1)–(3), and
40.3–40.4, printed pp.213–219.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The precise source 39.1(3) catalogue still needed for weak closure: an
order-64 elementary subgroup in the marked Sylow is one of its two rectangles. -/
@[expose] def RectangleCatalogue : Prop :=
  ∀ A : Subgroup G, A ≤ (sourceSylow F : Subgroup G) →
    IsElementaryAbelian 2 A → Nat.card A = 64 → A = F.plane ∨ A = F.threeSpace

/-- The unequal fusion counts turn the local elementary catalogue into ambient
weak closure of A₁. The catalogue remains an explicit source input. -/
theorem plane_weakly_closed_of_catalogue (hcat : RectangleCatalogue F)
    (hfusion : F.MathieuFusion) (g : G)
    (hg : F.plane.map (MulAut.conj g).toMonoidHom ≤ (sourceSylow F : Subgroup G)) :
    g ∈ normalizer (F.plane : Set G) := by
  have hEA := (marked_rectangle_elementary F 2).map (MulAut.conj g).toMonoidHom
  have hc : Nat.card (F.plane.map (MulAut.conj g).toMonoidHom) = 64 := by
    rw [card_map_of_injective (MulAut.conj g).injective, plane_card F]
  rcases hcat _ hg hEA hc with h | h
  · exact mem_normalizer_iff_map_conj_eq.mpr h
  · exact (planes_not_conjugate F hfusion g h).elim

/-- The same catalogue and unequal counts give weak closure of A₂. -/
theorem threeSpace_weakly_closed_of_catalogue (hcat : RectangleCatalogue F)
    (hfusion : F.MathieuFusion) (g : G)
    (hg : F.threeSpace.map (MulAut.conj g).toMonoidHom ≤ (sourceSylow F : Subgroup G)) :
    g ∈ normalizer (F.threeSpace : Set G) := by
  have hEA := (marked_rectangle_elementary F 3).map (MulAut.conj g).toMonoidHom
  have hc : Nat.card (F.threeSpace.map (MulAut.conj g).toMonoidHom) = 64 := by
    rw [card_map_of_injective (MulAut.conj g).injective, threeSpace_card F]
  rcases hcat _ hg hEA hc with h | h
  · have hi := (map_symm_eq_iff_map_eq F.threeSpace (e := MulAut.conj g)).mpr h
    have he : (MulAut.conj g).symm = MulAut.conj g⁻¹ := by ext x; simp
    rw [he] at hi
    exact (planes_not_conjugate F hfusion g⁻¹ hi).elim
  · exact mem_normalizer_iff_map_conj_eq.mpr h

/-- Source 39.6(3) on the literal A₁, conditional only on its outstanding
source-Sylow catalogue. -/
theorem plane_fusion_control_of_catalogue (hcat : RectangleCatalogue F)
    (hfusion : F.MathieuFusion) (a : G) (ha : a ∈ F.fusion F.plane) :
    ∃ n : planeNormalizer F, (n : G) * z * (n : G)⁻¹ = a := by
  obtain ⟨n, hn, he⟩ := (sourceSylow F).weakly_closed_normalizer_controls_centralizer_fusion
    F.plane (flag_le_sourceSylow F).2.2.1
    (plane_weakly_closed_of_catalogue F hcat hfusion)
    ((plane_centralizer_eq F).symm ▸ point_mem_plane F)
    ((plane_centralizer_eq F).symm ▸ ha.1) ha.2
  exact ⟨⟨n, hn⟩, he⟩

/-- Source 39.6(3) on the literal A₂ with the same outstanding catalogue. -/
theorem threeSpace_fusion_control_of_catalogue (hcat : RectangleCatalogue F)
    (hfusion : F.MathieuFusion) (a : G) (ha : a ∈ F.fusion F.threeSpace) :
    ∃ n : threeSpaceNormalizer F, (n : G) * z * (n : G)⁻¹ = a := by
  obtain ⟨n, hn, he⟩ := (sourceSylow F).weakly_closed_normalizer_controls_centralizer_fusion
    F.threeSpace (flag_le_sourceSylow F).2.2.2
    (threeSpace_weakly_closed_of_catalogue F hcat hfusion)
    ((threeSpace_centralizer_eq F).symm ▸ point_mem_threeSpace F)
    ((threeSpace_centralizer_eq F).symm ▸ ha.1) ha.2
  exact ⟨⟨n, hn⟩, he⟩

omit [Finite G] in
private theorem normalizer_relative_index (A : Subgroup G) (hz : z ∈ A)
    (hcontrol : ∀ a ∈ F.fusion A,
      ∃ n : normalizer (A : Set G), (n : G) * z * (n : G)⁻¹ = a) :
    (centralizer ({z} : Set G)).relIndex (normalizer (A : Set G)) =
      (F.fusion A).ncard := by
  let N := normalizer (A : Set G)
  let : MulAction N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hstab : (centralizer ({z} : Set G)).subgroupOf N = MulAction.stabilizer N z := by
    ext g
    change (g : G) ∈ centralizer ({z} : Set G) ↔ g • z = z
    rw [mem_centralizer_singleton_iff]
    change (g : G) * z = z * (g : G) ↔ (g : G) * z * (g : G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.symm
  have horbit : MulAction.orbit N z = F.fusion A := by
    ext a
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(mem_normalizer_iff.mp g.property z).mp hz, isConj_iff.mpr ⟨g, rfl⟩⟩
    · intro ha
      exact hcontrol a ha
  change ((centralizer ({z} : Set G)).subgroupOf N).index = _
  rw [hstab, MulAction.index_stabilizer, horbit]

/-- With the source catalogue, the actual point-centralizer intersection has
index 21 in N_G(A₁), as used in 40.3. -/
theorem plane_relative_index_of_catalogue (hcat : RectangleCatalogue F)
    (hcounts : MathieuFusionOrientation F) :
    (centralizer ({z} : Set G)).relIndex (planeNormalizer F) = 21 := by
  rw [normalizer_relative_index F F.plane (point_mem_plane F)
    (plane_fusion_control_of_catalogue F hcat (Or.inl hcounts))]
  exact hcounts.1

/-- At the opposite end the corresponding index is 45, as used in 40.4. -/
theorem threeSpace_relative_index_of_catalogue (hcat : RectangleCatalogue F)
    (hcounts : MathieuFusionOrientation F) :
    (centralizer ({z} : Set G)).relIndex (threeSpaceNormalizer F) = 45 := by
  rw [normalizer_relative_index F F.threeSpace (point_mem_threeSpace F)
    (threeSpace_fusion_control_of_catalogue F hcat (Or.inl hcounts))]
  exact hcounts.2

/-- The corrected source control discharges the exact premise of the existing
legacy-interface obstruction, once the elementary catalogue has been supplied. -/
theorem no_legacy_data_of_catalogue (hcat : RectangleCatalogue F)
    (hfusion : F.MathieuFusion) : ¬ Nonempty (NormalizerTypeConsequences F) :=
  no_normalizerTypeConsequences_of_plane_fusion_control F hfusion
    (plane_fusion_control_of_catalogue F hcat hfusion)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
