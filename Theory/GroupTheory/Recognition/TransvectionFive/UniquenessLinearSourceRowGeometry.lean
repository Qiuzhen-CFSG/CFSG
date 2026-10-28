module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFlagNormalizers
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.RowGeometry

/-!
# Row residues for the linear source geometry

The proved full row action identifies the two literal normalizer intersections
with the stabilizers of the marked three- and two-dimensional row subspaces.
Their maximality and distinctness prove generation of the entire row normalizer.
The subspace coordinates and dimensions are shared with the Mathieu development;
its conditional local-data record is not used.

This proves the point-residue generation clause of Aschbacher, *Sporadic
Groups* (1994), 41.1, pp.219–220, directly from the linear fusion counts.
Global generation and the source comparison remain separate obligations.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
open UniquenessMathieu.OctadSource
  (rowSubspace coordinates_mem_rowSubspace row_plane_finrank row_threeSpace_finrank)
local notation "Four" => (Fin 4 → ZMod 2)
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (hlinear : F.LinearFusion)

/-- The actual conjugation map, factored through the literal row quotient. -/
@[expose] def rowAction : rowNormalizer F →* BinaryLinear.GL Four :=
  (linearRowQuotientEquiv F hlinear).toMonoidHom.comp (QuotientGroup.mk' _)

theorem rowAction_surjective : Function.Surjective (rowAction F hlinear) :=
  (linearRowQuotientEquiv F hlinear).surjective.comp (QuotientGroup.mk'_surjective _)

theorem rowAction_coordinates (g : rowNormalizer F) (a : F.row) :
    rowAction F hlinear g (rowCoordinates F a).toAdd =
      (rowCoordinates F (F.row.normalizerMonoidHom g a)).toAdd :=
  linearRowQuotientEquiv_action F hlinear g a

theorem parabolic_comap (A : Subgroup G) :
    (BinaryLinear.parabolic (rowSubspace F A)).comap (rowAction F hlinear) =
      (normalizer ((F.row ⊓ A : Subgroup G) : Set G)).subgroupOf (rowNormalizer F) := by
  ext g
  change (∀ v : Four, rowAction F hlinear g v ∈ rowSubspace F A ↔ v ∈ rowSubspace F A) ↔
    (g : G) ∈ normalizer ((F.row ⊓ A : Subgroup G) : Set G)
  have hact (a : F.row) :
      rowAction F hlinear g (rowCoordinates F a).toAdd ∈ rowSubspace F A ↔
        (g : G) * (a : G) * (g : G)⁻¹ ∈ A := by
    rw [rowAction_coordinates, coordinates_mem_rowSubspace]
    rfl
  constructor
  · intro h
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · rintro ⟨har, haA⟩
      refine ⟨(mem_normalizer_iff.mp g.property a).mp har, ?_⟩
      exact (hact ⟨a, har⟩).mp ((h _).mpr
        ((coordinates_mem_rowSubspace F A ⟨a, har⟩).mpr haA))
    · rintro ⟨har, haA⟩
      have ha : a ∈ F.row := (mem_normalizer_iff.mp g.property a).mpr har
      exact ⟨ha, (coordinates_mem_rowSubspace F A ⟨a, ha⟩).mp
        ((h _).mp ((hact ⟨a, ha⟩).mpr haA))⟩
  · intro h v
    let a := (rowCoordinates F).symm (Multiplicative.ofAdd v)
    have hv : (rowCoordinates F a).toAdd = v := by simp [a]
    rw [← hv, hact, coordinates_mem_rowSubspace]
    have hn := mem_normalizer_iff.mp h (a : G)
    have hr := (mem_normalizer_iff.mp g.property (a : G)).mp a.property
    simpa only [Subgroup.mem_inf, a.property, hr, true_and] using hn.symm

theorem line_parabolic_comap :
    (BinaryLinear.parabolic (rowSubspace F F.plane)).comap (rowAction F hlinear) =
      (sourcePlaneNormalizer F).subgroupOf (rowNormalizer F) := by
  rw [parabolic_comap, source_row_plane_normalizer]
  ext g
  exact and_iff_right g.property

theorem plane_parabolic_comap :
    (BinaryLinear.parabolic (rowSubspace F F.threeSpace)).comap (rowAction F hlinear) =
      (sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F) := by
  rw [parabolic_comap, source_row_threeSpace_normalizer F hlinear]
  ext g
  exact and_iff_right g.property

omit [Finite G] in
private theorem rowSubspace_ne_bot_top (A : Subgroup G) (n : ℕ)
    (hn0 : 0 < n) (hn4 : n < 4)
    (hd : Module.finrank (ZMod 2) (rowSubspace F A) = n) :
    rowSubspace F A ≠ ⊥ ∧ rowSubspace F A ≠ ⊤ := by
  constructor
  · intro h
    rw [h, finrank_bot] at hd
    omega
  · intro h
    rw [h, finrank_top] at hd
    have hfour : Module.finrank (ZMod 2) Four = 4 := by simp
    rw [hfour] at hd
    omega

include hlinear

/-- The point-line flag stabilizer is a maximal subgroup of the literal point stabilizer. -/
theorem line_flag_maximal :
    IsCoatom ((sourcePlaneNormalizer F).subgroupOf (rowNormalizer F)) := by
  rw [← line_parabolic_comap F hlinear]
  apply isCoatom_comap_of_surjective (rowAction_surjective F hlinear)
  obtain ⟨h0, h1⟩ := rowSubspace_ne_bot_top F F.plane 3 (by decide) (by decide)
    (row_plane_finrank F)
  exact BinaryLinear.FourParabolicAction.parabolic_isCoatom _ h0 h1

/-- The point-plane flag stabilizer is maximal in the same literal point stabilizer. -/
theorem plane_flag_maximal :
    IsCoatom ((sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F)) := by
  rw [← plane_parabolic_comap F hlinear]
  apply isCoatom_comap_of_surjective (rowAction_surjective F hlinear)
  obtain ⟨h0, h1⟩ := rowSubspace_ne_bot_top F F.threeSpace 2 (by decide) (by decide)
    (row_threeSpace_finrank F)
  exact BinaryLinear.FourParabolicAction.parabolic_isCoatom _ h0 h1

/-- The two source parabolics are distinct, since they stabilize subspaces of different dimensions. -/
theorem line_plane_flag_ne :
    (sourcePlaneNormalizer F).subgroupOf (rowNormalizer F) ≠
      (sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F) := by
  intro h
  rw [← line_parabolic_comap F hlinear, ← plane_parabolic_comap F hlinear] at h
  have hp := (Subgroup.comap_injective (rowAction_surjective F hlinear)) h
  obtain ⟨h0, h1⟩ := rowSubspace_ne_bot_top F F.threeSpace 2 (by decide) (by decide)
    (row_threeSpace_finrank F)
  have he := BinaryLinear.FourParabolicAction.parabolic_le_imp_eq h0 h1 hp.le
  have hd := row_plane_finrank F
  rw [he, row_threeSpace_finrank F] at hd
  contradiction

/-- The two marked local flag subgroups generate the actual row normalizer.
This is the G₁ case of residual connectedness in source 41.1. -/
theorem row_flag_generate :
    (rowNormalizer F ⊓ sourcePlaneNormalizer F) ⊔
      (rowNormalizer F ⊓ sourceThreeSpaceNormalizer F) = rowNormalizer F := by
  have hn : ¬ (sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F) ≤
      (sourcePlaneNormalizer F).subgroupOf (rowNormalizer F) := by
    intro h
    rcases (plane_flag_maximal F hlinear).le_iff.mp h with he | he
    · exact (line_flag_maximal F hlinear).ne_top he
    · exact line_plane_flag_ne F hlinear he
  have hs : (sourcePlaneNormalizer F).subgroupOf (rowNormalizer F) ⊔
      (sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F) = ⊤ := by
    apply (line_flag_maximal F hlinear).2
    refine lt_of_le_of_ne le_sup_left ?_
    intro he
    apply hn
    rw [he]
    exact le_sup_right
  have hm := congrArg (fun K : Subgroup (rowNormalizer F) => K.map (rowNormalizer F).subtype) hs
  simpa only [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype,
    inf_comm (sourcePlaneNormalizer F) (rowNormalizer F),
    inf_comm (sourceThreeSpaceNormalizer F) (rowNormalizer F)] using hm

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
