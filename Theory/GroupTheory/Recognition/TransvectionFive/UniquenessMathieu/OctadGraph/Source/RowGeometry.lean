module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Boundary
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Intersections
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Maximality
public import Mathlib.FieldTheory.Finiteness

/-!
# The literal row residue in the Mathieu source geometry

Use the original row coordinates to regard U₁ ∩ A₁ and U₁ ∩ A₂ as
subspaces of the natural four-dimensional row module. Their dimensions are
three and two. The actual quotient action carries their normalizers to the
corresponding parabolics, with the literal quotient map and conjugation
formula retained. Both point-flag stabilizers are maximal and together
generate N_G(U₁), proving the point-residue generation clause of 41.1.

The only conditional input is SourceNormalizer.LocalData. This proves a
local clause, not global generation, the source uniqueness system, or the
source/model comparison of 41.4. Those remain obligations of this development.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1, pp.219–220.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer

local notation "Four" => (Fin 4 → ZMod 2)


variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The literal intersection with the marked row, in its binary coordinates. -/
@[expose] def rowSubspace (A : Subgroup G) : Submodule (ZMod 2) Four where
  carrier := {v | ((rowCoordinates F).symm (Multiplicative.ofAdd v) : G) ∈ A}
  zero_mem' := by change ((rowCoordinates F).symm 1 : G) ∈ A; simp
  add_mem' := by
    intro v w hv hw
    change ((rowCoordinates F).symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : G) ∈ A
    simpa only [map_mul, Subgroup.coe_mul] using A.mul_mem hv hw
  smul_mem' := by
    intro c v hv
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · simp
    · simpa only [one_smul] using hv

@[simp] theorem coordinates_mem_rowSubspace (A : Subgroup G) (a : F.row) :
    (rowCoordinates F a).toAdd ∈ rowSubspace F A ↔ (a : G) ∈ A := by
  change ((rowCoordinates F).symm (rowCoordinates F a) : G) ∈ A ↔ _
  rw [MulEquiv.symm_apply_apply]

private def rowSubspaceEquiv (A : Subgroup G) : rowSubspace F A ≃ ↥(F.row ⊓ A) where
  toFun v := ⟨(rowCoordinates F).symm (Multiplicative.ofAdd v.val),
    ((rowCoordinates F).symm _).property, v.property⟩
  invFun a := ⟨(rowCoordinates F ⟨a, a.property.1⟩).toAdd,
    (coordinates_mem_rowSubspace F A _).mpr a.property.2⟩
  left_inv v := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      ((rowCoordinates F).apply_symm_apply (Multiplicative.ofAdd v.val))
  right_inv a := by
    apply Subtype.ext
    exact congrArg (fun x : F.row => (x : G))
      ((rowCoordinates F).symm_apply_apply ⟨a, a.property.1⟩)

theorem rowSubspace_card (A : Subgroup G) :
    Nat.card (rowSubspace F A) = Nat.card ↥(F.row ⊓ A) :=
  Nat.card_congr (rowSubspaceEquiv F A)

variable (D : LocalData F)

theorem row_plane_finrank : Module.finrank (ZMod 2) (rowSubspace F F.plane) = 3 := by
  have h := (rowSubspace_card F F.plane).trans (SourceNormalizer.row_plane_card F)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) (h.trans (by decide : 8 = 2 ^ 3))

theorem row_threeSpace_finrank :
    Module.finrank (ZMod 2) (rowSubspace F F.threeSpace) = 2 := by
  have h := (rowSubspace_card F F.threeSpace).trans (SourceNormalizer.row_threeSpace_card F)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) (h.trans (by decide : 4 = 2 ^ 2))

/-- The actual conjugation map, factored through the literal row quotient. -/
@[expose] def rowAction : rowNormalizer F →* BinaryLinear.GL Four :=
  (LocalData.rowEquiv F D).toMonoidHom.comp (QuotientGroup.mk' _)

theorem rowAction_surjective : Function.Surjective (rowAction F D) :=
  (LocalData.rowEquiv F D).surjective.comp (QuotientGroup.mk'_surjective _)

theorem rowAction_coordinates (g : rowNormalizer F) (a : F.row) :
    rowAction F D g (rowCoordinates F a).toAdd =
      (rowCoordinates F (F.row.normalizerMonoidHom g a)).toAdd :=
  LocalData.rowEquiv_action F D g a

theorem parabolic_comap (A : Subgroup G) :
    (BinaryLinear.parabolic (rowSubspace F A)).comap (rowAction F D) =
      (normalizer ((F.row ⊓ A : Subgroup G) : Set G)).subgroupOf (rowNormalizer F) := by
  ext g
  change (∀ v : Four, rowAction F D g v ∈ rowSubspace F A ↔ v ∈ rowSubspace F A) ↔
    (g : G) ∈ normalizer ((F.row ⊓ A : Subgroup G) : Set G)
  have hact (a : F.row) :
      rowAction F D g (rowCoordinates F a).toAdd ∈ rowSubspace F A ↔
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
    (BinaryLinear.parabolic (rowSubspace F F.plane)).comap (rowAction F D) =
      (planeNormalizer F).subgroupOf (rowNormalizer F) := by
  rw [parabolic_comap]
  ext g
  constructor
  · intro h
    have hh : (g : G) ∈ rowNormalizer F ⊓ normalizer
        ((F.row ⊓ F.plane : Subgroup G) : Set G) := ⟨g.property, h⟩
    rw [← D.row_plane_normalizer] at hh
    exact hh.2
  · intro h
    have hh : (g : G) ∈ rowNormalizer F ⊓ planeNormalizer F := ⟨g.property, h⟩
    rw [D.row_plane_normalizer] at hh
    exact hh.2

theorem plane_parabolic_comap :
    (BinaryLinear.parabolic (rowSubspace F F.threeSpace)).comap (rowAction F D) =
      (threeSpaceNormalizer F).subgroupOf (rowNormalizer F) := by
  rw [parabolic_comap]
  ext g
  constructor
  · intro h
    have hh : (g : G) ∈ rowNormalizer F ⊓ normalizer
        ((F.row ⊓ F.threeSpace : Subgroup G) : Set G) := ⟨g.property, h⟩
    rw [← D.row_threeSpace_normalizer] at hh
    exact hh.2
  · intro h
    have hh : (g : G) ∈ rowNormalizer F ⊓ threeSpaceNormalizer F := ⟨g.property, h⟩
    rw [D.row_threeSpace_normalizer] at hh
    exact hh.2

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

include D

/-- The point-line flag stabilizer is a maximal subgroup of the literal point stabilizer. -/
theorem line_flag_maximal :
    IsCoatom ((planeNormalizer F).subgroupOf (rowNormalizer F)) := by
  rw [← line_parabolic_comap F D]
  apply isCoatom_comap_of_surjective (rowAction_surjective F D)
  obtain ⟨h0, h1⟩ := rowSubspace_ne_bot_top F F.plane 3 (by decide) (by decide)
    (row_plane_finrank F)
  exact BinaryLinear.FourParabolicAction.parabolic_isCoatom _ h0 h1

/-- The point-plane flag stabilizer is maximal in the same literal point stabilizer. -/
theorem plane_flag_maximal :
    IsCoatom ((threeSpaceNormalizer F).subgroupOf (rowNormalizer F)) := by
  rw [← plane_parabolic_comap F D]
  apply isCoatom_comap_of_surjective (rowAction_surjective F D)
  obtain ⟨h0, h1⟩ := rowSubspace_ne_bot_top F F.threeSpace 2 (by decide) (by decide)
    (row_threeSpace_finrank F)
  exact BinaryLinear.FourParabolicAction.parabolic_isCoatom _ h0 h1

/-- The two source parabolics are distinct, since they stabilize subspaces of different dimensions. -/
theorem line_plane_flag_ne :
    (planeNormalizer F).subgroupOf (rowNormalizer F) ≠
      (threeSpaceNormalizer F).subgroupOf (rowNormalizer F) := by
  intro h
  rw [← line_parabolic_comap F D, ← plane_parabolic_comap F D] at h
  have hp := (Subgroup.comap_injective (rowAction_surjective F D)) h
  obtain ⟨h0, h1⟩ := rowSubspace_ne_bot_top F F.threeSpace 2 (by decide) (by decide)
    (row_threeSpace_finrank F)
  have he := BinaryLinear.FourParabolicAction.parabolic_le_imp_eq h0 h1 hp.le
  have hd := row_plane_finrank F
  rw [he, row_threeSpace_finrank F] at hd
  contradiction

/-- The two marked local flag subgroups generate the actual row normalizer.
This is the G₁ case of residual connectedness in source 41.1. -/
theorem row_flag_generate :
    (rowNormalizer F ⊓ planeNormalizer F) ⊔
      (rowNormalizer F ⊓ threeSpaceNormalizer F) = rowNormalizer F := by
  have hn : ¬ (threeSpaceNormalizer F).subgroupOf (rowNormalizer F) ≤
      (planeNormalizer F).subgroupOf (rowNormalizer F) := by
    intro h
    rcases (plane_flag_maximal F D).le_iff.mp h with he | he
    · exact (line_flag_maximal F D).ne_top he
    · exact line_plane_flag_ne F D he
  have hs : (planeNormalizer F).subgroupOf (rowNormalizer F) ⊔
      (threeSpaceNormalizer F).subgroupOf (rowNormalizer F) = ⊤ := by
    apply (line_flag_maximal F D).2
    refine lt_of_le_of_ne le_sup_left ?_
    intro he
    apply hn
    rw [he]
    exact le_sup_right
  have hm := congrArg (fun K : Subgroup (rowNormalizer F) => K.map (rowNormalizer F).subtype) hs
  simpa only [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype,
    inf_comm (planeNormalizer F) (rowNormalizer F),
    inf_comm (threeSpaceNormalizer F) (rowNormalizer F)] using hm

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
