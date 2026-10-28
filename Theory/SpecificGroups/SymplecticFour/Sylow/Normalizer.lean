module

public import Theory.SpecificGroups.SymplecticFour.Sylow.Characters
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics
import Mathlib.Tactic.FinCases
/-!
# Recovering the symplectic flag from its unipotent subgroup

The fixed vectors of the determinant-one flag subgroup are exactly the
standard point. Its fixed vectors modulo that point are exactly the standard
plane. Four positive root families suffice to recover these two subspaces.
Every normalizing matrix therefore preserves the flag. Combined with relative
normality of the determinant kernels this proves that the full normalizer is
the Borel. No finiteness, characteristic, or Sylow assumption is needed.

Source: the concrete symplectic flag realization underlying Aschbacher--Smith,
F.1.12(I)(2), printed pp.262--264.
-/

@[expose] public section
open Matrix
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]

lemma positive_root_mem_unipotent (r : Fin 8) (t : F)
    (hr : r = 0 ∨ r = 2 ∨ r = 4 ∨ r = 6) : rootElement r t ∈ unipotent := by
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp [mem_unipotent_iff, mem_borel_iff, rootElement, rootMatrix, fromBlocks, single]

lemma unipotent_fixes_point {u : Sp F} (hu : u ∈ unipotent) {x : Vector F}
    (hx : x ∈ point F) : u • x = x := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  change toLinear u (a • e 0) = a • e 0
  rw [map_smul]
  congr 1
  obtain ⟨hb, h₀, _⟩ := (mem_unipotent_iff u).mp hu
  obtain ⟨h₁, h₂⟩ := (mem_borel_iff u).mp hb
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [toLinear_apply, smul_eq_mulVec, e, mulVec_single, h₀, h₁, h₂]

lemma fixedBy_unipotent_iff (x : Vector F) :
    (∀ u ∈ unipotent (F := F), u • x = x) ↔ x ∈ point F := by
  constructor
  · intro h
    have h₀ := congrFun (h (rootElement 0 1)
      (positive_root_mem_unipotent 0 1 (by simp))) (.inl 0)
    have h₂ := congrFun (h (rootElement 2 1)
      (positive_root_mem_unipotent 2 1 (by simp))) (.inl 1)
    have h₆ := congrFun (h (rootElement 6 1)
      (positive_root_mem_unipotent 6 1 (by simp))) (.inl 0)
    simp [rootElement, rootMatrix, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks, single, Matrix.one_apply] at h₀ h₂ h₆
    rw [mem_point_iff]
    refine ⟨h₆, ?_⟩
    intro i
    fin_cases i <;> assumption
  · intro hx u hu
    exact unipotent_fixes_point hu hx

lemma unipotent_trivial_on_plane_mod_point {u : Sp F} (hu : u ∈ unipotent)
    {x : Vector F} (hx : x ∈ plane F) : u • x - x ∈ point F := by
  obtain ⟨hb, _, h₁⟩ := (mem_unipotent_iff u).mp hu
  obtain ⟨h₀, h₂⟩ := (mem_borel_iff u).mp hb
  rw [mem_point_iff]
  constructor
  · simp [smul_eq_mulVec, mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, hx 0, hx 1, h₀, h₁]
  · intro i
    simp [smul_eq_mulVec, mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, hx 0, hx 1, hx i, h₂]

lemma fixedModulo_point_iff (x : Vector F) :
    (∀ u ∈ unipotent (F := F), u • x - x ∈ point F) ↔ x ∈ plane F := by
  constructor
  · intro h
    have h₂ := (mem_point_iff _).mp (h (rootElement 2 1)
      (positive_root_mem_unipotent 2 1 (by simp))) |>.1
    have h₄ := (mem_point_iff _).mp (h (rootElement 4 1)
      (positive_root_mem_unipotent 4 1 (by simp))) |>.1
    simp [rootElement, rootMatrix, mulVec, dotProduct,
      Fintype.sum_sum_type, fromBlocks, single, Matrix.one_apply] at h₂ h₄
    intro i
    fin_cases i <;> assumption
  · intro hx u hu
    exact unipotent_trivial_on_plane_mod_point hu hx

lemma normalizer_unipotent_le_pointParabolic :
    Subgroup.normalizer (unipotent (F := F)) ≤ pointParabolic (F := F) := by
  intro g hg
  rw [pointParabolic, mem_stabilizer_iff]
  intro x hx
  apply (fixedBy_unipotent_iff _).mp
  intro u hu
  have hv : g⁻¹ * u * g ∈ unipotent :=
    (Subgroup.mem_normalizer_iff''.mp hg u).mp hu
  have h := unipotent_fixes_point hv hx
  have h' := congrArg (fun y => g • y) h
  simpa only [mul_smul, smul_inv_smul] using h'

lemma normalizer_unipotent_le_borel :
    Subgroup.normalizer (unipotent (F := F)) ≤ borel (F := F) := by
  intro g hg
  have hp := normalizer_unipotent_le_pointParabolic hg
  refine ⟨hp, ?_⟩
  change g ∈ planeParabolic
  rw [planeParabolic, mem_stabilizer_iff]
  intro x hx
  apply (fixedModulo_point_iff _).mp
  intro u hu
  have hv : g⁻¹ * u * g ∈ unipotent :=
    (Subgroup.mem_normalizer_iff''.mp hg u).mp hu
  have h := unipotent_trivial_on_plane_mod_point hv hx
  have h' := (mem_stabilizer_iff (point F) g).mp hp _ h
  change toLinear g (_ - _) ∈ point F at h'
  rw [map_sub] at h'
  simpa only [toLinear_apply, mul_smul, smul_inv_smul] using h'

lemma borel_eq_normalizer_unipotent :
    borel (F := F) = Subgroup.normalizer (unipotent (F := F)) :=
  le_antisymm borel_le_normalizer_unipotent normalizer_unipotent_le_borel
end Theory.SpecificGroups.SymplecticFour
