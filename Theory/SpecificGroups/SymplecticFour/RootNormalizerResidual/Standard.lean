module

public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Theory.SpecificGroups.SymplecticFour.Sylow.Characters
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-!
# Standard symplectic root normalizers and centralizers

The normalizers of roots 0 and 4 are the point and plane parabolics. Comparing
entries in an intertwining equation forces the corresponding zero column or
block. Conversely, the symplectic inverse formula computes conjugation: its
root parameter is multiplied by the square of the point character or by the
plane determinant. In characteristic two their kernels are exactly the full
root centralizers and the published determinant-one local factors.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3c),
printed p.250 (PDF p.261), in the original type-C₂ matrix root convention.
-/

public section

open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual
variable {F : Type*} [Field F]
open scoped CharTwo
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

private theorem conjugate_matrix (g u : Sp F) :
    (g * u * g⁻¹).val = 1 + g.val * (u.val - 1) * (g⁻¹).val := by
  have h : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  change g.val * u.val * (g⁻¹).val = _
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]
  abel

private theorem root_zero_increment (t : F) :
    (rootElement 0 t).val - 1 = Matrix.single a c t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootElement, rootMatrix, fromBlocks, Matrix.single]

private theorem root_four_increment (t : F) :
    (rootElement 4 t).val - 1 = Matrix.single a d t + Matrix.single b c t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootElement, rootMatrix, fromBlocks, Matrix.single]

/-- Conjugation multiplies the long-root parameter by the squared point character. -/
theorem point_conjugate (g : Sp F) (hg : g ∈ pointParabolic) (t : F) :
    g * rootElement 0 t * g⁻¹ = rootElement 0 (g.val a a ^ 2 * t) := by
  apply Subtype.ext
  rw [conjugate_matrix, root_zero_increment, SymplecticGroup.coe_inv]
  have hz := (mem_pointParabolic_iff g).mp hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootElement, rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.single, Matrix.J, fromBlocks, Matrix.one_apply,
      hz.1, hz.2, pow_two]
  ring

variable [CharP F 2]

/-- Conjugation multiplies the short-root parameter by the plane determinant. -/
theorem plane_conjugate (g : Sp F) (hg : g ∈ planeParabolic) (t : F) :
    g * rootElement 4 t * g⁻¹ = rootElement 4
      ((g.val a a * g.val b b - g.val a b * g.val b a) * t) := by
  apply Subtype.ext
  rw [conjugate_matrix, root_four_increment, SymplecticGroup.coe_inv]
  have hz := (mem_planeParabolic_iff g).mp hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootElement, rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.single, Matrix.J, fromBlocks, Matrix.one_apply,
      hz, CharTwo.neg_eq, CharTwo.sub_eq_add] <;>
    ring_nf <;> simp

omit [CharP F 2] in
private theorem conjugate_parameter (r : Fin 8) (g : Sp F)
    (hg : g ∈ normalizer (RootSubgroup.group (F := F) r : Set (Sp F))) :
    ∃ t : F, g * rootElement r 1 = rootElement r t * g := by
  have h := (mem_normalizer_iff.mp hg (rootElement r 1)).mp
    ((RootSubgroup.mem_group_iff r _).mpr ⟨1, rfl⟩)
  obtain ⟨t, ht⟩ := (RootSubgroup.mem_group_iff r _).mp h
  exact ⟨t, by rw [ht, mul_assoc, inv_mul_cancel, mul_one]⟩

omit [CharP F 2] in
private theorem normalizer_zero_le : normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) ≤
    pointParabolic := by
  intro g hg
  obtain ⟨t, ht⟩ := conjugate_parameter 0 g hg
  have h (i j) := congrArg (fun x : Sp F => x.val i j) ht
  rw [mem_pointParabolic_iff]
  constructor
  · have hh := h b c
    simpa [rootElement, rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, fromBlocks, Matrix.single, Matrix.one_apply] using hh
  · intro i
    have hh := h (.inr i) c
    fin_cases i <;>
      simpa [rootElement, rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
        Fin.sum_univ_two, fromBlocks, Matrix.single, Matrix.one_apply] using hh

omit [CharP F 2] in
private theorem normalizer_four_le : normalizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) ≤
    planeParabolic := by
  intro g hg
  obtain ⟨t, ht⟩ := conjugate_parameter 4 g hg
  have h (i j) := congrArg (fun x : Sp F => x.val i j) ht
  rw [mem_planeParabolic_iff]
  intro i j
  have hh := h (.inr i) (.inr (1 - j))
  fin_cases i <;> fin_cases j <;>
    simpa [rootElement, rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, fromBlocks, Matrix.single, Matrix.one_apply] using hh

omit [CharP F 2] in
/-- The full normalizer of the standard long root is the point parabolic. -/
theorem normalizer_zero_eq : normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) =
    pointParabolic := by
  apply le_antisymm normalizer_zero_le
  apply le_set_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 0 x).mp hx
  rw [point_conjugate g hg]
  exact (RootSubgroup.mem_group_iff 0 _).mpr ⟨_, rfl⟩

/-- The full normalizer of the standard short root is the plane parabolic. -/
theorem normalizer_four_eq : normalizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) =
    planeParabolic := by
  apply le_antisymm normalizer_four_le
  apply le_set_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 4 x).mp hx
  rw [plane_conjugate g hg]
  exact (RootSubgroup.mem_group_iff 4 _).mpr ⟨_, rfl⟩

omit [CharP F 2] in
private theorem centralizer_iff (r : Fin 8) (g : Sp F) :
    g ∈ centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) ↔
      ∀ t : F, g * rootElement r t * g⁻¹ = rootElement r t := by
  rw [mem_centralizer_iff]
  constructor
  · intro h t
    rw [← h _ ((RootSubgroup.mem_group_iff r _).mpr ⟨t, rfl⟩),
      mul_assoc, mul_inv_cancel, mul_one]
  · intro h x hx
    obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff r x).mp hx
    exact ((mul_inv_eq_iff_eq_mul).mp (h t)).symm

/-- The full long-root centralizer is the point determinant kernel. -/
theorem centralizer_zero_eq : centralizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) =
    pointLocal := by
  ext g
  constructor
  · intro hg
    have hp : g ∈ pointParabolic := normalizer_zero_le (centralizer_le_normalizer _ hg)
    apply (mem_pointLocal_iff g).mpr
    refine ⟨hp, ?_⟩
    have h := (centralizer_iff 0 g).mp hg 1
    rw [point_conjugate g hp] at h
    have hh := RootSubgroup.element_injective 0 h
    exact CharTwo.sq_injective (by simpa using hh)
  · intro hg
    obtain ⟨hp, ha⟩ := (mem_pointLocal_iff g).mp hg
    apply (centralizer_iff 0 g).mpr
    intro t
    rw [point_conjugate g hp, ha]
    simp

/-- The full short-root centralizer is the plane determinant kernel. -/
theorem centralizer_four_eq : centralizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) =
    planeLocal := by
  ext g
  constructor
  · intro hg
    have hp : g ∈ planeParabolic := normalizer_four_le (centralizer_le_normalizer _ hg)
    apply (mem_planeLocal_iff g).mpr
    refine ⟨hp, ?_⟩
    have h := (centralizer_iff 4 g).mp hg 1
    rw [plane_conjugate g hp] at h
    simpa using RootSubgroup.element_injective 4 h
  · intro hg
    obtain ⟨hp, ha⟩ := (mem_planeLocal_iff g).mp hg
    apply (centralizer_iff 4 g).mpr
    intro t
    rw [plane_conjugate g hp, ha, one_mul]
end Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual
