module
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry.RootGeneration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Extracting an opposite symplectic root from a nonorthogonal point

If a matrix g has a nonzero entry in position (f₀,e₀), three positive-root
operations send its first column to a nonzero multiple of f₀. The symplectic
equation determines the paired row. Conjugation by the reduced matrix thus
sends the entire first upper long-root group to the first lower long-root
group. A subgroup containing g and the standard unipotent subgroup is
therefore all of Sp₄.

The calculation uses the full matrix carrier and works over every field of
characteristic two. It supplies the geometric generation step for the
Sylow-overgroup placement used in Aschbacher–Smith, Lemma 15.3.28, printed
p.1131 (PDF p.1148), with B.5.5–6, printed pp.104–105.
-/

public section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement.OvergroupGeometry
variable {K : Type*} [Field K] [CharP K 2]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

omit [CharP K 2] in
private lemma root0_mul_apply (t : K) (g : Sp K) (i j : Fin 2 ⊕ Fin 2) :
    (rootElement 0 t * g).val i j =
      if i = a then g.val a j + t * g.val c j else g.val i j := by
  change (rootMatrix 0 t * g.val) i j = _
  rcases i with i | i <;> fin_cases i <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.single, Matrix.one_apply, Matrix.fromBlocks]

omit [CharP K 2] in
private lemma root4_mul_apply (t : K) (g : Sp K) (i j : Fin 2 ⊕ Fin 2) :
    (rootElement 4 t * g).val i j =
      if i = a then g.val a j + t * g.val d j
      else if i = b then g.val b j + t * g.val c j else g.val i j := by
  change (rootMatrix 4 t * g.val) i j = _
  rcases i with i | i <;> fin_cases i <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.single, Matrix.one_apply, Matrix.fromBlocks]

omit [CharP K 2] in
private lemma root6_mul_apply (t : K) (g : Sp K) (i j : Fin 2 ⊕ Fin 2) :
    (rootElement 6 t * g).val i j =
      if i = a then g.val a j + t * g.val b j
      else if i = d then g.val d j - t * g.val c j else g.val i j := by
  change (rootMatrix 6 t * g.val) i j = _
  rcases i with i | i <;> fin_cases i <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.single, Matrix.one_apply, Matrix.fromBlocks, sub_mul, add_comm]

private lemma row_a_of_column (g : Sp K) (z : K)
    (hcol : ∀ i, g.val i a = if i = c then z else 0) (j : Fin 2 ⊕ Fin 2) :
    z * g.val a j = if j = c then 1 else 0 := by
  have hp := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M a j)
    (SymplecticGroup.mem_iff'.mp g.property)
  rcases j with j | j <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hcol,
      Matrix.J, fromBlocks, Matrix.one_apply, CharTwo.neg_eq] at hp ⊢
  all_goals exact hp

private lemma conjugate_long_of_column (g : Sp K) (z s : K)
    (hcol : ∀ i, g.val i a = if i = c then z else 0) :
    g * rootElement 0 s * g⁻¹ = rootElement 1 (z * z * s) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  change g.val * rootMatrix 0 s = rootMatrix 1 (z * z * s) * g.val
  have hrow := row_a_of_column g z hcol
  have hz : z ≠ 0 := by
    intro hz
    have hc := hrow c
    simp [hz] at hc
  have hr (j : Fin 2 ⊕ Fin 2) : g.val a j = (if j = c then 1 else 0) / z := by
    apply (eq_div_iff hz).mpr
    simpa only [mul_comm] using hrow j
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, mul_apply, Fintype.sum_sum_type,
      fromBlocks, single, Matrix.one_apply, hcol, hr]
  all_goals field_simp

omit [CharP K 2] in
private lemma exists_column_reduction (g : Sp K) (hz : g.val c a ≠ 0) :
    ∃ u ∈ unipotent (F := K),
      ∀ i, (u * g).val i a = if i = c then g.val c a else 0 := by
  let x := g.val a a
  let y := g.val b a
  let z := g.val c a
  let w := g.val d a
  let u := rootElement 0 (-(x + w / z * y) / z) *
    (rootElement 4 (-y / z) * rootElement 6 (w / z))
  refine ⟨u, ?_, ?_⟩
  · exact (unipotent (F := K)).mul_mem
      (positive_root_mem_unipotent 0 _ (by simp))
      ((unipotent (F := K)).mul_mem (positive_root_mem_unipotent 4 _ (by simp))
        (positive_root_mem_unipotent 6 _ (by simp)))
  · intro i
    rcases i with i | i <;> fin_cases i <;>
      simp [u, mul_assoc, root0_mul_apply, root4_mul_apply, root6_mul_apply, x, y, z, w]
    all_goals (field_simp [hz]; ring)

/-- A unipotent overgroup moving e₀ to a nonorthogonal vector is the whole group. -/
theorem eq_top_of_nonorthogonal_element (H : Subgroup (Sp K))
    (hU : unipotent ≤ H) (g : Sp K) (hg : g ∈ H) (hz : g.val c a ≠ 0) : H = ⊤ := by
  obtain ⟨u, hu, hcol⟩ := exists_column_reduction g hz
  have hm : u * g ∈ H := H.mul_mem (hU hu) hg
  apply eq_top_of_unipotent_le_of_opposite_long_root H hU
  intro t
  have h := H.mul_mem
    (H.mul_mem hm (hU (positive_root_mem_unipotent 0
      (t / (g.val c a * g.val c a)) (by simp)))) (H.inv_mem hm)
  rw [conjugate_long_of_column (u * g) (g.val c a) _ hcol] at h
  have he : g.val c a * g.val c a * (t / (g.val c a * g.val c a)) = t := by
    field_simp [hz]
  rwa [he] at h

end Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement.OvergroupGeometry
