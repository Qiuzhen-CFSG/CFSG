module

public import Theory.SpecificGroups.SymplecticFour.LocalFactors
public import Theory.Representation.FirstCohomologySymplecticFour.Generation
import Mathlib.Tactic.FinCases
/-!
# Generation and properness of the symplectic four-space parabolics

The root families lying in the two flag stabilizers supply six of the eight
standard roots. Two explicit Weyl conjugations supply the remaining roots,
so symplectic Gaussian elimination proves generation. Individual root elements
also witness that both parabolics are proper and distinct. These arguments work
over every field. Relative normality of the determinant kernels shows that the
whole flag stabilizer normalizes their intersection.

Source: the concrete Sp₄ flag amalgam in Aschbacher--Smith F.1.12(I)(2),
printed pp.262--264. Root conventions and elimination are from
`Theory.Representation.FirstCohomologySymplecticFour.Generation`.
-/

@[expose] public section
open Matrix
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]

/-- The incident point and plane stabilizers are distinct. -/
theorem pointParabolic_ne_planeParabolic : pointParabolic (F := F) ≠ planeParabolic := by
  intro h
  have hp : rootElement 3 (1 : F) ∈ pointParabolic := by
    simp [mem_pointParabolic_iff, rootElement, rootMatrix, fromBlocks, single]
  rw [h, mem_planeParabolic_iff] at hp
  have := hp 1 1
  simp [rootElement, rootMatrix, fromBlocks, single] at this

/-- A lower long root moves the standard point. -/
theorem pointParabolic_ne_top : pointParabolic (F := F) ≠ ⊤ := by
  intro h
  have hp : rootElement 1 (1 : F) ∈ pointParabolic := h ▸ Subgroup.mem_top _
  have := ((mem_pointParabolic_iff _).mp hp).2 0
  simp [rootElement, rootMatrix, fromBlocks, single] at this

/-- A lower long root moves the standard plane. -/
theorem planeParabolic_ne_top : planeParabolic (F := F) ≠ ⊤ := by
  intro h
  have hp : rootElement 3 (1 : F) ∈ planeParabolic := h ▸ Subgroup.mem_top _
  have := (mem_planeParabolic_iff _).mp hp 1 1
  simp [rootElement, rootMatrix, fromBlocks, single] at this

local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

private lemma root_mul_apply (r : Fin 8) (t : F)
    (g : Matrix.symplecticGroup (Fin 2) F) (i j : Fin 2 ⊕ Fin 2) :
    (rootElement r t * g).val i j =
    ![Sum.elim ![g.val a j + t * g.val c j, g.val b j] ![g.val c j, g.val d j],
      Sum.elim ![g.val a j, g.val b j] ![g.val c j + t * g.val a j, g.val d j],
      Sum.elim ![g.val a j, g.val b j + t * g.val d j] ![g.val c j, g.val d j],
      Sum.elim ![g.val a j, g.val b j] ![g.val c j, g.val d j + t * g.val b j],
      Sum.elim ![g.val a j + t * g.val d j, g.val b j + t * g.val c j]
        ![g.val c j, g.val d j],
      Sum.elim ![g.val a j, g.val b j]
        ![g.val c j + t * g.val b j, g.val d j + t * g.val a j],
      Sum.elim ![g.val a j + t * g.val b j, g.val b j]
        ![g.val c j, g.val d j - t * g.val c j],
      Sum.elim ![g.val a j, g.val b j + t * g.val a j]
        ![g.val c j - t * g.val d j, g.val d j]] r i := by
  change (rootMatrix r t * g.val) i j = _
  fin_cases r <;> rcases i with i | i <;> fin_cases i <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.one_apply, Matrix.fromBlocks, sub_mul, add_comm]

-- Mixed Weyl element transports the second long root to the first.
private lemma first_lower_root (t : F) : rootElement 1 t =
    rootElement 6 1 * rootElement 7 (-1) * rootElement 6 1 *
      rootElement 3 t *
    (rootElement 6 (-1) * rootElement 7 1 * rootElement 6 (-1)) := by
  simp only [mul_assoc]
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp only [root_mul_apply]
  all_goals simp [rootElement, rootMatrix, fromBlocks, single]

private lemma lower_short_root (t : F) : rootElement 5 t =
    rootElement 2 1 * rootElement 3 (-1) * rootElement 2 1 *
      rootElement 7 (-t) *
    (rootElement 2 (-1) * rootElement 3 1 * rootElement 2 (-1)) := by
  simp only [mul_assoc]
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp only [root_mul_apply]
  all_goals simp [rootElement, rootMatrix, fromBlocks, single]
private lemma root_mem_parabolics_sup (r : Fin 8) (t : F) (h₁ : r ≠ 1) (h₅ : r ≠ 5) :
    rootElement r t ∈ pointParabolic (F := F) ⊔ planeParabolic := by
  fin_cases r
  case «1» => exact (h₁ rfl).elim
  case «5» => exact (h₅ rfl).elim
  case «3» =>
    exact Subgroup.mem_sup_left (by
      simp [mem_pointParabolic_iff, rootElement, rootMatrix, fromBlocks, single])
  all_goals exact Subgroup.mem_sup_right (by
    simp [mem_planeParabolic_iff, rootElement, rootMatrix, fromBlocks, single])

/-- The two incident flag parabolics generate the actual matrix group Sp₄. -/
theorem parabolics_sup_eq_top :
    pointParabolic (F := F) ⊔ planeParabolic = ⊤ := by
  apply eq_top_of_rootElement_mem
  intro r t
  by_cases h₁ : r = 1
  · subst r
    rw [first_lower_root]
    repeat' apply Subgroup.mul_mem
    all_goals exact root_mem_parabolics_sup _ _ (by decide) (by decide)
  by_cases h₅ : r = 5
  · subst r
    rw [lower_short_root]
    repeat' apply Subgroup.mul_mem
    all_goals exact root_mem_parabolics_sup _ _ (by decide) (by decide)
  exact root_mem_parabolics_sup r t h₁ h₅

/-- Relative normality of both determinant kernels implies normalization by
 the whole flag stabilizer. The reverse inclusion is a separate geometric claim. -/
theorem borel_le_normalizer_unipotent :
    borel (F := F) ≤ Subgroup.normalizer (unipotent (F := F)) := by
  exact (inf_le_inf
    (Subgroup.le_normalizer_of_normal_subgroupOf pointLocal_le)
    (Subgroup.le_normalizer_of_normal_subgroupOf planeLocal_le)).trans
      Subgroup.inf_normalizer_le_normalizer_inf

instance unipotent_normal_in_borel :
    ((unipotent (F := F)).subgroupOf borel).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer unipotent_le_borel).mpr
    borel_le_normalizer_unipotent

end Theory.SpecificGroups.SymplecticFour
