module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# Proper overgroups of the degree-three Borel

Every proper subgroup of SL₃(F) containing the standard Borel fixes the
standard point or its incident line. The same conclusion descends through
the actual projective quotient, over any finite field.

If a matrix has nonzero bottom-left entry, upper row operations make its
first column a multiple of the last basis vector. Conjugating the first-row
root plane then supplies the full opposite corner root group. Commutators
with the upper simple roots and Gaussian elimination generate SL₃(F).
Thus properness forces every bottom-left entry to vanish. The same entry
in a product is the product of the two lower adjacent entries, forcing one
of those entries to vanish throughout the subgroup.

The pivot calculation adapts the first-column argument in
`LinearThreeSylow.SolvableOvergroups`, without its solvability hypothesis.
Source: Aschbacher--Smith, the characteristic-two paragraph of 15.3.43,
printed p.1140, and the rank-two list A.2.4, p.33. This supplies arbitrary
Borel-overgroup coverage, including the Borel itself.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry Subgroup
namespace Matrix.PSL3.LinearThree.BorelOvergroups
variable (F : Type*) [Field F] [Finite F]

local notation "e01" => SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1) (by decide)
local notation "e12" => SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide)
local notation "e10" => SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 0) (by decide)
local notation "e20" => SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 0) (by decide)
local notation "e21" => SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide)

omit [Finite F] in
private theorem upper_val (u : U F) : (specialLinear F u).val = matrix F u := rfl

private theorem upper_mem (a b c : F) : specialLinear F ⟨a,b,c⟩ ∈ borelSL F :=
  unipotentSL_le_borelSL F ((specialLinear_range F).le ⟨⟨a,b,c⟩, rfl⟩)

private theorem upper_root_mem (i j : Fin 3) (hij : i < j) (t : F) :
    SpecialLinearGroup.transvection (ne_of_lt hij) t ∈ borelSL F := by
  rw [mem_borelSL_iff]
  fin_cases i <;> fin_cases j <;> simp_all [SpecialLinearGroup.transvection_coe] <;>
    norm_num at hij

omit [Finite F] in
private theorem lower10_identity (t : F) :
    e10 t = e12 (1 : F) * e20 t * e12 (-1 : F) * e20 (-t) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

omit [Finite F] in
private theorem lower21_identity (t : F) :
    e21 t = e20 t * e01 (1 : F) * e20 (-t) * e01 (-1 : F) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

private theorem eq_top_of_lower20 (K : Subgroup SL(3,F)) (hB : borelSL F ≤ K)
    (h20 : ∀ t : F, e20 t ∈ K) : K = ⊤ := by
  have h10 (t : F) : e10 t ∈ K := by
    rw [lower10_identity]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hB (upper_root_mem F 1 2 (by decide) 1))
      (h20 t)) (hB (upper_root_mem F 1 2 (by decide) (-1)))) (h20 (-t))
  have h21 (t : F) : e21 t ∈ K := by
    rw [lower21_identity]
    exact K.mul_mem (K.mul_mem (K.mul_mem (h20 t)
      (hB (upper_root_mem F 0 1 (by decide) 1))) (h20 (-t)))
      (hB (upper_root_mem F 0 1 (by decide) (-1)))
  apply top_unique
  intro g _
  apply SpecialLinearGroup.diagonal_transvection_induction' (fun g => g ∈ K) g
  · intro i j hij c hc
    apply hB
    rw [mem_borelSL_iff]
    simp [SpecialLinearGroup.diag2n_coe]
  · intro i j hij t
    by_cases hlt : i < j
    · exact hB (upper_root_mem F i j hlt t)
    · fin_cases i <;> fin_cases j <;> simp_all <;> exact (hij rfl).elim
  · exact fun _ _ => K.mul_mem

private theorem lower20_of_first_column (K : Subgroup SL(3,F))
    (hB : borelSL F ≤ K) (g : SL(3,F)) (hg : g ∈ K)
    (h00 : g.val 0 0 = 0) (h10 : g.val 1 0 = 0) (h20 : g.val 2 0 ≠ 0) (t : F) :
    e20 t ∈ K := by
  let u := specialLinear F ⟨t * g.val 0 1 / g.val 2 0, 0,
    t * g.val 0 2 / g.val 2 0⟩
  have he : g * u = e20 t * g := by
    apply Subtype.ext
    change g.val * matrix F _ = (e20 t).val * g.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_three, h00, h10] <;> field_simp
  have hu : u ∈ K := hB (upper_mem F _ _ _)
  have hc := K.mul_mem (K.mul_mem hg hu) (K.inv_mem hg)
  rwa [he, mul_inv_cancel_right] at hc

private theorem bottom_left_eq_zero (K : Subgroup SL(3,F))
    (hB : borelSL F ≤ K) (hK : K ≠ ⊤) (g : SL(3,F)) (hg : g ∈ K) :
    g.val 2 0 = 0 := by
  by_contra h20
  apply hK
  apply eq_top_of_lower20 F K hB
  let u := specialLinear F ⟨0, -g.val 1 0 / g.val 2 0, -g.val 0 0 / g.val 2 0⟩
  let w := u * g
  have hw : w ∈ K := K.mul_mem (hB (upper_mem F _ _ _)) hg
  have hw00 : w.val 0 0 = 0 := by
    simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply,
      Fin.sum_univ_three, h20]
  have hw10 : w.val 1 0 = 0 := by
    simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply,
      Fin.sum_univ_three, h20]
  have hw20 : w.val 2 0 ≠ 0 := by
    simpa [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply,
      Fin.sum_univ_three] using h20
  exact lower20_of_first_column F K hB w hw hw00 hw10 hw20

/-- Every proper subgroup containing the full standard Borel fixes the
standard point or the standard line. -/
theorem overgroup_borelSL (K : Subgroup SL(3,F)) (hB : borelSL F ≤ K) (hK : K ≠ ⊤) :
    K ≤ pointParabolicSL F ∨ K ≤ lineParabolicSL F := by
  classical
  by_cases hp : K ≤ pointParabolicSL F
  · exact Or.inl hp
  · right
    obtain ⟨g, hg, hgp⟩ := SetLike.not_le_iff_exists.mp hp
    have hg20 := bottom_left_eq_zero F K hB hK g hg
    have hg10 : g.val 1 0 ≠ 0 := by
      intro hz
      exact hgp ((mem_pointParabolicSL_iff F g).mpr ⟨hz, hg20⟩)
    intro h hh
    have hh20 := bottom_left_eq_zero F K hB hK h hh
    have hprod := bottom_left_eq_zero F K hB hK (h * g) (K.mul_mem hh hg)
    have hz : h.val 2 1 * g.val 1 0 = 0 := by
      simpa [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
        hg20, hh20] using hprod
    exact (mem_lineParabolicSL_iff F h).mpr ⟨hh20, (mul_eq_zero.mp hz).resolve_right hg10⟩

/-- Every proper projective Borel overgroup lies in one of the two full
standard parabolics. -/
theorem overgroup_borel (K : Subgroup PSL(3,F)) (hB : borel F ≤ K) (hK : K ≠ ⊤) :
    K ≤ pointParabolic F ∨ K ≤ lineParabolic F := by
  have hpre : K.comap (projection F) ≠ ⊤ := by
    intro h
    apply hK
    rw [← map_comap_eq_self_of_surjective (projection_surjective F) K, h]
    exact map_top_of_surjective _ (projection_surjective F)
  have hBpre : borelSL F ≤ K.comap (projection F) := by
    intro g hg
    exact hB (mem_map_of_mem _ hg)
  rcases overgroup_borelSL F _ hBpre hpre with hp | hp
  · left
    simpa only [pointParabolic, lineParabolic,
      map_comap_eq_self_of_surjective (projection_surjective F)] using
      map_mono (f := projection F) hp
  · right
    simpa only [pointParabolic, lineParabolic,
      map_comap_eq_self_of_surjective (projection_surjective F)] using
      map_mono (f := projection F) hp
end Matrix.PSL3.LinearThree.BorelOvergroups
