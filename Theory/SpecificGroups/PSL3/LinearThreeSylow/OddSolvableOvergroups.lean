module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Solvable overgroups of the upper unitriangular subgroup

A solvable subgroup of SL₃ containing the full upper unipotent subgroup
is upper triangular. A forbidden lower entry, after upper row operations,
would supply an opposite root group and therefore a nontrivial perfect SL₂
subgroup. Passing through the actual scalar projection gives the PSL₃ result.

Source: Aschbacher–Smith, A.3.15, printed pp.50–51, the defining odd
linear-three branch used in Proposition 1.3.4, printed pp.510–511.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Subgroup
namespace Matrix.PSL3.LinearThree.OddSolvableOvergroups
variable (F : Type*) [Field F]
local notation "e10" => SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 0) (by decide)
local notation "e21" => SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide)

private theorem upper_val (u : U F) : (specialLinear F u).val = matrix F u := rfl

private theorem upper_mem (a b c : F) :
    specialLinear F ⟨a,b,c⟩ ∈ unipotentSL F :=
  (specialLinear_range F).le ⟨⟨a,b,c⟩, rfl⟩

private theorem lower10_of_first_column (K : Subgroup SL(3,F))
    (hU : unipotentSL F ≤ K) (g : SL(3,F)) (hg : g ∈ K)
    (h00 : g.val 0 0 = 0) (h20 : g.val 2 0 = 0) (h10 : g.val 1 0 ≠ 0) (t : F) :
    e10 t ∈ K := by
  let u := specialLinear F ⟨t * g.val 0 1 / g.val 1 0, 0,
    t * g.val 0 2 / g.val 1 0⟩
  have he : g * u = e10 t * g := by
    apply Subtype.ext
    change g.val * matrix F _ = (e10 t).val * g.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_three, h00, h20] <;> field_simp
  have hu : u ∈ K := hU (upper_mem F _ _ _)
  have hc := K.mul_mem (K.mul_mem hg hu) (K.inv_mem hg)
  rwa [he, mul_inv_cancel_right] at hc

private theorem lower21_of_first_column (K : Subgroup SL(3,F))
    (hU : unipotentSL F ≤ K) (g : SL(3,F)) (hg : g ∈ K)
    (h00 : g.val 0 0 = 0) (h10 : g.val 1 0 = 0) (h20 : g.val 2 0 ≠ 0) (t : F) :
    e21 t ∈ K := by
  let u := specialLinear F ⟨t * g.val 1 1 / g.val 2 0, 0,
    t * g.val 1 2 / g.val 2 0⟩
  have he : g * u = e21 t * g := by
    apply Subtype.ext
    change g.val * matrix F _ = (e21 t).val * g.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_three, h00, h10] <;> field_simp
  have hu : u ∈ K := hU (upper_mem F _ _ _)
  have hc := K.mul_mem (K.mul_mem hg hu) (K.inv_mem hg)
  rwa [he, mul_inv_cancel_right] at hc

private theorem lower21_of_second_column (K : Subgroup SL(3,F))
    (hU : unipotentSL F ≤ K) (g : SL(3,F)) (hg : g ∈ K)
    (h01 : g.val 0 1 = 0) (h10 : g.val 1 0 = 0) (h11 : g.val 1 1 = 0)
    (h21 : g.val 2 1 ≠ 0) (t : F) : e21 t ∈ K := by
  let u := specialLinear F ⟨0, t * g.val 1 2 / g.val 2 1, 0⟩
  have he : g * u = e21 t * g := by
    apply Subtype.ext
    change g.val * matrix F _ = (e21 t).val * g.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_three, h01, h10, h11]
    field_simp
  have hu : u ∈ K := hU (upper_mem F _ _ _)
  have hc := K.mul_mem (K.mul_mem hg hu) (K.inv_mem hg)
  rwa [he, mul_inv_cancel_right] at hc

private def block₀ : SL(2,F) →* SL(3,F) :=
  (SL3.blockEmbedding F).comp SpecialLinearGroup.toGL

private theorem block₀_val (x : SL(2,F)) :
    (block₀ F x).val = !![x.val 0 0,x.val 0 1,0; x.val 1 0,x.val 1 1,0; 0,0,1] := by
  change SL3.blockMatrix F (SpecialLinearGroup.toGL x) = _
  simp [SL3.blockMatrix]

private theorem block₀_injective : Function.Injective (block₀ F) :=
  (SL3.blockEmbedding_injective F).comp SpecialLinearGroup.toGL_injective

private def cycle : SL(3,F) :=
  ⟨!![0,0,1; 1,0,0; 0,1,0], by simp [Matrix.det_fin_three]⟩

private theorem cycle_inv_val : (cycle F)⁻¹.val = !![0,1,0; 0,0,1; 1,0,0] := by
  let d : SL(3,F) := ⟨!![0,1,0; 0,0,1; 1,0,0], by simp [Matrix.det_fin_three]⟩
  have he : cycle F * d = 1 := by
    apply Subtype.ext
    change (cycle F).val * d.val = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycle, d, Matrix.mul_apply, Fin.sum_univ_three]
  have hi : (cycle F)⁻¹ = d := inv_eq_of_mul_eq_one_right he
  exact congrArg (fun g : SL(3,F) => g.val) hi

private def block₁ : SL(2,F) →* SL(3,F) :=
  (MulAut.conj (cycle F)).toMonoidHom.comp (block₀ F)

private theorem block₁_val (x : SL(2,F)) :
    (block₁ F x).val = !![1,0,0; 0,x.val 0 0,x.val 0 1; 0,x.val 1 0,x.val 1 1] := by
  change (cycle F * block₀ F x * (cycle F)⁻¹).val = _
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, block₀_val, cycle_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycle, Matrix.mul_apply, Fin.sum_univ_three]

private theorem block₁_injective : Function.Injective (block₁ F) :=
  (MulAut.conj (cycle F)).injective.comp (block₀_injective F)

private theorem sl2_not_solvable [Finite F]
    (hF : 4 ≤ Nat.card F) : ¬ Group.IsSolvable SL(2,F) := by
  obtain ⟨a,ha⟩ : IsCyclic Fˣ := inferInstance
  have hasq : (a : F) ^ 2 ≠ 1 := by
    intro he
    grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers ha,
      orderOf_le_of_pow_eq_one zero_lt_two (Units.ext (by simpa using he))] at hF
    omega
  let : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top a.ne_zero hasq⟩
  let : Nontrivial SL(2,F) := ⟨⟨
    SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F),
    1, by
      intro h
      have he := congrArg (fun g : SL(2,F) => g.val 0 1) h
      simp [SpecialLinearGroup.transvection_coe] at he⟩⟩
  exact Group.IsPerfect.not_isSolvable _

private theorem not_contains_sl2 [Finite F]
    (hF : 4 ≤ Nat.card F) (K : Subgroup SL(3,F)) [Group.IsSolvable K]
    (f : SL(2,F) →* SL(3,F)) (hf : Function.Injective f)
    (hupper : ∀ t : F, f (SpecialLinearGroup.transvection
      (i := (0 : Fin 2)) (j := 1) zero_ne_one t) ∈ K)
    (hlower : ∀ t : F, f (SpecialLinearGroup.transvection
      (i := (1 : Fin 2)) (j := 0) one_ne_zero t) ∈ K) : False := by
  have hall (x : SL(2,F)) : f x ∈ K := by
    apply Matrix.SL2.transvection_induction (fun x => f x ∈ K) ?_ ?_ x
    · intro i j hij t
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hupper t
      · exact hlower t
      · exact (hij rfl).elim
    · intro x y hx hy
      simpa only [map_mul] using K.mul_mem hx hy
  let f' : SL(2,F) →* K := f.codRestrict K hall
  have hf' : Function.Injective f' := by
    intro x y h
    exact hf (congrArg Subtype.val h)
  exact sl2_not_solvable F hF (Group.isSolvable_of_isSolvable_injective hf')

private theorem no_lower10 [Finite F]
    (hF : 4 ≤ Nat.card F) (K : Subgroup SL(3,F)) [Group.IsSolvable K]
    (hU : unipotentSL F ≤ K) : ¬ ∀ t : F, e10 t ∈ K := by
  intro h
  apply not_contains_sl2 F hF K (block₀ F) (block₀_injective F)
  · intro t
    have he : block₀ F (SpecialLinearGroup.transvection
        (i := (0 : Fin 2)) (j := 1) zero_ne_one t) = specialLinear F ⟨t,0,0⟩ := by
      apply Subtype.ext
      rw [block₀_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, upper_val, matrix]
    rw [he]
    exact hU (upper_mem F _ _ _)
  · intro t
    have he : block₀ F (SpecialLinearGroup.transvection
        (i := (1 : Fin 2)) (j := 0) one_ne_zero t) = e10 t := by
      apply Subtype.ext
      rw [block₀_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe]
    rw [he]
    exact h t

private theorem no_lower21 [Finite F]
    (hF : 4 ≤ Nat.card F) (K : Subgroup SL(3,F)) [Group.IsSolvable K]
    (hU : unipotentSL F ≤ K) : ¬ ∀ t : F, e21 t ∈ K := by
  intro h
  apply not_contains_sl2 F hF K (block₁ F) (block₁_injective F)
  · intro t
    have he : block₁ F (SpecialLinearGroup.transvection
        (i := (0 : Fin 2)) (j := 1) zero_ne_one t) = specialLinear F ⟨0,t,0⟩ := by
      apply Subtype.ext
      rw [block₁_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, upper_val, matrix]
    rw [he]
    exact hU (upper_mem F _ _ _)
  · intro t
    have he : block₁ F (SpecialLinearGroup.transvection
        (i := (1 : Fin 2)) (j := 0) one_ne_zero t) = e21 t := by
      apply Subtype.ext
      rw [block₁_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe]
    rw [he]
    exact h t

variable [Finite F]

/-- A solvable overgroup of the full upper-unitriangular group in SL₃ fixes its flag. -/
theorem solvable_le_borelSL (hF : 4 ≤ Nat.card F)
    (K : Subgroup SL(3,F)) [Group.IsSolvable K]
    (hU : unipotentSL F ≤ K) : K ≤ borelSL F := by
  intro g hg
  have h20 : g.val 2 0 = 0 := by
    by_contra h20
    apply no_lower21 F hF K hU
    let u := specialLinear F ⟨0, -g.val 1 0 / g.val 2 0, -g.val 0 0 / g.val 2 0⟩
    let w := u * g
    have hw : w ∈ K := K.mul_mem (hU (upper_mem F _ _ _)) hg
    have hw00 : w.val 0 0 = 0 := by
      simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply, Fin.sum_univ_three, h20]
    have hw10 : w.val 1 0 = 0 := by
      simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply, Fin.sum_univ_three, h20]
    have hw20 : w.val 2 0 ≠ 0 := by
      simpa [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply, Fin.sum_univ_three] using h20
    exact lower21_of_first_column F K hU w hw hw00 hw10 hw20
  have h10 : g.val 1 0 = 0 := by
    by_contra h10
    apply no_lower10 F hF K hU
    let u := specialLinear F ⟨-g.val 0 0 / g.val 1 0, 0, 0⟩
    let w := u * g
    have hw : w ∈ K := K.mul_mem (hU (upper_mem F _ _ _)) hg
    have hw00 : w.val 0 0 = 0 := by
      simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply, Fin.sum_univ_three, h10]
    have hw20 : w.val 2 0 = 0 := by
      simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply, Fin.sum_univ_three, h20]
    have hw10 : w.val 1 0 ≠ 0 := by
      simpa [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply, Fin.sum_univ_three] using h10
    exact lower10_of_first_column F K hU w hw hw00 hw20 hw10
  have h21 : g.val 2 1 = 0 := by
    by_contra h21
    apply no_lower21 F hF K hU
    let u := specialLinear F ⟨0, -g.val 1 1 / g.val 2 1, -g.val 0 1 / g.val 2 1⟩
    let w := u * g
    have hw : w ∈ K := K.mul_mem (hU (upper_mem F _ _ _)) hg
    have hw01 : w.val 0 1 = 0 := by
      simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply, Fin.sum_univ_three, h21]
    have hw10 : w.val 1 0 = 0 := by
      simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply, Fin.sum_univ_three, h10, h20]
    have hw11 : w.val 1 1 = 0 := by
      simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply, Fin.sum_univ_three, h21]
    have hw21 : w.val 2 1 ≠ 0 := by
      simpa [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply, Fin.sum_univ_three] using h21
    exact lower21_of_second_column F K hU w hw hw01 hw10 hw11 hw21
  exact (mem_borelSL_iff F g).mpr ⟨h10, h20, h21⟩

/-- A solvable overgroup of the standard projective unipotent group lies in its Borel. -/
theorem solvable_le_borel (hF : 4 ≤ Nat.card F)
    (H : Subgroup PSL(3,F)) [Group.IsSolvable H]
    (hU : unipotent F ≤ H) : H ≤ borel F := by
  let : Group.IsSolvable (projection F).ker := by
    rw [projection_ker]
    exact Group.isSolvable_of_comm fun x y =>
      Subtype.ext ((mem_center_iff.mp x.property y).symm)
  let : Group.IsSolvable (H.comap (projection F)) :=
    isSolvable_comap_of_solvable_ker (projection F) H
  have hpre : unipotentSL F ≤ H.comap (projection F) := by
    intro u hu
    exact hU (mem_map_of_mem _ hu)
  have hB := solvable_le_borelSL F hF (H.comap (projection F)) hpre
  intro x hx
  obtain ⟨g, rfl⟩ := projection_surjective F x
  exact mem_map_of_mem (projection F) (hB hx)


end Matrix.PSL3.LinearThree.OddSolvableOvergroups
