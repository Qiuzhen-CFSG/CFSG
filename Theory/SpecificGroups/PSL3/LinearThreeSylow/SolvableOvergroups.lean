module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.GroupTheory.SolvableRadical.SolvableKernel


/-!
# Solvable overgroups of Sylow two-subgroups in PSL₃

Over a finite field of characteristic two with at least four elements, every
solvable subgroup containing the full upper-unitriangular group is upper
triangular. Consequently, every solvable overgroup of an arbitrary Sylow
two-subgroup of PSL₃ normalizes that supplied Sylow.

The matrix proof uses three pivots. If the bottom entry of the first column
is nonzero, upper-unitriangular row operations send that column to a multiple
of e₂. Conjugating the full first-row root plane then supplies every lower
(2,1) transvection. If only the middle entry is nonzero, the same argument
supplies the lower (1,0) root group. Once both entries vanish, a nonzero
(2,1) entry gives the lower (2,1) root group using the second column.
Each lower simple-root group, together with its upper opposite, generates
an embedded SL₂. That group is nontrivial and perfect when the field has
at least four elements, contradicting solvability.

The scalar center is abelian, so a solvable projective subgroup has a
solvable full preimage in SL₃. The standard Sylow normalizer calculation
and Sylow conjugacy finish the projective statement. No parabolic-placement
hypothesis, simplicity theorem, or exclusion of F₄ is used.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.3.38, printed pp.1135–1136, particularly the first sentence on p.1136.
The rank-one nonsolvability argument also occurs in this repository's
Chapter 1 `Placement.ParabolicBorel.RankOne`; the present proof depends only
on Theory and Mathlib and supplies the missing intrinsic overgroup result.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Subgroup
namespace Matrix.PSL3.LinearThree.SolvableOvergroups
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

private theorem sl2_not_solvable [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) : ¬ Group.IsSolvable SL(2,F) := by
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := by simpa using ha
  have hasq : (a : F) ^ 2 ≠ 1 := by
    intro h
    apply ha1
    exact (frobenius_inj F 2) (by simpa [frobenius_def] using h)
  let : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top a.ne_zero hasq⟩
  let : Nontrivial SL(2,F) := ⟨⟨
    SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F),
    1, by
      intro h
      have he := congrArg (fun g : SL(2,F) => g.val 0 1) h
      simp [SpecialLinearGroup.transvection_coe] at he⟩⟩
  exact Group.IsPerfect.not_isSolvable _

private theorem not_contains_sl2 [Finite F] [CharP F 2]
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

private theorem no_lower10 [Finite F] [CharP F 2]
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

private theorem no_lower21 [Finite F] [CharP F 2]
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
theorem solvable_le_borelSL [CharP F 2] (hF : 4 ≤ Nat.card F)
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
theorem solvable_le_borel [CharP F 2] (hF : 4 ≤ Nat.card F)
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

/-- Every solvable overgroup normalizes the supplied Sylow when the field has size 2ⁿ ≥ 4. -/
theorem solvable_overgroup_le_normalizer_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 PSL(3,F)) (H : Subgroup PSL(3,F))
    (hsol : Group.IsSolvable H) (hPH : (P : Subgroup PSL(3,F)) ≤ H) :
    H ≤ normalizer (P : Set PSL(3,F)) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hn
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(3,F) P
    (unipotentSylow F (by omega : 0 < n) hF)
  let e := MulAut.conj g
  have hP : (P : Subgroup PSL(3,F)).map e.toMonoidHom = unipotent F := by
    change ((g • P : Sylow 2 PSL(3,F)) : Subgroup PSL(3,F)) = _
    rw [hg]
    rfl
  let : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  have hUH : unipotent F ≤ H.map e.toMonoidHom := by
    rw [← hP]
    exact map_mono hPH
  have hN := (solvable_le_borel F hfour (H.map e.toMonoidHom) hUH).trans
    (borel_le_normalizer_unipotent F)
  rw [← hP, ← map_equiv_normalizer_eq (P : Subgroup PSL(3,F)) e] at hN
  exact (map_le_map_iff_of_injective e.injective).mp hN

/-- The intrinsic normalizer contract for the positive even exponents in source 15.3.38. -/
theorem solvable_overgroup_le_normalizer
    {n : ℕ} (hn : 0 < n) (heven : Even n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 PSL(3,F)) (H : Subgroup PSL(3,F))
    (hsol : Group.IsSolvable H) (hPH : (P : Subgroup PSL(3,F)) ≤ H) :
    H ≤ normalizer (P : Set PSL(3,F)) := by
  have htwo : 2 ≤ n := by
    obtain ⟨k, hk⟩ := heven
    omega
  exact solvable_overgroup_le_normalizer_of_two_le F htwo hF P H hsol hPH

end Matrix.PSL3.LinearThree.SolvableOvergroups
