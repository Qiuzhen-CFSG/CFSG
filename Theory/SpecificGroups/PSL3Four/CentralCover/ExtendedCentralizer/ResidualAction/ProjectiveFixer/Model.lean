module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.Projection
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# A concrete Sylow three-subgroup of PSL₃(4)

The diagonal matrices `diag(1,u,u⁻¹)`, for `u ∈ F₄ˣ`, commute projectively
with the permutation matrix of a three-cycle. Their projective images have
trivial intersection, so multiplication embeds `F₄ˣ × C₃` with image of order
nine. The known order of PSL₃(4) makes this image Sylow.

The scalar test `project_eq_iff` retains the actual central quotient and is
also the interface for the subsequent pointwise-fixer calculation.

Source: the matrix calculation underlying Aschbacher--Smith 15.3.38,
printed pp.1136--1137, manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer

theorem unit_cube (u : Fˣ) : u ^ 3 = 1 := by
  have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, card_F]
  simpa only [hc] using (pow_card_eq_one' : u ^ Nat.card Fˣ = 1)

theorem unit_inv (u : Fˣ) : u⁻¹ = u ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [← pow_succ'] using unit_cube u

def diagonalSL : Fˣ →* SL where
  toFun u := ⟨!![1,0,0;0,(u : F),0;0,0,(↑u⁻¹ : F)], by
    simp [Matrix.det_fin_three]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by
    apply Subtype.ext
    change !![1,0,0;0,↑(u*v),0;0,0,↑((u*v)⁻¹)] =
      !![1,0,0;0,(u : F),0;0,0,↑u⁻¹] * !![1,0,0;0,(v : F),0;0,0,↑v⁻¹]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

def cycleSL : SL := ⟨!![0,1,0;0,0,1;1,0,0], by simp [Matrix.det_fin_three]⟩

def project : SL →* PSL := QuotientGroup.mk' (center SL)
def diagonal : Fˣ →* PSL := project.comp diagonalSL
def cycle : PSL := project cycleSL

theorem project_eq_iff (A B : SL) : project A = project B ↔
    ∃ r : F, r ^ 3 = 1 ∧ A.val = Matrix.scalar (Fin 3) r * B.val := by
  constructor
  · intro h
    have hz : A * B⁻¹ ∈ center SL := by
      apply (QuotientGroup.eq_one_iff _).mp
      change project (A * B⁻¹) = 1
      rw [map_mul, map_inv, h, mul_inv_cancel]
    obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hz
    refine ⟨r, hr, ?_⟩
    rw [he]
    change A.val = ((A * B⁻¹) * B).val
    simp
  · rintro ⟨r, hr, he⟩
    have hz : A * B⁻¹ ∈ center SL := by
      apply SpecialLinearGroup.mem_center_iff.mpr
      refine ⟨r, hr, ?_⟩
      change Matrix.scalar (Fin 3) r = A.val * B⁻¹.val
      rw [he, mul_assoc]
      have hBB : B.val * B⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel B)
      rw [hBB, mul_one]
    have h := (QuotientGroup.eq_one_iff _).mpr hz
    change project (A * B⁻¹) = 1 at h
    rw [map_mul, map_inv, mul_inv_eq_one] at h
    exact h

theorem cycleSL_cube : cycleSL ^ 3 = 1 := by
  apply Subtype.ext
  change (!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  simp [pow_succ, Matrix.one_fin_three]

theorem cycle_cube : cycle ^ 3 = 1 := by
  rw [cycle, ← map_pow, cycleSL_cube, map_one]

theorem cycle_ne_one : cycle ≠ 1 := by
  intro h
  have hz : cycleSL ∈ center SL := (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨r, _, he⟩ := SpecialLinearGroup.mem_center_iff.mp hz
  have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 1) he
  exact zero_ne_one hh

theorem cycle_order : orderOf cycle = 3 := orderOf_eq_prime cycle_cube cycle_ne_one

theorem diagonal_injective : Function.Injective diagonal := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro u hu
  have hz : diagonalSL u ∈ center SL := (QuotientGroup.eq_one_iff _).mp hu
  obtain ⟨r, _, he⟩ := SpecialLinearGroup.mem_center_iff.mp hz
  have h0 := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 0) he
  have h1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 1 1) he
  exact Units.ext (h1.symm.trans h0)

theorem diagonal_commute_cycle (u : Fˣ) : Commute (diagonal u) cycle := by
  change project (diagonalSL u) * project cycleSL = project cycleSL * project (diagonalSL u)
  rw [← map_mul, ← map_mul, project_eq_iff]
  refine ⟨(↑u⁻¹ : F), congrArg Units.val (unit_cube u⁻¹), ?_⟩
  have hc : (u : F) ^ 3 = 1 := congrArg Units.val (unit_cube u)
  have hi : (↑u⁻¹ : F) = (u : F) ^ 2 := congrArg Units.val (unit_inv u)
  change !![1,0,0;0,(u : F),0;0,0,↑u⁻¹] * !![0,1,0;0,0,1;1,0,0] =
    Matrix.scalar (Fin 3) (↑u⁻¹ : F) *
      (!![0,1,0;0,0,1;1,0,0] * !![1,0,0;0,(u : F),0;0,0,↑u⁻¹])
  have h2 : (↑u⁻¹ : F) * (↑u⁻¹ : F) = (u : F) := by
    calc
      _ = (u : F)^3 * u := by rw [hi]; ring
      _ = (u : F) := by rw [hc, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  simpa only [Units.val_inv_eq_inv_val] using h2.symm

private theorem diagonal_disjoint_cycle : Disjoint diagonal.range (zpowers cycle) := by
  classical
  apply disjoint_iff_inf_le.mpr
  rintro x ⟨⟨u, rfl⟩, hx⟩
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp
    ((isOfFinOrder_of_finite cycle).mem_zpowers_iff_mem_range_orderOf.mp hx)
  have hk3 : k < 3 := by simpa [cycle_order] using Finset.mem_range.mp hk
  have he' : project (diagonalSL u) = project (cycleSL ^ k) := by
    simpa only [map_pow, cycle] using (show project (diagonalSL u) = cycle ^ k from he.symm)
  obtain ⟨r, hr, he'⟩ := project_eq_iff _ _ |>.mp he'
  change diagonal u = 1
  interval_cases k
  · simpa only [pow_zero] using he.symm
  · change !![1,0,0;0,(u : F),0;0,0,↑u⁻¹] =
      Matrix.scalar (Fin 3) r * (!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F)^1 at he'
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 1) he'
    have hr0 : r = 0 := by simpa [ Matrix.mul_apply, Fin.sum_univ_three] using h.symm
    simp [hr0] at hr
  · change !![1,0,0;0,(u : F),0;0,0,↑u⁻¹] =
      Matrix.scalar (Fin 3) r * (!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F)^2 at he'
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 2) he'
    have hr0 : r = 0 := by simpa [ pow_two, Matrix.mul_apply, Fin.sum_univ_three] using h.symm
    simp [hr0] at hr

def embedding : Fˣ × zpowers cycle →* PSL :=
  diagonal.noncommCoprod (zpowers cycle).subtype (by
    intro u x
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp x.property
    change Commute (diagonal u) (x : PSL)
    rw [← hk]
    exact (diagonal_commute_cycle u).zpow_right k)

theorem embedding_injective : Function.Injective embedding := by
  apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
  exact ⟨diagonal_injective, (zpowers cycle).subtype_injective, by
    simpa only [Subgroup.range_subtype] using diagonal_disjoint_cycle⟩

def model : Subgroup PSL := embedding.range

theorem model_card : Nat.card model = 9 := by
  rw [model, Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv.symm,
    Nat.card_prod, Nat.card_units, card_F, Nat.card_zpowers, cycle_order]

def sylow : Sylow 3 PSL := Sylow.ofCard model (by
  rw [model_card, card_PSL]
  decide +kernel)

theorem sylow_coe : (sylow : Subgroup PSL) = model := Sylow.coe_ofCard _ _

theorem model_eq : model = diagonal.range ⊔ zpowers cycle := by
  rw [model, embedding, MonoidHom.noncommCoprod_range, Subgroup.range_subtype]

theorem diagonal_mem_model (u : Fˣ) : diagonal u ∈ model := by
  rw [model_eq]
  exact (le_sup_left : diagonal.range ≤ diagonal.range ⊔ zpowers cycle) (show diagonal u ∈ diagonal.range from ⟨u, rfl⟩)

theorem cycle_mem_model : cycle ∈ model := by
  rw [model_eq]
  exact (le_sup_right : zpowers cycle ≤ diagonal.range ⊔ zpowers cycle) (mem_zpowers cycle)

end Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
