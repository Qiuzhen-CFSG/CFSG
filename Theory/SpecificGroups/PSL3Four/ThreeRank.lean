module

public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.GroupTheory.PrimeRankFixedJoin
/-!
# An elementary nine in the actual PSL₃(4)

Choose a generator u of the multiplicative group of the field of four
elements. The diagonal matrix diag(1,u,u²) and a coordinate three-cycle
have order three. They commute modulo the scalar center, and the cycle is
outside the diagonal cyclic subgroup. Their projective images therefore
generate an elementary group of order nine.

This supplies the strict three-rank hypothesis in Aschbacher–Smith A.3.18
for the PSL₃(4) branch of 13.6.27, printed pp.934–935.
-/

public section

open Subgroup Matrix
noncomputable section
namespace Matrix.PSL3Four.ThreeRank
private def diagonal (u : Fˣ) (hu : u ^ 3 = 1) : SL :=
  ⟨!![1,0,0;0,(u : F),0;0,0,(u : F)^2], by
    simpa [Matrix.det_fin_three, pow_succ, mul_assoc] using congrArg Units.val hu⟩
private def cycle : SL := ⟨!![0,1,0;0,0,1;1,0,0], by simp [Matrix.det_fin_three]⟩
private def scalar (u : Fˣ) (hu : u ^ 3 = 1) : SL :=
  ⟨Matrix.scalar (Fin 3) (u : F), by
    simpa using congrArg Units.val hu⟩
private theorem scalar_central (u : Fˣ) (hu : u ^ 3 = 1) : scalar u hu ∈ center SL := by
  exact SpecialLinearGroup.mem_center_iff.mpr ⟨u, by simpa using congrArg Units.val hu, rfl⟩
private theorem diagonal_cube (u : Fˣ) (hu : u ^ 3 = 1) : diagonal u hu ^ 3 = 1 := by
  have h : (u : F)^3 = 1 := congrArg Units.val hu
  apply Subtype.ext
  change (!![1,0,0;0,(u : F),0;0,0,(u : F)^2] : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf
  · exact h
  · calc
      (u : F) ^ 6 = ((u : F) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [h, one_pow]
private theorem cycle_cube : cycle ^ 3 = 1 := by
  apply Subtype.ext
  change (!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
private theorem cycle_diagonal (u : Fˣ) (hu : u ^ 3 = 1) :
    cycle * diagonal u hu = scalar u hu * (diagonal u hu * cycle) := by
  have h : (u : F)^3 = 1 := congrArg Units.val hu
  apply Subtype.ext
  change cycle.val * (diagonal u hu).val = (scalar u hu).val * ((diagonal u hu).val * cycle.val)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycle, diagonal, scalar, Matrix.scalar, Matrix.diagonal, Matrix.mul_apply,
      Fin.sum_univ_three] <;> ring_nf
  exact h.symm

private theorem diagonal_image_ne_one (u : Fˣ) (hu : u ^ 3 = 1) (hne : u ≠ 1) :
    QuotientGroup.mk' (center SL) (diagonal u hu) ≠ 1 := by
  intro he
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff _).mp he)
  have h0 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) hr
  have h1 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 1 1) hr
  have heq : (u : F) = 1 := by simpa [diagonal, Matrix.scalar] using h1.symm.trans h0
  exact hne (Units.ext heq)

private theorem cycle_image_not_power (u : Fˣ) (hu : u ^ 3 = 1) (n : ℕ) :
    QuotientGroup.mk' (center SL) cycle ≠
      (QuotientGroup.mk' (center SL) (diagonal u hu)) ^ n := by
  intro he
  rw [← map_pow] at he
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp
    (QuotientGroup.eq_iff_div_mem.mp he.symm)
  have hm : Matrix.scalar (Fin 3) r * cycle.val = (diagonal u hu ^ n).val := by
    rw [hr]
    change ((diagonal u hu ^ n / cycle) * cycle).val = _
    rw [div_mul_cancel]
  change Matrix.scalar (Fin 3) r * cycle.val = (diagonal u hu).val ^ n at hm
  have hd : (diagonal u hu).val = Matrix.diagonal ![1,(u : F),(u : F)^2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.diagonal]
  rw [hd, Matrix.diagonal_pow] at hm
  have h0 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) hm
  simp [cycle, Matrix.scalar, Matrix.diagonal, Matrix.mul_apply] at h0

/-- An explicit diagonal and monomial pair gives projective three-rank at least two. -/
theorem three_rank_ge_two : 2 ≤ primeRank 3 PSL := by
  classical
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have ho : orderOf u = 3 := by simpa [Nat.card_units, card_F] using hu
  have hc : u ^ 3 = 1 := ho ▸ pow_orderOf_eq_one u
  have hn : u ≠ 1 := by intro he; simp [he] at ho
  let q := QuotientGroup.mk' (center SL)
  let d := q (diagonal u hc)
  let c := q cycle
  have hd3 : d ^ 3 = 1 := by rw [← map_pow, diagonal_cube, map_one]
  have hc3 : c ^ 3 = 1 := by rw [← map_pow, cycle_cube, map_one]
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 (diagonal_image_ne_one u hc hn)
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 (by
    simpa only [pow_zero] using cycle_image_not_power u hc 0)
  have hcomm : c * d = d * c := by
    change q cycle * q (diagonal u hc) = q (diagonal u hc) * q cycle
    have hs : q (scalar u hc) = 1 := (QuotientGroup.eq_one_iff _).mpr (scalar_central u hc)
    rw [← map_mul, cycle_diagonal, map_mul, hs, one_mul, map_mul]
  have hnot : c ∉ zpowers d := by
    rw [mem_zpowers_iff_mem_range_orderOf, hdo]
    intro h
    obtain ⟨n, _, he⟩ := Finset.mem_image.mp h
    exact cycle_image_not_power u hc n he.symm
  let _ : IsElementaryAbelian 3 (zpowers d) := IsElementaryAbelian.zpowers_of_pow_eq_one hd3
  have hfix : zpowers d ≤ centralizer ({c} : Set PSL) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcomm.symm)
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join (zpowers d) c hco hnot hfix
    (by simp [Nat.card_zpowers, hdo])
end Matrix.PSL3Four.ThreeRank
