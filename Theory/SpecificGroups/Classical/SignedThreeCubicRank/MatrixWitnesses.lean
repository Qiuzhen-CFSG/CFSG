module

public import Theory.GroupTheory.PrimeRankFixedJoin
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring

/-!
# Two cubic matrix witnesses in degree three

The scalar uI and diag(1,u,u²) are independent commuting cubics whenever
u is a nontrivial cube root of one. The diagonal and a coordinate three-cycle
commute modulo scalars and are independent in PGL. Faithful matrix maps
transport these explicit witnesses into any group containing them.

Source application: Aschbacher–Smith, proof of 13.8.20(a), printed p.954.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SignedThreeCubicRank

private theorem rank_of_cubics {G : Type*} [Group G] [Finite G]
    (x y : G) (hx : x ^ 3 = 1) (hx1 : x ≠ 1) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) (hyx : y ≠ x) (hyx2 : y ≠ x ^ 2) (hcomm : Commute x y) :
    2 ≤ primeRank 3 G := by
  classical
  have hxo : orderOf x = 3 := orderOf_eq_prime hx hx1
  let : IsElementaryAbelian 3 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  apply IsElementaryAbelian.primeRank_ge_of_fixed_join (n := 1) (zpowers x) y
    (orderOf_eq_prime hy hy1)
  · intro hm
    rw [mem_zpowers_iff_mem_range_orderOf, hxo] at hm
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hm
    have hk' : k < 3 := Finset.mem_range.mp hk
    interval_cases k <;> simp_all
  · rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr hcomm.eq
  · simp [Nat.card_zpowers, hxo]

variable {F : Type*} [Field F] (u : F) (hu : u ^ 3 = 1)

@[expose] def diagonal : SL(3,F) :=
  ⟨!![1,0,0;0,u,0;0,0,u^2], by simpa [Matrix.det_fin_three, pow_succ, mul_comm] using hu⟩
@[expose] def scalar : SL(3,F) :=
  ⟨Matrix.scalar (Fin 3) u, by simpa using hu⟩
@[expose] def cycle : SL(3,F) :=
  ⟨!![0,0,1;1,0,0;0,1,0], by simp [Matrix.det_fin_three]⟩

private theorem diagonal_cube : diagonal u hu ^ 3 = 1 := by
  apply Subtype.ext
  change (diagonal u hu).val ^ 3 = 1
  have h6 : u ^ 6 = 1 := by
    calc u ^ 6 = (u ^ 3) ^ 2 := by ring
         _ = 1 := by rw [hu]; simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp_all

private theorem scalar_cube : scalar u hu ^ 3 = 1 := by
  apply Subtype.ext
  change (Matrix.scalar (Fin 3) u) ^ 3 = 1
  rw [← map_pow, hu, map_one]

private theorem cycle_cube : (cycle (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  change (cycle (F := F)).val ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycle, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

private theorem scalar_central : scalar u hu ∈ center SL(3,F) := by
  exact SpecialLinearGroup.mem_center_iff.mpr ⟨u, by simpa using hu, rfl⟩

private theorem diagonal_cycle : diagonal u hu * cycle = scalar u hu * cycle * diagonal u hu := by
  apply Subtype.ext
  change (diagonal u hu).val * cycle.val = ((scalar u hu).val * cycle.val) * (diagonal u hu).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, scalar, cycle, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar,
      Matrix.diagonal]
  all_goals ring_nf
  all_goals simp_all


private theorem diagonal_ne_one (hne : u ≠ 1) : diagonal u hu ≠ 1 := by
  intro h
  have he := congrArg (fun A : SL(3,F) => A.val 1 1) h
  exact hne (by simpa [diagonal] using he)

private theorem scalar_ne_diagonal_pow (hne : u ≠ 1) {k : ℕ} (hk : k < 3) :
    scalar u hu ≠ diagonal u hu ^ k := by
  intro h
  have he := congrArg (fun A : SL(3,F) => A.val 0 0) h
  change u = ((diagonal u hu).val ^ k) 0 0 at he
  apply hne
  interval_cases k <;>
    simpa [scalar, diagonal, SpecialLinearGroup.coe_pow, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] using he

private theorem projective_diagonal_ne_one (hne : u ≠ 1) :
    SpecialLinearGroup.toPGL (diagonal u hu) ≠ 1 := by
  intro he
  have hc := (SpecialLinearGroup.toGL_mem_center_iff _).mp
    (ProjGenLinGroup.mk_eq_one.mp he)
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hr
  have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 1) hr
  simp [diagonal] at h0 h1
  exact hne (h1.symm.trans h0)

private theorem projective_cycle_ne_diagonal_pow {k : ℕ} (hk : k < 3) :
    SpecialLinearGroup.toPGL (cycle (F := F)) ≠
      SpecialLinearGroup.toPGL (diagonal u hu) ^ k := by
  intro he
  rw [← map_pow] at he
  obtain ⟨r, hr⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he.symm
  have hh := congrArg (fun A : GL (Fin 3) F => A.val 1 0) hr
  change (((diagonal u hu).val ^ k) * Matrix.scalar (Fin 3) (r : F)) 1 0 = 1 at hh
  interval_cases k <;>
    simp [diagonal, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar] at hh

private theorem projective_commute :
    Commute (SpecialLinearGroup.toPGL (diagonal u hu))
      (SpecialLinearGroup.toPGL (cycle (F := F))) := by
  have hz : SpecialLinearGroup.toPGL (scalar u hu) = 1 :=
    ProjGenLinGroup.mk_eq_one.mpr
      ((SpecialLinearGroup.toGL_mem_center_iff _).mpr (scalar_central u hu))
  have he := congrArg (SpecialLinearGroup.toPGL (n := Fin 3)) (diagonal_cycle u hu)
  change _ * _ = _ * _
  simpa only [map_mul, hz, one_mul] using he

/-- Two marked determinant-one diagonal cubics witness rank two in any
faithful matrix group containing them. -/
theorem special_rank {G : Type*} [Group G] [Finite G]
    (hne : u ≠ 1) (f : G →* GL (Fin 3) F) (hf : Function.Injective f)
    (x y : G) (hx : f x = SpecialLinearGroup.toGL (diagonal u hu))
    (hy : f y = SpecialLinearGroup.toGL (scalar u hu)) : 2 ≤ primeRank 3 G := by
  have hx3 : x ^ 3 = 1 := by
    apply hf
    rw [map_pow, hx, ← map_pow, diagonal_cube, map_one, map_one]
  have hy3 : y ^ 3 = 1 := by
    apply hf
    rw [map_pow, hy, ← map_pow, scalar_cube, map_one, map_one]
  have hx1 : x ≠ 1 := by
    intro he
    apply diagonal_ne_one u hu hne
    apply SpecialLinearGroup.toGL_injective
    rw [map_one, ← hx, he, map_one]
  have hnot (k : ℕ) (hk : k < 3) : y ≠ x ^ k := by
    intro he
    apply scalar_ne_diagonal_pow u hu hne hk
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, ← hx, ← hy, he, map_pow]
  have hcomm : Commute x y := by
    apply hf
    rw [map_mul, map_mul, hx, hy, ← map_mul, ← map_mul]
    exact congrArg SpecialLinearGroup.toGL ((mem_center_iff.mp (scalar_central u hu)) _)
  exact rank_of_cubics x y hx3 hx1 hy3 (by simpa using hnot 0 (by omega))
    (by simpa using hnot 1 (by omega)) (hnot 2 (by omega)) hcomm

/-- The diagonal cubic and a three-cycle witness rank two after quotienting
by scalar matrices. -/
theorem projective_rank {G : Type*} [Group G] [Finite G]
    (hne : u ≠ 1) (f : G →* PGL(3,F)) (hf : Function.Injective f)
    (x y : G) (hx : f x = SpecialLinearGroup.toPGL (diagonal u hu))
    (hy : f y = SpecialLinearGroup.toPGL (cycle (F := F))) : 2 ≤ primeRank 3 G := by
  have hx3 : x ^ 3 = 1 := by
    apply hf
    rw [map_pow, hx, ← map_pow, diagonal_cube, map_one, map_one]
  have hy3 : y ^ 3 = 1 := by
    apply hf
    rw [map_pow, hy, ← map_pow, cycle_cube, map_one, map_one]
  have hx1 : x ≠ 1 := by
    intro he
    exact projective_diagonal_ne_one u hu hne (by rw [← hx, he, map_one])
  have hnot (k : ℕ) (hk : k < 3) : y ≠ x ^ k := by
    intro he
    exact projective_cycle_ne_diagonal_pow u hu hk (by rw [← hy, ← hx, he, map_pow])
  have hcomm : Commute x y := by
    apply hf
    rw [map_mul, map_mul, hx, hy]
    exact (projective_commute u hu).eq
  exact rank_of_cubics x y hx3 hx1 hy3 (by simpa using hnot 0 (by omega))
    (by simpa using hnot 1 (by omega)) (hnot 2 (by omega)) hcomm

end Theory.SpecificGroups.SignedThreeCubicRank

end
