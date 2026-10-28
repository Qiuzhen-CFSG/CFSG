module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Metric
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Data.Real.Basic

/-!
# Distance matrices for even polygon parameters

The two-step graph census is packaged as matrices on one color class.
These matrices satisfy the hexagon and octagon recurrences used by the
Feit--Higman square argument.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters.Datum
open scoped BigOperators
open OctagonShortPaths
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {m s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance : DecidableEq V := Classical.decEq _
variable (D : Datum G m s t)

abbrev Point := {v : V // D.color v=0}

def distanceMatrix (k : ℕ) : Matrix D.Point D.Point ℝ :=
  fun u v => if G.dist u.val v.val=2*k then 1 else 0

theorem distanceMatrix_zero : D.distanceMatrix 0=1 := by
  ext u v
  simp only [distanceMatrix, mul_zero, Matrix.one_apply]
  simp only [D.connected.dist_eq_zero_iff, Subtype.coe_inj]

theorem trace_distanceMatrix (k : ℕ) (hk : 0<k) :
    (D.distanceMatrix k).trace=0 := by
  simp [Matrix.trace, Matrix.diag, distanceMatrix, Nat.ne_of_gt hk]

private theorem distance_two_color {u v : V} (hu : D.color u=0)
    (h : G.dist u v=2) : D.color v=0 := by
  have hh := distance_color D.connected D.color D.color_adj u v
  norm_num [hu,h] at hh
  exact hh.symm

theorem matrix_mul_apply (hm : 2<m) (he : Even m) (k : ℕ) (u r : D.Point) :
    (D.distanceMatrix 1*D.distanceMatrix k) u r =
      if G.dist u.val r.val=0 then ((t : ℝ)+1)*s*(if 2=2*k then 1 else 0) else
      if G.dist u.val r.val=m then
        ((t : ℝ)+1)*(if m-2=2*k then 1 else 0)+
        ((t : ℝ)+1)*(s-1)*(if m=2*k then 1 else 0) else
        (if G.dist u.val r.val-2=2*k then 1 else 0)+
        ((s : ℝ)-1)*(if G.dist u.val r.val=2*k then 1 else 0)+
        ((s : ℝ)*t)*(if G.dist u.val r.val+2=2*k then 1 else 0) := by
  let f : ℕ → ℤ := fun n => if n=2*k then 1 else 0
  have hs := D.double_point_sum hm he u.val r.val u.property r.property f
  have hsum : (∑ v : D.Point,
      if G.dist u.val v.val=2 then f (G.dist v.val r.val) else 0) =
      ∑ v : V, if G.dist u.val v=2 then f (G.dist v r.val) else 0 := by
    have hh := Fintype.sum_subtype_add_sum_subtype (fun v => D.color v=0)
      (fun v => if G.dist u.val v=2 then f (G.dist v r.val) else 0)
    have hz : (∑ v : {v : V // ¬D.color v=0},
        if G.dist u.val v.val=2 then f (G.dist v.val r.val) else 0)=0 := by
      apply Finset.sum_eq_zero
      intro v hv
      have hd : G.dist u.val v.val≠2 := fun hd => v.property (D.distance_two_color u.property hd)
      simp [hd]
    simpa only [hz,add_zero] using hh
  rw [←hsum] at hs
  have hh : (D.distanceMatrix 1*D.distanceMatrix k) u r =
      ((∑ v : D.Point, if G.dist u.val v.val=2 then f (G.dist v.val r.val) else 0 : ℤ) : ℝ) := by
    simp only [Matrix.mul_apply, distanceMatrix, mul_one, Int.cast_sum, f]
    apply Finset.sum_congr rfl
    intro v hv
    split_ifs <;> simp_all
  rw [hh,hs]
  simp only [f, Int.cast_ite, Int.cast_zero, Int.cast_one, Int.cast_add,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast]


theorem hexagon_recurrence_1 (D : Datum G 6 s t) :
    D.distanceMatrix 1*D.distanceMatrix 1 =
      ((s : ℝ)*(t+1)) • D.distanceMatrix 0 + ((s : ℝ)-1) • D.distanceMatrix 1 + D.distanceMatrix 2 := by
  ext u v
  rw [D.matrix_mul_apply (by decide) (by decide)]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  have hdb : d≤3 := by omega
  interval_cases d <;>
    norm_num [hd,distanceMatrix, Matrix.add_apply, Matrix.smul_apply]
  ring

theorem hexagon_recurrence_2 (D : Datum G 6 s t) :
    D.distanceMatrix 1*D.distanceMatrix 2 =
      ((s : ℝ)*t) • D.distanceMatrix 1 + ((s : ℝ)-1) • D.distanceMatrix 2 + ((t : ℝ)+1) • D.distanceMatrix 3 := by
  ext u v
  rw [D.matrix_mul_apply (by decide) (by decide)]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  have hdb : d≤3 := by omega
  interval_cases d <;>
    norm_num [hd,distanceMatrix, Matrix.add_apply, Matrix.smul_apply]

theorem hexagon_recurrence_3 (D : Datum G 6 s t) :
    D.distanceMatrix 1*D.distanceMatrix 3 =
      ((s : ℝ)*t) • D.distanceMatrix 2 + (((s : ℝ)-1)*(t+1)) • D.distanceMatrix 3 := by
  ext u v
  rw [D.matrix_mul_apply (by decide) (by decide)]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  have hdb : d≤3 := by omega
  interval_cases d <;>
    norm_num [hd,distanceMatrix, Matrix.add_apply, Matrix.smul_apply]
  ring

theorem octagon_recurrence_1 (D : Datum G 8 s t) :
    D.distanceMatrix 1*D.distanceMatrix 1 =
      ((s : ℝ)*(t+1)) • D.distanceMatrix 0 + ((s : ℝ)-1) • D.distanceMatrix 1 + D.distanceMatrix 2 := by
  ext u v
  rw [D.matrix_mul_apply (by decide) (by decide)]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  have hdb : d≤4 := by omega
  interval_cases d <;>
    norm_num [hd,distanceMatrix, Matrix.add_apply, Matrix.smul_apply]
  ring

theorem octagon_recurrence_2 (D : Datum G 8 s t) :
    D.distanceMatrix 1*D.distanceMatrix 2 =
      ((s : ℝ)*t) • D.distanceMatrix 1 + ((s : ℝ)-1) • D.distanceMatrix 2 + D.distanceMatrix 3 := by
  ext u v
  rw [D.matrix_mul_apply (by decide) (by decide)]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  have hdb : d≤4 := by omega
  interval_cases d <;>
    norm_num [hd,distanceMatrix, Matrix.add_apply, Matrix.smul_apply]

theorem octagon_recurrence_3 (D : Datum G 8 s t) :
    D.distanceMatrix 1*D.distanceMatrix 3 =
      ((s : ℝ)*t) • D.distanceMatrix 2 + ((s : ℝ)-1) • D.distanceMatrix 3 + ((t : ℝ)+1) • D.distanceMatrix 4 := by
  ext u v
  rw [D.matrix_mul_apply (by decide) (by decide)]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  have hdb : d≤4 := by omega
  interval_cases d <;>
    norm_num [hd,distanceMatrix, Matrix.add_apply, Matrix.smul_apply]

theorem octagon_recurrence_4 (D : Datum G 8 s t) :
    D.distanceMatrix 1*D.distanceMatrix 4 =
      ((s : ℝ)*t) • D.distanceMatrix 3 + (((s : ℝ)-1)*(t+1)) • D.distanceMatrix 4 := by
  ext u v
  rw [D.matrix_mul_apply (by decide) (by decide)]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  have hdb : d≤4 := by omega
  interval_cases d <;>
    norm_num [hd,distanceMatrix, Matrix.add_apply, Matrix.smul_apply]
  ring
end SimpleGraph.PolygonParameters.Datum
