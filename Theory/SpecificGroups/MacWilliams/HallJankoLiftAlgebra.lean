module

public import Theory.SpecificGroups.MacWilliams.HallJankoFrame
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-!
# Algebra of the lifts in a Hall–Janko action frame

Self-centrality of the marked C₄-square base puts the three unspecified lift
defects in that base. `LiftParameters` records the proposed 32 possible triples;
existence of these parameters is a separate assertion, not part of the structure.
For an odd parameter, explicit changes of lifts normalize all three equations:
multiply `t` by `a⁻ʳ`, `u` by `a^(j+2r+1)`, and `v` by `a^(2k)`.
The finite word calculations also prove that these changes preserve the frame
and generation, provided the marked four lies in the elementary subgroup.

Source: the extension calculation underlying Janko–Thompson, Math. Z. 113
(1970), Theorem 1.3(a), printed p.386, citing MacWilliams, Trans. AMS 150
(1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace MacWilliamsSylow.HallJankoActionFrame
variable {P : Type*} [Group P] {D W B : Subgroup P}
private theorem inv_of_four (a : P) (h : a ^ 4 = 1) : a⁻¹ = a * a * a := by
  calc
    a⁻¹ = a⁻¹ * a ^ 4 := by rw [h, mul_one]
    _ = a * a * a := by group; simp [pow_succ]
private theorem collect_a4 (f : HallJankoActionFrame D W B) (x : P) :
    f.a * (f.a * (f.a * (f.a * x))) = x := by
  simpa [pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.a_four
private theorem collect_b4 (f : HallJankoActionFrame D W B) (x : P) :
    f.b * (f.b * (f.b * (f.b * x))) = x := by
  simpa [pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.b_four
private theorem collect_ba (f : HallJankoActionFrame D W B) (x : P) :
    f.b * (f.a * x) = f.a * (f.b * x) := by rw [← mul_assoc, f.ba, mul_assoc]
private theorem collect_ua (f : HallJankoActionFrame D W B) (x : P) :
    f.u * (f.a * x) = f.a * (f.a * (f.a * (f.b * (f.b * (f.u * x))))) := by
  simpa [inv_of_four f.a f.a_four, pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.ua
private theorem collect_ub (f : HallJankoActionFrame D W B) (x : P) :
    f.u * (f.b * x) = f.b * (f.b * (f.b * (f.u * x))) := by
  simpa [inv_of_four f.b f.b_four, mul_assoc] using congrArg (fun z : P => z * x) f.ub
private theorem collect_va (f : HallJankoActionFrame D W B) (x : P) :
    f.v * (f.a * x) = f.a * (f.b * (f.b * (f.v * x))) := by
  simpa [pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.va
private theorem collect_vb (f : HallJankoActionFrame D W B) (x : P) :
    f.v * (f.b * x) = f.a * (f.a * (f.b * (f.v * x))) := by
  simpa [pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.vb
private theorem collect_ta (f : HallJankoActionFrame D W B) (x : P) :
    f.t * (f.a * x) = f.a * (f.b * (f.t * x)) := by
  simpa [mul_assoc] using congrArg (fun z : P => z * x) f.ta
private theorem collect_tb (f : HallJankoActionFrame D W B) (x : P) :
    f.t * (f.b * x) = f.b * (f.b * (f.b * (f.t * x))) := by
  simpa [inv_of_four f.b f.b_four, mul_assoc] using congrArg (fun z : P => z * x) f.tb

private theorem collect_a4_end (f : HallJankoActionFrame D W B) :
    f.a * (f.a * (f.a * f.a)) = 1 := by simpa [pow_succ, mul_assoc] using f.a_four
private theorem collect_b4_end (f : HallJankoActionFrame D W B) :
    f.b * (f.b * (f.b * f.b)) = 1 := by simpa [pow_succ, mul_assoc] using f.b_four

/-- Change the three lifts by base powers while preserving the full action frame. -/
def twist (f : HallJankoActionFrame D W B) (hWB : W ≤ B)
    (r : Fin 4) (s k : Fin 2) : HallJankoActionFrame D W B where
  a := f.a
  b := f.b
  u := f.a ^ (2 * s.val) * f.u
  v := f.a ^ (2 * k.val) * f.v
  t := f.a ^ r.val * f.t
  a_four := f.a_four
  b_four := f.b_four
  ba := f.ba
  base := f.base
  four := f.four
  u_mem := by
    apply B.mul_mem _ f.u_mem
    apply hWB
    have ha : f.a ^ 2 ∈ W := by simp only [f.four]; exact Subgroup.subset_closure (by simp)
    simpa only [pow_mul] using W.pow_mem ha s.val
  v_mem := by
    apply B.mul_mem _ f.v_mem
    apply hWB
    have ha : f.a ^ 2 ∈ W := by simp only [f.four]; exact Subgroup.subset_closure (by simp)
    simpa only [pow_mul] using W.pow_mem ha k.val
  u_two := by
    fin_cases s <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one] <;>
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_a4_end, collect_b4_end, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
      collect_ta, collect_tb, f.u_two, f.v_two, f.vu, f.ba, f.ua, f.ub, f.va, f.vb,
      f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  v_two := by
    fin_cases k <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one] <;>
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_a4_end, collect_b4_end, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
      collect_ta, collect_tb, f.u_two, f.v_two, f.vu, f.ba, f.ua, f.ub, f.va, f.vb,
      f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  vu := by
    fin_cases s <;> fin_cases k <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one] <;>
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_a4_end, collect_b4_end, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
      collect_ta, collect_tb, f.u_two, f.v_two, f.vu, f.ba, f.ua, f.ub, f.va, f.vb,
      f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  ua := by
    fin_cases s <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one] <;>
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_a4_end, collect_b4_end, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
      collect_ta, collect_tb, f.u_two, f.v_two, f.vu, f.ba, f.ua, f.ub, f.va, f.vb,
      f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  ub := by
    fin_cases s <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one] <;>
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_a4_end, collect_b4_end, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
      collect_ta, collect_tb, f.u_two, f.v_two, f.vu, f.ba, f.ua, f.ub, f.va, f.vb,
      f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  va := by
    fin_cases k <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one] <;>
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_a4_end, collect_b4_end, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
      collect_ta, collect_tb, f.u_two, f.v_two, f.vu, f.ba, f.ua, f.ub, f.va, f.vb,
      f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  vb := by
    fin_cases k <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one] <;>
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_a4_end, collect_b4_end, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
      collect_ta, collect_tb, f.u_two, f.v_two, f.vu, f.ba, f.ua, f.ub, f.va, f.vb,
      f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  ta := by
    fin_cases r <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one] <;>
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_a4_end, collect_b4_end, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
      collect_ta, collect_tb, f.u_two, f.v_two, f.vu, f.ba, f.ua, f.ub, f.va, f.vb,
      f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  tb := by
    fin_cases r <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one] <;>
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_a4_end, collect_b4_end, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
      collect_ta, collect_tb, f.u_two, f.v_two, f.vu, f.ba, f.ua, f.ub, f.va, f.vb,
      f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  generate := by
    let H := Subgroup.closure ({f.a, f.b, f.a ^ (2 * s.val) * f.u,
      f.a ^ (2 * k.val) * f.v, f.a ^ r.val * f.t} : Set P)
    have ha : f.a ∈ H := Subgroup.subset_closure (by simp)
    have hb : f.b ∈ H := Subgroup.subset_closure (by simp)
    have hu : f.u ∈ H := by
      have hh := H.mul_mem (H.inv_mem (H.pow_mem ha (2 * s.val)))
        (Subgroup.subset_closure (by simp) : f.a ^ (2 * s.val) * f.u ∈ H)
      simpa only [inv_mul_cancel_left] using hh
    have hv : f.v ∈ H := by
      have hh := H.mul_mem (H.inv_mem (H.pow_mem ha (2 * k.val)))
        (Subgroup.subset_closure (by simp) : f.a ^ (2 * k.val) * f.v ∈ H)
      simpa only [inv_mul_cancel_left] using hh
    have ht : f.t ∈ H := by
      have hh := H.mul_mem (H.inv_mem (H.pow_mem ha r.val))
        (Subgroup.subset_closure (by simp) : f.a ^ r.val * f.t ∈ H)
      simpa only [inv_mul_cancel_left] using hh
    apply top_unique
    rw [← f.generate]
    exact (Subgroup.closure_le _).mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption)

/-- The 32 candidate extension parameter triples; existence must be proved separately. -/
structure LiftParameters (f : HallJankoActionFrame D W B) where
  r : Fin 4
  j : Fin 4
  k : Fin 2
  t_sq : f.t * f.t = f.a ^ (2 * r.val) * f.b ^ r.val
  t_u : f.t * f.u = f.a ^ (2 * r.val) * f.b ^ j.val * f.u * f.t
  t_v : f.t * f.v = f.a ^ j.val * f.b ^ (2 * k.val) * f.u * f.v * f.t

set_option maxHeartbeats 2000000 in
/-- Odd extension parameters admit lifts satisfying all three remaining relations. -/
theorem normalize_of_parameters (f : HallJankoActionFrame D W B) (hWB : W ≤ B)
    (p : f.LiftParameters) (hodd : p.j.val % 2 = 1) :
    ∃ f' : HallJankoActionFrame D W B, f'.LiftRelations := by
  rcases p with ⟨r, j, k, htt, htu, htv⟩
  change j.val % 2 = 1 at hodd
  let r' : Fin 4 := ⟨(4 - r.val) % 4, Nat.mod_lt _ (by decide)⟩
  let s' : Fin 2 := ⟨((j.val + 2 * r.val + 1) / 2) % 2, Nat.mod_lt _ (by decide)⟩
  refine ⟨f.twist hWB r' s' k, ?_⟩
  have htu' (x : P) := congrArg (fun z : P => z * x) htu
  have htv' (x : P) := congrArg (fun z : P => z * x) htv
  simp only [mul_assoc] at htu' htv'
  fin_cases r <;> fin_cases j <;> fin_cases k <;> norm_num at hodd
  all_goals constructor
  all_goals
    dsimp [twist, r', s']
    norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one] at htt htu htv htu' htv'
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_a4_end, collect_b4_end,
      collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
      collect_ta, collect_tb, f.u_two, f.v_two, f.vu, f.ba, f.ua, f.ub, f.va, f.vb,
      f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four,
      htt, htu, htv, htu', htv']

/-- If the `tu` defect is outside the marked four, its parameter is odd. -/
theorem j_odd_of_defect_not_mem (f : HallJankoActionFrame D W B)
    (p : f.LiftParameters) (hn : f.t * f.u * (f.u * f.t)⁻¹ ∉ W) :
    p.j.val % 2 = 1 := by
  have ha : f.a ^ 2 ∈ W := by simp only [f.four]; exact Subgroup.subset_closure (by simp)
  have hb : f.b ^ 2 ∈ W := by simp only [f.four]; exact Subgroup.subset_closure (by simp)
  rcases p with ⟨r, j, k, htt, htu, htv⟩
  change j.val % 2 = 1
  have he : f.t * f.u * (f.u * f.t)⁻¹ = f.a ^ (2 * r.val) * f.b ^ j.val := by
    rw [htu]
    group
  have ha' : f.a ^ (2 * r.val) ∈ W := by simpa only [pow_mul] using W.pow_mem ha r.val
  fin_cases j <;> norm_num
  · apply hn
    rw [he]
    simpa using ha'
  · apply hn
    rw [he]
    exact W.mul_mem ha' hb

private theorem left_defect_commutes (x y z A : P)
    (hx : x * z = A * x) (hy : y * z = A * y) :
    z * (y⁻¹ * x) = (y⁻¹ * x) * z := by
  apply (mul_left_cancel_iff (a := y)).mp
  calc
    y * (z * (y⁻¹ * x)) = (y * z) * (y⁻¹ * x) := by group
    _ = (A * y) * (y⁻¹ * x) := by rw [hy]
    _ = A * x := by group
    _ = x * z := hx.symm
    _ = y * ((y⁻¹ * x) * z) := by group

/-- Equal actions on the two base generators put the quotient of two lifts in the base. -/
theorem defect_mem_base (f : HallJankoActionFrame D W B) [D.Normal]
    (hDC : Subgroup.centralizer (D : Set P) ≤ D)
    (x y A B' : P) (hxa : x * f.a = A * x) (hya : y * f.a = A * y)
    (hxb : x * f.b = B' * x) (hyb : y * f.b = B' * y) : x * y⁻¹ ∈ D := by
  have hleft : y⁻¹ * x ∈ D := by
    apply hDC
    simp only [f.base, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact left_defect_commutes _ _ _ _ hxa hya
    · exact left_defect_commutes _ _ _ _ hxb hyb
  have hh := (inferInstance : D.Normal).conj_mem (y⁻¹ * x) hleft y
  simpa only [mul_inv_cancel_left] using hh

/-- The three unspecified lift products differ from their quotient words by base elements. -/
theorem lift_defects_mem_base (f : HallJankoActionFrame D W B) [D.Normal]
    (hDC : Subgroup.centralizer (D : Set P) ≤ D) :
    f.t * f.t ∈ D ∧ f.t * f.u * (f.u * f.t)⁻¹ ∈ D ∧
      f.t * f.v * (f.u * f.v * f.t)⁻¹ ∈ D := by
  have ht : f.t * f.t ∈ D := by
    apply hDC
    simp only [f.base, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    all_goals
      simp only [mul_assoc, collect_ta, collect_tb, collect_ba, collect_b4,
        f.ta, f.tb, inv_of_four f.b f.b_four]
  refine ⟨ht, ?_, ?_⟩
  · apply f.defect_mem_base hDC (f.t * f.u) (f.u * f.t) (f.a⁻¹ * f.b) f.b
    all_goals
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
        collect_a4, collect_b4, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
        collect_ta, collect_tb, f.ba, f.ua, f.ub, f.va, f.vb, f.ta, f.tb,
        inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · apply f.defect_mem_base hDC (f.t * f.v) (f.u * f.v * f.t)
      (f.a * f.b⁻¹) (f.a ^ 2 * f.b)
    all_goals
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
        collect_a4, collect_b4, collect_ba, collect_ua, collect_ub, collect_va, collect_vb,
        collect_ta, collect_tb, f.ba, f.ua, f.ub, f.va, f.vb, f.ta, f.tb,
        inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
end MacWilliamsSylow.HallJankoActionFrame
