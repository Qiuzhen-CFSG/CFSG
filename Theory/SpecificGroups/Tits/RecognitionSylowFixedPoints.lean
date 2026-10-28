module

public import Theory.SpecificGroups.Tits.RecognitionSylowSeed
public import Theory.GroupTheory.CyclicExtension
import Mathlib.Tactic.FinCases

/-!
# Fixed points of the outer seed action

The action v ↦ vt, u ↦ uv, w ↦ wu fixes exactly the subgroup generated
by z,t in the elementary derived subgroup. Collecting the three binary
coordinates reduces the assertion to seven exclusions; successive application
of the action would otherwise force t = 1.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, p.680, the commutator bound preceding equation (18).
-/

open Subgroup
namespace Tits.ParrottSylowSeedRelations
set_option linter.unusedSimpArgs false
variable {G : Type*} [Group G] [Finite G] {z t v u w a b c d x : G}
private theorem split_insert (S : Set G) (g : G) (hg : g^2=1)
    (hc : ∀ s ∈ S, Commute g s) {k : G} (hk : k ∈ closure (insert g S)) :
    ∃ r ∈ closure S, k = r ∨ k = r*g := by
  obtain ⟨r, hr, i, hi⟩ := Theory.GroupTheory.exists_mul_pow_of_mem_closure_insert
    S g 2 (by decide) hg (fun s hs => by
      rw [(hc s hs).eq, mul_inv_cancel_right]
      exact subset_closure hs) hk
  refine ⟨r, hr, ?_⟩
  fin_cases i <;> simp_all

private theorem coordinates (h : ParrottSylowSeedRelations false z t v u w a b c d x) {q : G}
    (hq : q ∈ closure ({z,t,v,u,w} : Set G)) :
    ∃ r ∈ closure ({z,t} : Set G),
      q = r ∨ q = r*v ∨ q = r*u ∨ q = r*v*u ∨
      q = r*w ∨ q = r*v*w ∨ q = r*u*w ∨ q = r*v*u*w := by
  have he : ({z,t,v,u,w} : Set G) = {w,u,v,z,t} := by ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [he] at hq
  obtain ⟨r, hr, hq⟩ := split_insert ({u,v,z,t} : Set G) w h.w_sq (by
    intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    exact h.comm_uw.symm
    exact h.comm_vw.symm
    exact h.comm_zw.symm
    exact h.comm_tw.symm) hq
  obtain ⟨s, hs, hr⟩ := split_insert ({v,z,t} : Set G) u h.u_sq (by
    intro k hk; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl
    exact h.comm_vu.symm
    exact h.comm_zu.symm
    exact h.comm_tu.symm) hr
  obtain ⟨p, hp, hs⟩ := split_insert ({z,t} : Set G) v h.v_sq (by
    intro k hk; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    exact h.comm_zv.symm
    exact h.comm_tv.symm) hs
  refine ⟨p, hp, ?_⟩
  rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> tauto


omit [Finite G] in
private theorem conj_of_commute {g k : G} (h : Commute g k) : g⁻¹*k*g=k := by
  rw [mul_assoc, h.symm.eq, inv_mul_cancel_left]
omit [Finite G] in
private theorem pc_conj_rev {p q r : G} (h : parrottCommutator p q = r)
    (hr : r^2=1) : p⁻¹*q*p=q*r := by
  have hi : r⁻¹=r := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hr)
  rw [← hi, ← h, parrottCommutator]
  group

/-- The fixed points of the prescribed unipotent outer action on the derived
elementary subgroup lie in the two central coordinates. -/
public theorem fixed_mem_pair (h : ParrottSylowSeedRelations false z t v u w a b c d x)
    (ht : t ≠ 1) {q : G}
    (hq : q ∈ closure ({z,t,v,u,w} : Set G)) (hfix : x⁻¹*q*x=q) :
    q ∈ closure ({z,t} : Set G) := by
  let P : G ≃* G := MulAut.conj x⁻¹
  have Peq (s : G) : P s = x⁻¹*s*x := by simp [P]
  have Pz : P z = z := by rw [Peq]; exact conj_of_commute h.comm_zx.symm
  have Pt : P t = t := by rw [Peq]; exact conj_of_commute ((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt)
  have Pv : P v = v*t := by rw [Peq]; exact pc_conj_rev h.eq01_xv h.t_sq
  have Pu : P u = u*v := by rw [Peq]; exact pc_conj_rev h.eq01_xu h.v_sq
  have Pw : P w = w*u := by rw [Peq]; exact pc_conj_rev h.eq01_xw h.u_sq
  have Pr (r : G) (hr : r ∈ closure ({z,t} : Set G)) : P r = r := by
    have hl : closure ({z,t} : Set G) ≤ centralizer ({x} : Set G) := by
      apply (closure_le _).mpr
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      exact mem_centralizer_singleton_iff.mpr h.comm_zx
      exact mem_centralizer_singleton_iff.mpr ((parrottCommutator_eq_one_iff _ _).mp h.eq01_xt).symm
    rw [Peq]
    exact conj_of_commute (mem_centralizer_singleton_iff.mp (hl hr)).symm
  have hqf : P q = q := by rw [Peq]; exact hfix
  obtain ⟨r, hr, hq⟩ := coordinates h hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hr
  all_goals
    simp only [map_mul, Pr r hr, Pv, Pu, Pw, mul_assoc, mul_left_cancel_iff] at hqf
  · exact (ht ((mul_eq_left.mp hqf))).elim
  · have hv : v = 1 := mul_eq_left.mp hqf
    have he := congrArg P hv
    simp only [Pv, map_one] at he
    simp only [hv, one_mul] at he
    exact (ht he).elim
  · have he : v*t=1 := by
      apply mul_left_cancel (a := u)
      simpa only [mul_one, mul_assoc, h.comm_tu.left_comm, h.comm_tv.eq] using hqf
    have he' := congrArg P he
    simp only [map_mul, Pv, Pt, map_one] at he'
    simp only [he, one_mul] at he'
    exact (ht he').elim
  · have hu : u = 1 := mul_eq_left.mp hqf
    have hv := congrArg P hu
    simp only [Pu, map_one] at hv
    simp only [hu, one_mul] at hv
    have he := congrArg P hv
    simp only [Pv, map_one] at he
    simp only [hv, one_mul] at he
    exact (ht he).elim
  · have he : u*t=1 := by
      apply mul_left_cancel (a := w)
      simpa only [mul_one, mul_assoc, h.comm_tu.left_comm,
        h.comm_tv.left_comm, h.comm_tw.left_comm, h.comm_vw.left_comm,
        h.comm_tu.eq, h.comm_uw.eq, h.comm_tv.eq] using hqf
    have he' := congrArg P he
    simp only [map_mul, Pu, Pt, map_one] at he'
    have hv : v=1 := by
      rw [mul_assoc u v t, h.comm_tv.symm.eq, ← mul_assoc, he, one_mul] at he'
      exact he'
    have he'' := congrArg P hv
    simp only [Pv, map_one] at he''
    simp only [hv, one_mul] at he''
    exact (ht he'').elim
  · have he : u*v=1 := by
      apply mul_left_cancel (a := w)
      simpa only [mul_one, mul_assoc, h.comm_vw.left_comm, h.comm_vu.eq] using hqf
    have he' := congrArg P he
    simp only [map_mul, Pu, Pv, map_one] at he'
    have hvt : v*t=1 := by
      simpa only [← mul_assoc, he, one_mul] using he'
    have he'' := congrArg P hvt
    simp only [map_mul, Pv, Pt, map_one] at he''
    simp only [hvt, one_mul] at he''
    exact (ht he'').elim
  · have he : u*v*t=1 := by
      apply mul_left_cancel (a := u*w)
      simpa only [mul_one, mul_assoc, h.comm_tw.left_comm, h.comm_tu.left_comm,
        h.comm_tv.left_comm, h.comm_vw.left_comm, h.comm_vu.left_comm, h.comm_uw.left_comm,
        h.comm_tv.eq, h.comm_vu.eq, h.comm_tu.eq, h.comm_uw.eq] using hqf
    have he' := congrArg P he
    simp only [map_mul, Pu, Pv, Pt, map_one] at he'
    have hvt : v*t=1 := by
      rw [mul_assoc (u*v) (v*t) t, h.comm_tv.symm.eq, mul_assoc t v t,
        ← mul_assoc (u*v) t (v*t), he, one_mul] at he'
      exact he'
    have he'' := congrArg P hvt
    simp only [map_mul, Pv, Pt, map_one] at he''
    simp only [hvt, one_mul] at he''
    exact (ht he'').elim
end Tits.ParrottSylowSeedRelations

