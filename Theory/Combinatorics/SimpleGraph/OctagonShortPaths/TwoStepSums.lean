module

public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.NeighborSums
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Counting walks of length two in an octagonal graph

Distinct vertices have a common neighbor exactly at distance two, and that
neighbor is unique. This follows by comparing paths of combined length below
sixteen. Consequently two successive neighbor sums equal the sum over vertices
at distance two, plus the immediate return walks counted by the valence.

Source: the point-graph intersection calculation for Aschbacher–Smith J.5.9–12.
-/

public noncomputable section
namespace SimpleGraph.OctagonShortPaths
open scoped BigOperators
variable {V : Type*} {G : SimpleGraph V} [Fintype V]
attribute [local instance] Classical.propDecidable
local instance : DecidableEq V := Classical.decEq _

omit [Fintype V] in
theorem distance_two_of_common (conn : G.Connected)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    {u v w : V} (huv : u≠v) (huw : G.Adj u w) (hwv : G.Adj w v) :
    G.dist u v=2 := by
  let p := Walk.cons huw (Walk.cons hwv Walk.nil)
  have hp : p.IsPath := by
    simp [p,Walk.cons_isPath_iff,huw.ne,hwv.ne,huv]
  obtain ⟨q,hq⟩ := conn.exists_walk_length_eq_dist u v
  have hd := G.dist_le p
  have he : p=q := paths_eq hg hp (q.isPath_of_length_eq_dist hq) (by
    have hl : p.length=2 := rfl
    omega)
  rw [←hq,←he]
  rfl

theorem common_neighbor_card (conn : G.Connected)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    (u v : V) (huv : G.dist u v=2) :
    (Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj w v)).card=1 := by
  classical
  have hd : G.dist v u=2 := by rwa [dist_comm]
  obtain ⟨w,⟨hvw,hw⟩,hunique⟩ := unique_predecessor conn hg u v (by omega) (by omega)
  have hwu : G.dist w u=1 := by omega
  have huw : G.Adj u w := (dist_eq_one_iff_adj.mp hwu).symm
  have he : Finset.univ.filter (fun z => G.Adj u z ∧ G.Adj z v)={w} := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · rintro ⟨huz,hzv⟩
      exact hunique z ⟨hzv.symm,by rw [dist_eq_one_iff_adj.mpr huz.symm,hd]⟩
    · rintro rfl
      exact ⟨huw,hvw.symm⟩
  rw [he,Finset.card_singleton]

@[expose] noncomputable def edgeWeight (G : SimpleGraph V) (u v : V) : ℤ := by
  classical
  exact if G.Adj u v then 1 else 0

theorem neighborSum_eq_sum (v : V) (f : V → ℤ) :
    neighborSum G v f=∑ w,edgeWeight G v w*f w := by
  classical
  simp [neighborSum,Finset.sum_filter,edgeWeight]

theorem edgeWeight_square (conn : G.Connected)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length) (u v : V) :
    ∑ w,edgeWeight G u w*edgeWeight G w v =
      (if u=v then (neighborCard G u : ℤ) else 0) +
      (if G.dist u v=2 then 1 else 0) := by
  classical
  have hcount : ∑ w,edgeWeight G u w*edgeWeight G w v =
      ((Finset.univ.filter (fun w=> G.Adj u w ∧ G.Adj w v)).card : ℤ) := by
    calc
      _ = ∑ w, if G.Adj u w ∧ G.Adj w v then (1:ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        simp only [edgeWeight]
        split_ifs <;> simp_all
      _ = _ := Finset.sum_boole _ _
  rw [hcount]
  by_cases he : u=v
  · subst v
    simp [neighborCard,adj_comm]
  · by_cases hd : G.dist u v=2
    · simp [he,hd,common_neighbor_card conn hg u v hd]
    · have hc : Finset.univ.filter (fun w=>G.Adj u w ∧ G.Adj w v)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have hh := (Finset.mem_filter.mp hw).2
        exact hd (distance_two_of_common conn hg he hh.1 hh.2)
      simp [hc,he,hd]

theorem two_step_sum (conn : G.Connected)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    (u : V) (f : V → ℤ) :
    neighborSum G u (fun w=>neighborSum G w f) =
      (neighborCard G u : ℤ)*f u + ∑ v, if G.dist u v=2 then f v else 0 := by
  classical
  rw [neighborSum_eq_sum]
  simp_rw [neighborSum_eq_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ v,(∑ w,edgeWeight G u w*edgeWeight G w v)*f v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      rw [mul_assoc]
    _ = _ := by
      simp_rw [edgeWeight_square conn hg,add_mul]
      rw [Finset.sum_add_distrib]
      simp

end SimpleGraph.OctagonShortPaths
