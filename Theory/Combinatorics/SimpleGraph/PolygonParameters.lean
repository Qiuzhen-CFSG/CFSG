module
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.TwoStepSums
public import Mathlib.Tactic.LinearCombination

public noncomputable section
namespace SimpleGraph.PolygonParameters
open SimpleGraph.OctagonShortPaths
variable {V : Type*} {G : SimpleGraph V}

theorem paths_eq (m : ℕ)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 2*m ≤ c.length)
    {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < 2*m) : p = q := by
  by_contra hne
  obtain ⟨w, _, _, c, hc, hle⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  have h := hg w c hc
  omega

theorem unique_predecessor (m : ℕ) (hc : G.Connected)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 2*m ≤ c.length)
    (r v : V) (hpos : 0<G.dist v r) (hshort : G.dist v r<m) :
    ∃! w, G.Adj v w ∧ G.dist w r+1=G.dist v r := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v r
  cases p with
  | nil => simp at hpos
  | @cons v w r hvw p =>
    have hd := G.dist_le p
    have ht := hc.dist_triangle (u:=v) (v:=w) (w:=r)
    rw [dist_eq_one_iff_adj.mpr hvw] at ht
    have hlen : p.length+1=G.dist v r := hp
    have he : G.dist w r+1=G.dist v r := by omega
    refine ⟨w,⟨hvw,he⟩,?_⟩
    rintro z ⟨hvz,hz⟩
    obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist z r
    have hq' : (Walk.cons hvz q).length=G.dist v r := by
      simpa only [Walk.length_cons,hq] using hz
    have heq := paths_eq m hg
      ((Walk.cons hvz q).isPath_of_length_eq_dist hq')
      ((Walk.cons hvw p).isPath_of_length_eq_dist hp) (by rw [hq',hp]; omega)
    have hs := congrArg (fun a : G.Walk v r => a.getVert 1) heq
    simpa using hs


open scoped BigOperators
variable [Fintype V]
attribute [local instance] Classical.propDecidable
local instance : DecidableEq V := Classical.decEq _

theorem neighborSum_interior (m : ℕ) (conn : G.Connected) (color : V → ZMod 2)
    (hc : ∀ ⦃u v⦄, G.Adj u v → color u+1=color v)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 2*m ≤ c.length)
    (r v : V) (hpos : 0<G.dist v r) (hshort : G.dist v r<m) (f : ℕ → ℤ) :
    neighborSum G v (fun w => f (G.dist w r)) =
      f (G.dist v r-1)+(neighborCard G v-1 : ℤ)*f (G.dist v r+1) := by
  classical
  obtain ⟨w,⟨hvw,hw⟩,hunique⟩ := unique_predecessor m conn hg r v hpos hshort
  let S := Finset.univ.filter (G.Adj v)
  have hwS : w ∈ S := by simp [S,hvw]
  have hout : ∀ z ∈ S.erase w, G.dist z r=G.dist v r+1 := by
    intro z hz
    have hzs := Finset.mem_erase.mp hz
    have hvz := (Finset.mem_filter.mp hzs.2).2
    rcases adjacent_distance_step conn color hc r hvz with h | h
    · exact (hzs.1 (hunique z ⟨hvz,h⟩)).elim
    · exact h
  change ∑ z ∈ S, f (G.dist z r)=_
  rw [← Finset.add_sum_erase S (fun z => f (G.dist z r)) hwS]
  have he : G.dist w r=G.dist v r-1 := by omega
  rw [he]
  congr 1
  calc
    ∑ z ∈ S.erase w, f (G.dist z r) = ∑ _z ∈ S.erase w, f (G.dist v r+1) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hout z hz]
    _ = _ := by
      have hcard : 1 ≤ S.card := Finset.one_le_card.mpr ⟨w,hwS⟩
      simp only [Finset.sum_const,Finset.card_erase_of_mem hwS,nsmul_eq_mul]
      rw [Nat.cast_sub hcard,Nat.cast_one]
      rfl

theorem neighborSum_last (m : ℕ) (hm : 0 < m) (conn : G.Connected) (color : V → ZMod 2)
    (hc : ∀ ⦃u v⦄, G.Adj u v → color u+1=color v)
    (hd : ∀ u v,G.dist u v≤m) (r v : V) (hlast : G.dist v r=m) (f : ℕ → ℤ) :
    neighborSum G v (fun w => f (G.dist w r))=(neighborCard G v : ℤ)*f (m-1) := by
  calc
    _ = neighborSum G v (fun _ => f (m-1)) := by
      apply neighborSum_congr
      intro w hw
      have hs := adjacent_distance_step conn color hc r hw
      have hb := hd w r
      have he : G.dist w r=m-1 := by omega
      rw [he]
    _ = _ := neighborSum_constant _ _

omit [Fintype V] in
theorem distance_two_of_common (m : ℕ) (hm : 2 < m) (conn : G.Connected)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 2*m ≤ c.length)
    {u v w : V} (huv : u≠v) (huw : G.Adj u w) (hwv : G.Adj w v) :
    G.dist u v=2 := by
  let p := Walk.cons huw (Walk.cons hwv Walk.nil)
  have hp : p.IsPath := by
    simp [p,Walk.cons_isPath_iff,huw.ne,hwv.ne,huv]
  obtain ⟨q,hq⟩ := conn.exists_walk_length_eq_dist u v
  have hd := G.dist_le p
  have he : p=q := paths_eq m hg hp (q.isPath_of_length_eq_dist hq) (by
    have hl : p.length=2 := rfl
    omega)
  rw [←hq,←he]
  rfl

theorem common_neighbor_card (m : ℕ) (hm : 2 < m) (conn : G.Connected)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 2*m ≤ c.length)
    (u v : V) (huv : G.dist u v=2) :
    (Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj w v)).card=1 := by
  classical
  have hd : G.dist v u=2 := by rwa [dist_comm]
  obtain ⟨w,⟨hvw,hw⟩,hunique⟩ := unique_predecessor m conn hg u v (by omega) (by omega)
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
theorem edgeWeight_square (m : ℕ) (hm : 2 < m) (conn : G.Connected)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 2*m ≤ c.length) (u v : V) :
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
    · simp [he,hd,common_neighbor_card m hm conn hg u v hd]
    · have hc : Finset.univ.filter (fun w=>G.Adj u w ∧ G.Adj w v)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have hh := (Finset.mem_filter.mp hw).2
        exact hd (distance_two_of_common m hm conn hg he hh.1 hh.2)
      simp [hc,he,hd]

theorem two_step_sum (m : ℕ) (hm : 2 < m) (conn : G.Connected)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 2*m ≤ c.length)
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
      simp_rw [edgeWeight_square m hm conn hg,add_mul]
      rw [Finset.sum_add_distrib]
      simp

end SimpleGraph.PolygonParameters
