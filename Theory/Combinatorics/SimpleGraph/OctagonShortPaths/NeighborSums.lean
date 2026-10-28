module

public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.Metric
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Weighted neighbor counts in bipartite octagonal graphs

A two-coloring makes adjacent distances differ by one. Below distance eight,
the unique predecessor leaves every other neighbor one step farther away; at
distance eight every neighbor is inward. Summing an arbitrary integer-valued
function of distance packages the source intersection numbers without any
assumed distance-regularity or matrix recurrence.

Source: Aschbacher–Smith J.5.9–12, the generalized octagon of order (2,4).
-/

public section
namespace SimpleGraph.OctagonShortPaths
variable {V : Type*} {G : SimpleGraph V}

theorem walk_color (color : V → ZMod 2)
    (hc : ∀ ⦃u v⦄, G.Adj u v → color u+1=color v)
    {u v : V} (p : G.Walk u v) : color u + (p.length : ZMod 2)=color v := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    rw [Walk.length_cons,Nat.cast_add,Nat.cast_one,←add_assoc,add_right_comm,hc huv]
    exact ih

theorem distance_color (conn : G.Connected) (color : V → ZMod 2)
    (hc : ∀ ⦃u v⦄, G.Adj u v → color u+1=color v) (u v : V) :
    color u + (G.dist u v : ZMod 2)=color v := by
  obtain ⟨p,hp⟩ := conn.exists_walk_length_eq_dist u v
  simpa only [hp] using walk_color color hc p

theorem adjacent_distance_ne (conn : G.Connected) (color : V → ZMod 2)
    (hc : ∀ ⦃u v⦄, G.Adj u v → color u+1=color v)
    (r : V) {u v : V} (huv : G.Adj u v) : G.dist u r ≠ G.dist v r := by
  intro he
  have hu := distance_color conn color hc u r
  have hv := distance_color conn color hc v r
  rw [he] at hu
  have hcuv : color u=color v := add_right_cancel (hu.trans hv.symm)
  have hzero : (1 : ZMod 2)=0 := by
    have hh := hc huv
    rw [hcuv] at hh
    exact add_left_cancel (hh.trans (add_zero _).symm)
  exact one_ne_zero hzero

theorem adjacent_distance_step (conn : G.Connected) (color : V → ZMod 2)
    (hc : ∀ ⦃u v⦄, G.Adj u v → color u+1=color v)
    (r : V) {u v : V} (huv : G.Adj u v) :
    G.dist v r+1=G.dist u r ∨ G.dist v r=G.dist u r+1 := by
  have hne := adjacent_distance_ne conn color hc r huv
  have htri := conn.dist_triangle (u:=u) (v:=v) (w:=r)
  rw [dist_eq_one_iff_adj.mpr huv] at htri
  rcases huv.diff_dist_adj (u:=r) with h | h | h
  all_goals rw [dist_comm (u:=r) (v:=u),dist_comm (u:=r) (v:=v)] at h
  · exact (hne h.symm).elim
  · exact Or.inr h
  · exact Or.inl (by omega)

open scoped BigOperators
variable [Fintype V]

@[expose] noncomputable def neighborSum (G : SimpleGraph V) (v : V) (f : V → ℤ) : ℤ := by
  classical
  exact ∑ w ∈ Finset.univ.filter (G.Adj v), f w

@[expose] noncomputable def neighborCard (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (G.Adj v)).card

theorem neighborSum_congr (v : V) {f g : V → ℤ}
    (h : ∀ w, G.Adj v w → f w=g w) : neighborSum G v f=neighborSum G v g := by
  classical
  apply Finset.sum_congr rfl
  intro w hw
  exact h w (Finset.mem_filter.mp hw).2

theorem neighborSum_constant (v : V) (a : ℤ) :
    neighborSum G v (fun _ => a)=(neighborCard G v : ℤ)*a := by
  classical
  simp [neighborSum,neighborCard]

theorem neighborSum_zero_distance (conn : G.Connected)
    (r v : V) (hzero : G.dist v r=0) (f : ℕ → ℤ) :
    neighborSum G v (fun w => f (G.dist w r))=(neighborCard G v : ℤ)*f 1 := by
  have he : v=r := (conn.dist_eq_zero_iff).mp hzero
  subst v
  calc
    _=neighborSum G r (fun _ => f 1) := neighborSum_congr _ fun w hw => by
      rw [dist_eq_one_iff_adj.mpr hw.symm]
    _=_ := neighborSum_constant _ _

theorem neighborSum_interior (conn : G.Connected) (color : V → ZMod 2)
    (hc : ∀ ⦃u v⦄, G.Adj u v → color u+1=color v)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 16 ≤ c.length)
    (r v : V) (hpos : 0<G.dist v r) (hshort : G.dist v r<8) (f : ℕ → ℤ) :
    neighborSum G v (fun w => f (G.dist w r)) =
      f (G.dist v r-1)+(neighborCard G v-1 : ℤ)*f (G.dist v r+1) := by
  classical
  obtain ⟨w,⟨hvw,hw⟩,hunique⟩ := unique_predecessor conn hg r v hpos hshort
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

theorem neighborSum_last (conn : G.Connected) (color : V → ZMod 2)
    (hc : ∀ ⦃u v⦄, G.Adj u v → color u+1=color v)
    (hd : ∀ u v,G.dist u v≤8) (r v : V) (hlast : G.dist v r=8) (f : ℕ → ℤ) :
    neighborSum G v (fun w => f (G.dist w r))=(neighborCard G v : ℤ)*f 7 := by
  calc
    _ = neighborSum G v (fun _ => f 7) := by
      apply neighborSum_congr
      intro w hw
      have hs := adjacent_distance_step conn color hc r hw
      have hb := hd w r
      have he : G.dist w r=7 := by omega
      rw [he]
    _ = _ := neighborSum_constant _ _

end SimpleGraph.OctagonShortPaths
