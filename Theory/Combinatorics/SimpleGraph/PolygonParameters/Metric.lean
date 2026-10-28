module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters

/-!
# Point-neighbor counts in a finite even polygon

Connectedness, a bipartition, the diameter and girth bounds, and the two
valences determine the sums over vertices at distance two. The unique
predecessor below the diameter is the only geometric counting input.
This supplies distance-matrix recurrences for the hexagon and octagon
parameter constraints of Feit--Higman (1964), Theorems 1--2.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters
open SimpleGraph.OctagonShortPaths
open scoped BigOperators
variable {V : Type*} {G : SimpleGraph V} [Fintype V]
attribute [local instance] Classical.propDecidable
local instance : DecidableEq V := Classical.decEq _

structure Datum (G : SimpleGraph V) (m s t : ℕ) where
  color : V → ZMod 2
  color_adj : ∀ ⦃u v⦄, G.Adj u v → color u+1=color v
  connected : G.Connected
  cycle_bound : ∀ v (c : G.Walk v v), c.IsCycle → 2*m ≤ c.length
  diameter : ∀ u v, G.dist u v ≤ m
  valence : ∀ v, neighborCard G v = if color v=0 then t+1 else s+1

namespace Datum
variable {m s t : ℕ} (D : Datum G m s t)

theorem even_point_distance {u v : V} (hu : D.color u=0) (hv : D.color v=0) :
    Even (G.dist u v) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  have h := distance_color D.connected D.color D.color_adj u v
  simpa only [hu,hv,zero_add] using h

theorem neighbor_distance_interior (heven : Even m)
    {u v r : V} (hu : D.color u=0) (hr : D.color r=0) (huv : G.Adj u v) :
    0<G.dist v r ∧ G.dist v r<m := by
  have hcol : D.color v=1 := by simpa only [hu,zero_add] using (D.color_adj huv).symm
  have hc := distance_color D.connected D.color D.color_adj v r
  rw [hcol,hr] at hc
  have hb := D.diameter v r
  have h0 : G.dist v r ≠ 0 := by intro h; simp [h] at hc
  have hm : G.dist v r ≠ m := by
    intro h
    rw [h, ZMod.natCast_eq_zero_iff_even.mpr heven,add_zero] at hc
    exact one_ne_zero hc
  omega

theorem double_point_sum (hm : 2 < m) (heven : Even m)
    (u r : V) (hu : D.color u=0) (hr : D.color r=0) (f : ℕ → ℤ) :
    (∑ v, if G.dist u v=2 then f (G.dist v r) else 0) =
      if G.dist u r=0 then ((t : ℤ)+1)*s*f 2 else
      if G.dist u r=m then ((t : ℤ)+1)*f (m-2)+((t : ℤ)+1)*(s-1)*f m else
      f (G.dist u r-2)+((s : ℤ)-1)*f (G.dist u r)+((s : ℤ)*t)*f (G.dist u r+2) := by
  classical
  have hdegree : neighborCard G u=t+1 := by rw [D.valence,hu,if_pos rfl]
  let g : ℕ → ℤ := fun n => f (n-1)+(s : ℤ)*f (n+1)
  have hinner (w : V) (huw : G.Adj u w) :
      neighborSum G w (fun v=>f (G.dist v r))=g (G.dist w r) := by
    obtain ⟨hpos,hshort⟩ := D.neighbor_distance_interior heven hu hr huw
    rw [neighborSum_interior m D.connected D.color D.color_adj D.cycle_bound r w hpos hshort]
    have hw : D.color w=1 := by simpa only [hu,zero_add] using (D.color_adj huw).symm
    rw [D.valence,hw,if_neg one_ne_zero]
    simp [g]
  have ht := two_step_sum m hm D.connected D.cycle_bound u (fun v=>f (G.dist v r))
  have hh : neighborSum G u (fun w=>neighborSum G w (fun v=>f (G.dist v r))) =
      neighborSum G u (fun w=>g (G.dist w r)) := neighborSum_congr u hinner
  rw [hh,hdegree] at ht
  obtain ⟨k,hk⟩ := D.even_point_distance hu hr
  by_cases h0 : G.dist u r=0
  · rw [if_pos h0]
    rw [neighborSum_zero_distance D.connected r u h0,hdegree] at ht
    norm_num [g,h0] at ht
    linear_combination -ht
  · rw [if_neg h0]
    by_cases hlast : G.dist u r=m
    · rw [if_pos hlast]
      rw [neighborSum_last m (by omega) D.connected D.color D.color_adj D.diameter r u hlast,hdegree] at ht
      have hm1 : m-1-1=m-2 := by omega
      have hm2 : m-1+1=m := by omega
      simp only [g,hlast,hm1,hm2,Nat.cast_add,Nat.cast_one] at ht
      linear_combination -ht
    · rw [if_neg hlast]
      have hb := D.diameter u r
      have hp : 0<G.dist u r := by omega
      have hs : G.dist u r<m := by omega
      have hlo : 2≤G.dist u r := by omega
      rw [neighborSum_interior m D.connected D.color D.color_adj D.cycle_bound r u hp hs,hdegree] at ht
      have hm : G.dist u r-1-1=G.dist u r-2 := by omega
      have hp1 : G.dist u r-1+1=G.dist u r := by omega
      have hp2 : G.dist u r+1-1=G.dist u r := by omega
      have hp3 : G.dist u r+1+1=G.dist u r+2 := by omega
      simp only [g,hm,hp1,hp2,hp3,Nat.cast_add,Nat.cast_one] at ht
      linear_combination -ht

end Datum
end SimpleGraph.PolygonParameters
