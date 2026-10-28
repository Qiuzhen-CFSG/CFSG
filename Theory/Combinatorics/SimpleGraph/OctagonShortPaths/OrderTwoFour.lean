module

public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.TwoStepSums
public import Mathlib.Tactic.NormNum

/-!
# The point-graph intersection numbers of an octagon of order (2,4)

The datum contains only connectedness, girth, diameter, a bipartition and the
two vertex valences. Two successive weighted neighbor sums, minus the immediate
return walks, give the point-graph intersection numbers: (1,1,8) at distances
one through three, and (5,5,0) at distance four. No recurrence or opposition
count is part of the input. The binary Ree coset geometry constructs this datum
from its actual parabolics.

Source: Aschbacher–Smith J.5.9–12, printed pp.448–449.
-/

public noncomputable section
namespace SimpleGraph.OctagonShortPaths
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure OrderTwoFourDatum (G : SimpleGraph V) where
  color : V → ZMod 2
  color_adj : ∀ ⦃u v⦄,G.Adj u v → color u+1=color v
  connected : G.Connected
  cycle_bound : ∀ v(c:G.Walk v v),c.IsCycle →16≤c.length
  diameter : ∀ u v,G.dist u v≤8
  valence : ∀ v,neighborCard G v=if color v=0 then 5 else 3

namespace OrderTwoFourDatum
variable (D : OrderTwoFourDatum G)

theorem even_point_distance {u v : V} (hu : D.color u=0) (hv : D.color v=0) :
    Even (G.dist u v) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  have h := distance_color D.connected D.color D.color_adj u v
  simpa only [hu,hv,zero_add] using h

theorem neighbor_distance_interior {u v r : V} (hu : D.color u=0)
    (hr : D.color r=0) (huv : G.Adj u v) : 0<G.dist v r ∧ G.dist v r<8 := by
  have hcol : D.color v=1 := by simpa only [hu,zero_add] using (D.color_adj huv).symm
  have hc := distance_color D.connected D.color D.color_adj v r
  rw [hcol,hr] at hc
  have hb := D.diameter v r
  have h0 : G.dist v r ≠ 0 := by intro h; simp [h] at hc
  have h8 : G.dist v r ≠ 8 := by
    intro h
    rw [h] at hc
    exact (by decide : ¬ ((1:ZMod 2)+8=0)) hc
  omega

theorem double_point_sum (u r : V) (hu : D.color u=0) (hr : D.color r=0)
    (f : ℕ → ℤ) :
    (∑ v, if G.dist u v=2 then f (G.dist v r) else 0) =
      if G.dist u r=0 then 10*f 2 else
      if G.dist u r=8 then 5*f 6+5*f 8 else
      f (G.dist u r-2)+f (G.dist u r)+8*f (G.dist u r+2) := by
  classical
  have hdegree : neighborCard G u=5 := by rw [D.valence,hu,if_pos rfl]
  let g : ℕ → ℤ := fun n => f (n-1)+2*f (n+1)
  have hinner (w : V) (huw : G.Adj u w) :
      neighborSum G w (fun v=>f (G.dist v r))=g (G.dist w r) := by
    obtain ⟨hpos,hshort⟩ := D.neighbor_distance_interior hu hr huw
    rw [neighborSum_interior D.connected D.color D.color_adj D.cycle_bound r w hpos hshort]
    have hw : D.color w=1 := by simpa only [hu,zero_add] using (D.color_adj huw).symm
    rw [D.valence,hw,if_neg one_ne_zero]
    norm_num [g]
  have ht := two_step_sum D.connected D.cycle_bound u (fun v=>f (G.dist v r))
  have hh : neighborSum G u (fun w=>neighborSum G w (fun v=>f (G.dist v r))) =
      neighborSum G u (fun w=>g (G.dist w r)) := neighborSum_congr u hinner
  rw [hh,hdegree] at ht
  obtain ⟨k,hk⟩ := D.even_point_distance hu hr
  by_cases h0 : G.dist u r=0
  · rw [if_pos h0]
    rw [neighborSum_zero_distance D.connected r u h0,hdegree] at ht
    norm_num [g,h0] at ht
    omega
  · rw [if_neg h0]
    by_cases h8 : G.dist u r=8
    · rw [if_pos h8]
      rw [neighborSum_last D.connected D.color D.color_adj D.diameter r u h8,hdegree] at ht
      norm_num [g,h8] at ht
      omega
    · rw [if_neg h8]
      have hb := D.diameter u r
      have hp : 0<G.dist u r := by omega
      have hs : G.dist u r<8 := by omega
      have hlo : 2≤G.dist u r := by omega
      rw [neighborSum_interior D.connected D.color D.color_adj D.cycle_bound r u hp hs,hdegree] at ht
      have hm : G.dist u r-1-1=G.dist u r-2 := by omega
      have hp1 : G.dist u r-1+1=G.dist u r := by omega
      have hp2 : G.dist u r+1-1=G.dist u r := by omega
      have hp3 : G.dist u r+1+1=G.dist u r+2 := by omega
      norm_num only [g,hm,hp1,hp2,hp3,Nat.cast_ofNat] at ht
      omega

end OrderTwoFourDatum
end SimpleGraph.OctagonShortPaths
