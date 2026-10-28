module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Metric

/-!
# Nonempty distance spheres and odd polygon parameters

Positive parameters allow each geodesic below the diameter to extend. Thus
every distance in the declared range occurs. Opposite vertices have equally
many neighbors: the unique geodesics of length `m-1` give a bijection between
their neighbor sets. For odd gonality the endpoints have different colors,
so the two polygon parameters coincide.

These are the geometric inputs to the finite-polygon spectral argument
cited in Fong--Seitz I (1J), printed p.6 (Feit--Higman, J. Algebra 1
(1964), 114--131). Only the literal metric and valence hypotheses are used.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters.Datum
open SimpleGraph.OctagonShortPaths
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {m s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityGeodesicsDecidableEq0 : DecidableEq V := Classical.decEq _

/-- Before the diameter a geodesic can be extended without backtracking. -/
theorem exists_successor (D : Datum G m s t) (hs : 0<s) (ht : 0<t)
    (r v : V) (hshort : G.dist v r<m) :
    ∃ w, G.Adj v w ∧ G.dist w r=G.dist v r+1 := by
  have hval : 1 < (Finset.univ.filter (G.Adj v)).card := by
    change 1 < neighborCard G v
    rw [D.valence]
    split_ifs <;> omega
  by_cases hzero : G.dist v r=0
  · obtain ⟨w,hw,_⟩ := Finset.exists_mem_ne hval v
    have hvw := (Finset.mem_filter.mp hw).2
    have he := D.connected.dist_eq_zero_iff.mp hzero
    refine ⟨w,hvw,?_⟩
    rw [hzero, zero_add, ←he]
    exact dist_eq_one_iff_adj.mpr hvw.symm
  · obtain ⟨w,hw,hunique⟩ := unique_predecessor m D.connected D.cycle_bound r v (by omega) hshort
    obtain ⟨z,hz,hzw⟩ := Finset.exists_mem_ne hval w
    have hvz := (Finset.mem_filter.mp hz).2
    refine ⟨z,hvz,?_⟩
    rcases adjacent_distance_step D.connected D.color D.color_adj r hvz with h|h
    · exact (hzw (hunique z ⟨hvz,h⟩)).elim
    · exact h

/-- Every distance up to the stated diameter actually occurs from every vertex. -/
theorem exists_distance (D : Datum G m s t) (hs : 0<s) (ht : 0<t)
    (r : V) (k : ℕ) (hk : k≤m) : ∃ v, G.dist v r=k := by
  induction k with
  | zero => exact ⟨r, G.dist_self⟩
  | succ k ih =>
    obtain ⟨v,hv⟩ := ih (by omega)
    obtain ⟨w,_,hw⟩ := D.exists_successor hs ht r v (by omega)
    exact ⟨w,by omega⟩

/-- Opposite vertices have equally many neighbors, via unique short geodesics. -/
theorem opposite_neighborCard_eq (D : Datum G m s t) (hm : 2≤m)
    (r v : V) (hv : G.dist v r=m) : neighborCard G v = neighborCard G r := by
  classical
  let A := {w : V // G.Adj v w}
  let B := {u : V // G.Adj r u}
  have hdistA (w : A) : G.dist w.val r=m-1 := by
    have hd := adjacent_distance_step D.connected D.color D.color_adj r w.property
    have hb := D.diameter w.val r
    omega
  have hdistB (u : B) : G.dist u.val v=m-1 := by
    have hd := adjacent_distance_step D.connected D.color D.color_adj v u.property
    have hb := D.diameter u.val v
    have hv' : G.dist r v=m := by rw [G.dist_comm]; exact hv
    omega
  have ha (w : A) : ∃! u : B, G.dist w.val u.val=m-2 := by
    have hd := hdistA w
    have hd' : G.dist r w.val=m-1 := by rw [G.dist_comm]; exact hd
    obtain ⟨u,hu,hunique⟩ := unique_predecessor m D.connected D.cycle_bound w.val r (by omega) (by omega)
    refine ⟨⟨u,hu.1⟩,?_,?_⟩
    · change G.dist w.val u=m-2
      rw [G.dist_comm]; omega
    · intro u' hu'
      apply Subtype.ext
      exact hunique u'.val ⟨u'.property,by rw [G.dist_comm]; omega⟩
  have hb (u : B) : ∃! w : A, G.dist w.val u.val=m-2 := by
    have hd := hdistB u
    have hd' : G.dist v u.val=m-1 := by rw [G.dist_comm]; exact hd
    obtain ⟨w,hw,hunique⟩ := unique_predecessor m D.connected D.cycle_bound u.val v (by omega) (by omega)
    refine ⟨⟨w,hw.1⟩,?_,?_⟩
    · change G.dist w u.val=m-2
      omega
    · intro w' hw'
      apply Subtype.ext
      exact hunique w'.val ⟨w'.property,by omega⟩
  let e : A ≃ B := Equiv.ofBijective
    (fun w => (ha w).choose) (by
      constructor
      · intro w z hwz
        exact (hb ((ha w).choose)).unique (ha w).choose_spec.1 (by simpa only [hwz] using (ha z).choose_spec.1)
      · intro u
        obtain ⟨w,hw,_⟩ := hb u
        exact ⟨w, (ha w).unique (ha w).choose_spec.1 hw⟩)
  have hc := Fintype.card_congr e
  simpa [A,B,neighborCard,Fintype.card_subtype] using hc

/-- The two valences coincide when the polygon has odd gonality. -/
theorem parameters_eq_of_odd (D : Datum G m s t) (hm : 2≤m)
    (hs : 0<s) (ht : 0<t) (hp : ∃ r, D.color r=0) (ho : Odd m) : s=t := by
  obtain ⟨r,hr⟩ := hp
  obtain ⟨v,hv⟩ := D.exists_distance hs ht r m le_rfl
  have hc := distance_color D.connected D.color D.color_adj r v
  have hv' : G.dist r v=m := by rw [G.dist_comm]; exact hv
  have hmcast : (m : ZMod 2)=1 := ZMod.natCast_eq_one_iff_odd.mpr ho
  have hcol : D.color v=1 := by simpa [hr,hv',hmcast] using hc.symm
  have hval := D.opposite_neighborCard_eq hm r v hv
  rw [D.valence,D.valence,hr,hcol,if_pos rfl,if_neg one_ne_zero] at hval
  omega
end SimpleGraph.PolygonParameters.Datum
