module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.MinimalPolynomial
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.DistanceMatrices
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Even

/-!
# The point spectrum in odd polygon gonality

For gonality `2*h+1`, every point is within distance `2*h` of a base point.
The final two-step census has coefficient `s*t+s-1`, since lines at distance
`2*h+1` have all their points in that last point sphere. The resulting
three-term recurrence gives a monic annihilator of degree `h+1`. Nonempty
spheres prove minimality. When the parameters coincide (as proved from the
odd geometry), the nontrivial factor is a sum of consecutive shifted
Chebyshev polynomials.

This supplies the odd spectral input to the finite-polygon theorem cited in
Fong--Seitz I (1J), printed p.6, from Feit--Higman, J. Algebra 1 (1964),
114--131, DOI 10.1016/0021-8693(64)90028-6. The recurrence is proved directly
from `Datum`; the gonality exclusions still require the multiplicity argument.
The internal imports access the existing matrix and polynomial definitions
without changing their public boundaries.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters.Datum
open scoped BigOperators
open SimpleGraph.OctagonShortPaths
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityOddDecidableEq : DecidableEq V := Classical.decEq _

theorem odd_double_point_sum (D : Datum G (2*h+1) s t) (hh : 0<h)
    (u r : V) (hu : D.color u=0) (hr : D.color r=0) (f : ℕ → ℤ) :
    (∑ v, if G.dist u v=2 then f (G.dist v r) else 0) =
      if G.dist u r=0 then ((t : ℤ)+1)*s*f 2 else
      if G.dist u r=2*h then f (2*h-2)+((s : ℤ)*t+s-1)*f (2*h) else
      f (G.dist u r-2)+((s : ℤ)-1)*f (G.dist u r)+((s : ℤ)*t)*f (G.dist u r+2) := by
  have hdegree : neighborCard G u=t+1 := by rw [D.valence,hu,if_pos rfl]
  let g : ℕ → ℤ := fun n => if n=2*h+1 then ((s:ℤ)+1)*f (2*h) else
    f (n-1)+(s:ℤ)*f (n+1)
  have hinner (w : V) (huw : G.Adj u w) :
      neighborSum G w (fun v => f (G.dist v r))=g (G.dist w r) := by
    have hw : D.color w=1 := by simpa only [hu,zero_add] using (D.color_adj huw).symm
    have hval : neighborCard G w=s+1 := by rw [D.valence,hw,if_neg one_ne_zero]
    have hpos : 0<G.dist w r := by
      by_contra hn
      have he := D.connected.dist_eq_zero_iff.mp (show G.dist w r=0 by omega)
      simp [he,hr] at hw
    by_cases he : G.dist w r=2*h+1
    · rw [neighborSum_last (2*h+1) (by omega) D.connected D.color D.color_adj
        D.diameter r w he, hval]
      simp [g,he]
    · have hb := D.diameter w r
      rw [neighborSum_interior (2*h+1) D.connected D.color D.color_adj
        D.cycle_bound r w hpos (by omega), hval]
      simp [g,he]
  have ht := two_step_sum (2*h+1) (by omega) D.connected D.cycle_bound u
    (fun v => f (G.dist v r))
  have hi := neighborSum_congr u hinner
  rw [hi,hdegree] at ht
  obtain ⟨k,hk⟩ := D.even_point_distance hu hr
  have hb := D.diameter u r
  have hshort : G.dist u r<2*h+1 := by omega
  by_cases hzero : G.dist u r=0
  · rw [if_pos hzero]
    rw [neighborSum_zero_distance D.connected r u hzero,hdegree] at ht
    norm_num [g,hzero,show h≠0 by omega] at ht
    linear_combination -ht
  · rw [if_neg hzero]
    rw [neighborSum_interior (2*h+1) D.connected D.color D.color_adj D.cycle_bound
      r u (by omega) hshort,hdegree] at ht
    by_cases hlast : G.dist u r=2*h
    · rw [if_pos hlast]
      simp only [g, hlast, show 2*h-1≠2*h+1 by omega, if_false,
        show 2*h-1-1=2*h-2 by omega, show 2*h-1+1=2*h by omega,
        if_true, Nat.cast_add,Nat.cast_one] at ht
      linear_combination -ht
    · rw [if_neg hlast]
      have hlo : 2≤G.dist u r := by omega
      simp only [g, show G.dist u r-1≠2*h+1 by omega,
        show G.dist u r+1≠2*h+1 by omega, if_false,
        show G.dist u r-1-1=G.dist u r-2 by omega,
        show G.dist u r-1+1=G.dist u r by omega,
        show G.dist u r+1-1=G.dist u r by omega,
        show G.dist u r+1+1=G.dist u r+2 by omega,
        Nat.cast_add,Nat.cast_one] at ht
      linear_combination -ht

theorem odd_matrix_mul_apply (D : Datum G (2*h+1) s t) (hh : 0<h)
    (k : ℕ) (u r : D.Point) :
    (D.distanceMatrix 1*D.distanceMatrix k) u r =
      if G.dist u.val r.val=0 then ((t : ℝ)+1)*s*(if 2=2*k then 1 else 0) else
      if G.dist u.val r.val=2*h then
        (if 2*h-2=2*k then 1 else 0)+
        ((s : ℝ)*t+s-1)*(if 2*h=2*k then 1 else 0) else
        (if G.dist u.val r.val-2=2*k then 1 else 0)+
        ((s : ℝ)-1)*(if G.dist u.val r.val=2*k then 1 else 0)+
        ((s : ℝ)*t)*(if G.dist u.val r.val+2=2*k then 1 else 0) := by
  let f : ℕ → ℤ := fun n => if n=2*k then 1 else 0
  have hs := D.odd_double_point_sum hh u.val r.val u.property r.property f
  have hsum : (∑ v : D.Point,
      if G.dist u.val v.val=2 then f (G.dist v.val r.val) else 0) =
      ∑ v : V, if G.dist u.val v=2 then f (G.dist v r.val) else 0 := by
    have he := Fintype.sum_subtype_add_sum_subtype (fun v => D.color v=0)
      (fun v => if G.dist u.val v=2 then f (G.dist v r.val) else 0)
    have hz : (∑ v : {v : V // ¬D.color v=0},
        if G.dist u.val v.val=2 then f (G.dist v.val r.val) else 0)=0 := by
      apply Finset.sum_eq_zero
      intro v hv
      have hd : G.dist u.val v.val≠2 := fun hd => v.property (D.distance_two_color u.property hd)
      simp [hd]
    simpa only [hz,add_zero] using he
  rw [←hsum] at hs
  have he : (D.distanceMatrix 1*D.distanceMatrix k) u r =
      ((∑ v : D.Point, if G.dist u.val v.val=2 then f (G.dist v.val r.val) else 0 : ℤ) : ℝ) := by
    simp only [Matrix.mul_apply, distanceMatrix, mul_one, Int.cast_sum, f]
    apply Finset.sum_congr rfl
    intro v hv
    split_ifs <;> simp_all
  rw [he,hs]
  simp only [f, Int.cast_ite, Int.cast_zero, Int.cast_one, Int.cast_add,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast]

theorem odd_recurrence (D : Datum G (2*h+1) s t) (hh : 0<h)
    (k : ℕ) (hk : 0<k) (hkh : k<h) :
    D.distanceMatrix 1 * D.distanceMatrix k =
      (if k=1 then (s:ℝ)*(t+1) else (s:ℝ)*t) • D.distanceMatrix (k-1) +
      ((s:ℝ)-1) • D.distanceMatrix k + D.distanceMatrix (k+1) := by
  ext u v
  rw [D.odd_matrix_mul_apply hh]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, distanceMatrix]
  split_ifs <;> try omega
  all_goals ring

theorem odd_last_recurrence (D : Datum G (2*h+1) s t) (hh : 0<h) :
    D.distanceMatrix 1 * D.distanceMatrix h =
      (if h=1 then (s:ℝ)*(t+1) else (s:ℝ)*t) • D.distanceMatrix (h-1) +
      ((s:ℝ)*t+s-1) • D.distanceMatrix h := by
  ext u v
  rw [D.odd_matrix_mul_apply hh]
  obtain ⟨d,hd⟩ := D.even_point_distance u.property v.property
  have hb := D.diameter u.val v.val
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, distanceMatrix]
  split_ifs <;> try omega
  all_goals ring
end SimpleGraph.PolygonParameters.Datum

namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial

def oddAnnihilator (h : ℕ) (s t : ℝ) : ℝ[X] :=
  (X-C (s*t+s-1))*distancePolynomial s t h -
    C (if h=1 then s*(t+1) else s*t)*distancePolynomial s t (h-1)
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityOddDecidableEq2 : DecidableEq V := Classical.decEq _

theorem odd_distancePolynomial_aeval (D : Datum G (2*h+1) s t) (hh : 0<h)
    (k : ℕ) (hk : k≤h) :
    aeval (D.distanceMatrix 1) (distancePolynomial s t k) = D.distanceMatrix k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [distancePolynomial, D.distanceMatrix_zero]
  | one => simp [distancePolynomial]
  | more k ih₀ ih₁ =>
    have h₀ := ih₀ (by omega)
    have h₁ := ih₁ (by omega)
    have hr := D.odd_recurrence hh (k+1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel, Nat.add_eq_right] at hr
    simp only [distancePolynomial, map_sub, map_mul, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one, h₀, h₁, sub_mul, smul_mul_assoc, one_mul]
    linear_combination (norm := module) hr

theorem oddAnnihilator_aeval (D : Datum G (2*h+1) s t) (hh : 0<h) :
    aeval (D.distanceMatrix 1) (oddAnnihilator h s t) = 0 := by
  have h₀ := D.odd_distancePolynomial_aeval hh h le_rfl
  have h₁ := D.odd_distancePolynomial_aeval hh (h-1) (by omega)
  simp only [oddAnnihilator, map_sub, map_mul, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, h₀, h₁, sub_mul, smul_mul_assoc, one_mul,
    D.odd_last_recurrence hh]
  module
end SimpleGraph.PolygonParameters.Datum

namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial

private theorem oddAnnihilator_recurrence (s t : ℝ) (k : ℕ) (hk : 1≤k) :
    oddAnnihilator (k+2) s t =
      (X-C (s-1))*oddAnnihilator (k+1) s t - C (s*t)*oddAnnihilator k s t := by
  have hrec (i : ℕ) (hi : 0 < i) : distancePolynomial s t (i+2) =
      (X-C (s-1))*distancePolynomial s t (i+1)-C (s*t)*distancePolynomial s t i := by
    rw [distancePolynomial, if_neg (by omega)]
  have he : k-1+2=k+1 := by omega
  have he' : k-1+1=k := by omega
  have hrec' := distancePolynomial.eq_3 s t (k-1)
  simp only [Nat.succ_eq_add_one] at hrec'
  rw [he,he'] at hrec'
  have hcase : (if k-1=0 then s*(t+1) else s*t) =
      (if k=1 then s*(t+1) else s*t) := by
    have heq : (k-1=0) ↔ k=1 := by omega
    simp only [heq]
  rw [hcase] at hrec'
  simp only [oddAnnihilator, show k+2≠1 by omega, show k+1≠1 by omega,
    if_false, Nat.add_sub_cancel, show k+2-1=k+1 by omega]
  rw [hrec k (by omega),hrec']
  ring

/-- In odd gonality the nontrivial factor is a sum of two consecutive
shifted Chebyshev polynomials. -/
theorem oddAnnihilator_factorization (q : ℝ) (h : ℕ) (hh : 0<h) :
    oddAnnihilator h q q = (X-C (q*(q+1))) *
      (spectralPolynomial q q h+C q*spectralPolynomial q q (h-1)) := by
  obtain ⟨k,rfl⟩ : ∃ k,h=k+1 := ⟨h-1,by omega⟩
  clear hh
  induction k using Nat.twoStepInduction with
  | zero => norm_num [oddAnnihilator,distancePolynomial,spectralPolynomial,map_sub,map_add,map_mul]; ring
  | one => norm_num [oddAnnihilator,distancePolynomial,spectralPolynomial,map_sub,map_add,map_mul]; ring
  | more k ih₀ ih₁ =>
    rw [show k+2+1=(k+1)+2 by omega, oddAnnihilator_recurrence q q (k+1) (by omega)]
    rw [ih₁,ih₀]
    simp only [Nat.add_sub_cancel, show k+1+2-1=k+2 by omega]
    rw [spectralPolynomial.eq_3 q q (k+1), spectralPolynomial.eq_3 q q k]
    ring

private theorem oddAnnihilator_monic_natDegree (s t : ℝ) (h : ℕ) (hh : 0<h) :
    (oddAnnihilator h s t).Monic ∧ (oddAnnihilator h s t).natDegree=h+1 := by
  have hm := (monic_X_sub_C (s*t+s-1)).mul (distancePolynomial_monic s t h)
  have hd : ((X-C (s*t+s-1))*distancePolynomial s t h).natDegree=h+1 := by
    rw [(monic_X_sub_C _).natDegree_mul (distancePolynomial_monic s t h),
      natDegree_X_sub_C,distancePolynomial_natDegree]
    omega
  have hlt : (C (if h=1 then s*(t+1) else s*t)*distancePolynomial s t (h-1)).natDegree <
      ((X-C (s*t+s-1))*distancePolynomial s t h).natDegree := by
    have hb := natDegree_C_mul_le (if h=1 then s*(t+1) else s*t) (distancePolynomial s t (h-1))
    rw [hd,distancePolynomial_natDegree] at *
    omega
  exact ⟨hm.sub_of_left (degree_lt_degree hlt),
    (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hd⟩

theorem oddAnnihilator_monic (s t : ℝ) (h : ℕ) (hh : 0<h) :
    (oddAnnihilator h s t).Monic := (oddAnnihilator_monic_natDegree s t h hh).1

theorem oddAnnihilator_natDegree (s t : ℝ) (h : ℕ) (hh : 0<h) :
    (oddAnnihilator h s t).natDegree=h+1 := (oddAnnihilator_monic_natDegree s t h hh).2
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality SimpleGraph.OctagonShortPaths
open scoped BigOperators
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {m h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityOddDecidableEq3 : DecidableEq V := Classical.decEq _

/-- Any collection of point distances within the diameter is independent. -/
theorem distanceMatrix_linearIndependent_of_le (D : Datum G m s t) (hh : 2*h≤m)
    (hs : 0<s) (ht : 0<t) (hp : ∃ r,D.color r=0) :
    LinearIndependent ℝ (fun i : Fin (h+1) => D.distanceMatrix i.val) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  obtain ⟨r,hr⟩ := hp
  obtain ⟨v,hv⟩ := D.exists_distance hs ht r (2*i.val) (by omega)
  have hv' : G.dist r v=2*i.val := by rw [G.dist_comm]; exact hv
  have hcol : D.color v=0 := by
    have hc := distance_color D.connected D.color D.color_adj r v
    have hz : ((2*i.val : ℕ) : ZMod 2)=0 := ZMod.natCast_eq_zero_iff_even.mpr ⟨i.val,by omega⟩
    rw [hr,hv',hz,zero_add] at hc
    exact hc.symm
  let r' : D.Point := ⟨r,hr⟩
  let v' : D.Point := ⟨v,hcol⟩
  have hj (j : Fin (h+1)) : D.distanceMatrix j.val r' v' = if j=i then 1 else 0 := by
    change (if G.dist r v=2*j.val then (1:ℝ) else 0)=_
    rw [hv']
    congr 1
    apply propext
    constructor
    · intro hji
      apply Fin.ext
      omega
    · rintro rfl
      rfl
  have heval := congrArg (fun M : Matrix D.Point D.Point ℝ => M r' v') ha
  simpa [Matrix.sum_apply,Matrix.smul_apply,hj] using heval

/-- The terminal polynomial is the actual minimal polynomial also in odd gonality. -/
theorem odd_minpoly (D : Datum G (2*h+1) s t) (hh : 0<h)
    (hs : 0<s) (ht : 0<t) (hp : ∃ r,D.color r=0) :
    minpoly ℝ (D.distanceMatrix 1) = oddAnnihilator h s t := by
  have hnonzero (p : ℝ[X]) (hp0 : p≠0) (hdeg : p.natDegree≤h) :
      aeval (D.distanceMatrix 1) p≠0 := by
    intro hz
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
      (mem_span_distancePolynomial s t h p hdeg)
    have he := congrArg (aeval (D.distanceMatrix 1)) hc
    simp only [map_sum,map_smul,hz] at he
    simp_rw [D.odd_distancePolynomial_aeval hh _ (Nat.le_of_lt_succ (Fin.isLt _))] at he
    have hcoeff := Fintype.linearIndependent_iff.mp
      (D.distanceMatrix_linearIndependent_of_le (by omega) hs ht hp) _ he
    apply hp0
    rw [←hc]
    simp only [hcoeff,zero_smul,Finset.sum_const_zero]
  symm
  apply minpoly.unique ℝ (D.distanceMatrix 1) (oddAnnihilator_monic s t h hh)
    (D.oddAnnihilator_aeval hh)
  intro q hq hzero
  have hgt : h<q.natDegree := by
    by_contra hsmall
    exact hnonzero q hq.ne_zero (by omega) hzero
  rw [degree_eq_natDegree (oddAnnihilator_monic s t h hh).ne_zero,
    degree_eq_natDegree hq.ne_zero,oddAnnihilator_natDegree s t h hh]
  exact_mod_cast Nat.succ_le_of_lt hgt

/-- Odd spectral information without transporting the datum to a new index. -/
theorem odd_minpoly_of_eq (D : Datum G m s t) (he : m=2*h+1) (hh : 0<h)
    (hs : 0<s) (ht : 0<t) (hp : ∃ r,D.color r=0) :
    minpoly ℝ (D.distanceMatrix 1) = oddAnnihilator h s t := by
  subst m
  exact D.odd_minpoly hh hs ht hp
end SimpleGraph.PolygonParameters.Datum
