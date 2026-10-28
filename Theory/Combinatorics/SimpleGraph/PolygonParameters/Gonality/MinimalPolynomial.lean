module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Even
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Geodesics
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.Even
import all Theory.Combinatorics.SimpleGraph.PolygonParameters.DistanceMatrices
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# The actual point-adjacency minimal polynomial

Every distance occurs, so the point distance matrices are linearly independent.
The monic distance polynomials form a basis by degree. Evaluating a polynomial
of degree at most `h` in that basis shows that it cannot annihilate adjacency
unless it is zero. Consequently the terminal recurrence polynomial of degree
`h+1` is the minimal polynomial for gonality `2*h`.

This completes the even minimal-polynomial step needed by the Feit--Higman
finite-polygon argument cited in Fong--Seitz I (1J), printed p.6. The
multiplicity and integrality restrictions on `h` remain separate arguments.
The two internal imports are deliberate: this proof uses the defining
polynomial recurrence and the entries of the existing distance matrices.
-/

public noncomputable section
namespace SimpleGraph.PolygonParameters.Gonality
open Polynomial
private theorem distancePolynomial_monic_natDegree (s t : ℝ) (k : ℕ) :
    (distancePolynomial s t k).Monic ∧ (distancePolynomial s t k).natDegree = k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [distancePolynomial]
  | one => exact ⟨monic_X, natDegree_X⟩
  | more k ih₀ ih₁ =>
    rw [distancePolynomial]
    have hm := (monic_X_sub_C (s-1)).mul ih₁.1
    have hd : ((X-C (s-1))*distancePolynomial s t (k+1)).natDegree=k+2 := by
      rw [(monic_X_sub_C (s-1)).natDegree_mul ih₁.1, natDegree_X_sub_C, ih₁.2]
      omega
    have hlt : (C (if k=0 then s*(t+1) else s*t)*distancePolynomial s t k).natDegree <
        ((X-C (s-1))*distancePolynomial s t (k+1)).natDegree := by
      have hb := natDegree_C_mul_le (if k=0 then s*(t+1) else s*t) (distancePolynomial s t k)
      rw [hd, ih₀.2] at *
      omega
    exact ⟨hm.sub_of_left (degree_lt_degree hlt),
      (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hd⟩

theorem distancePolynomial_monic (s t : ℝ) (k : ℕ) :
    (distancePolynomial s t k).Monic := (distancePolynomial_monic_natDegree s t k).1

theorem distancePolynomial_natDegree (s t : ℝ) (k : ℕ) :
    (distancePolynomial s t k).natDegree = k := (distancePolynomial_monic_natDegree s t k).2

private def distanceSequence (s t : ℝ) : Polynomial.Sequence ℝ where
  elems' := distancePolynomial s t
  degree_eq' k := by
    rw [degree_eq_natDegree (distancePolynomial_monic s t k).ne_zero, distancePolynomial_natDegree]

/-- Distance polynomials span all polynomials up to their last degree. -/
theorem mem_span_distancePolynomial (s t : ℝ) (h : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ h) :
    p ∈ Submodule.span ℝ (Set.range (fun i : Fin (h+1) => distancePolynomial s t i.val)) := by
  have he : Set.range (fun i : Fin (h+1) => distancePolynomial s t i.val) =
      distanceSequence s t '' Set.Iic h := by
    ext q
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val, by simpa using Nat.le_of_lt_succ i.isLt, rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,by simpa using Nat.lt_succ_of_le hi⟩,rfl⟩
  rw [he, (distanceSequence s t).span_degreeLE]
  · exact Polynomial.mem_degreeLE.mpr ((Polynomial.degree_le_natDegree).trans (by exact_mod_cast hp))
  · intro i _
    change IsUnit (distancePolynomial s t i).leadingCoeff
    rw [distancePolynomial_monic s t i]
    exact isUnit_one
end SimpleGraph.PolygonParameters.Gonality

namespace SimpleGraph.PolygonParameters.Datum
open Polynomial Gonality SimpleGraph.OctagonShortPaths
open scoped BigOperators
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {h s t : ℕ}
attribute [local instance] Classical.propDecidable
local instance gonalityMinimalPolynomialDecidableEq : DecidableEq V := Classical.decEq _

/-- Nonempty distance spheres make the point distance matrices independent. -/
theorem even_distanceMatrix_linearIndependent (D : Datum G (2*h) s t)
    (hs : 0<s) (ht : 0<t) (hp : ∃ r, D.color r=0) :
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
  simpa [Matrix.sum_apply, Matrix.smul_apply, hj] using heval

/-- A nonzero polynomial of degree at most half the gonality cannot annihilate
point adjacency. This supplies the lower bound for its minimal polynomial. -/
theorem even_aeval_ne_zero (D : Datum G (2*h) s t) (hh : 2≤h)
    (hs : 0<s) (ht : 0<t) (hp : ∃ r, D.color r=0)
    (p : ℝ[X]) (hp0 : p≠0) (hdeg : p.natDegree≤h) :
    aeval (D.distanceMatrix 1) p ≠ 0 := by
  intro hz
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (mem_span_distancePolynomial s t h p hdeg)
  have he := congrArg (aeval (D.distanceMatrix 1)) hc
  simp only [map_sum, map_smul, hz] at he
  simp_rw [D.even_distancePolynomial_aeval hh _ (Nat.le_of_lt_succ (Fin.isLt _)), smul_smul] at he
  have hcoeff := Fintype.linearIndependent_iff.mp (D.even_distanceMatrix_linearIndependent hs ht hp) _ he
  have hc0 (i : Fin (h+1)) : c i=0 := by
    have hi := hcoeff i
    have hn : (if i.val=h then (t:ℝ)+1 else 1)≠0 := by split_ifs <;> positivity
    exact (mul_eq_zero.mp hi).resolve_right hn
  apply hp0
  rw [←hc]
  simp only [hc0, zero_smul, Finset.sum_const_zero]

/-- The annihilator obtained from the geometry is the actual minimal polynomial. -/
theorem even_minpoly (D : Datum G (2*h) s t) (hh : 2≤h)
    (hs : 0<s) (ht : 0<t) (hp : ∃ r, D.color r=0) :
    minpoly ℝ (D.distanceMatrix 1) = evenAnnihilator h s t := by
  symm
  apply minpoly.unique ℝ (D.distanceMatrix 1) (evenAnnihilator_monic s t h hh)
    (D.evenAnnihilator_aeval hh)
  intro q hq hzero
  have hgt : h<q.natDegree := by
    by_contra hsmall
    exact D.even_aeval_ne_zero hh hs ht hp q hq.ne_zero (by omega) hzero
  rw [degree_eq_natDegree (evenAnnihilator_monic s t h hh).ne_zero,
    degree_eq_natDegree hq.ne_zero, evenAnnihilator_natDegree s t h hh]
  exact_mod_cast Nat.succ_le_of_lt hgt

/-- The same minimal-polynomial statement without changing the datum's index. -/
theorem even_minpoly_of_eq {m : ℕ} (D : Datum G m s t) (he : m=2*h) (hh : 2≤h)
    (hs : 0<s) (ht : 0<t) (hp : ∃ r, D.color r=0) :
    minpoly ℝ (D.distanceMatrix 1) = evenAnnihilator h s t := by
  subst m
  exact D.even_minpoly hh hs ht hp
end SimpleGraph.PolygonParameters.Datum
