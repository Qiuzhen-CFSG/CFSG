module

public import Mathlib.GroupTheory.OrderOfElement
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.CoordinateDensity
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion

/-!
# Structural criteria for the degree-1792 density certificate

Monomial generator rows forming a rooted, increasing tree realize every
coordinate row in an algebra orbit. A sequential checker verifies those edges
without dense matrix multiplication. Its soundness connects the packed ATLAS
rows to the literal matrix entries.

Separately, an idempotent orthogonal to an algebra element belongs to that
algebra if their sum is a unit in a finite ring: a positive power of the unit
is one, so the idempotent is one minus the same power of the algebra element.
The concrete consumers are `RowOrbit` and `Projector`.

Source application: James, J. Algebra 27 (1973), 57–111, and the ATLAS binary
M24 matrices documented in `../source/README.md`.
-/

@[expose] public section

open Matrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792

def checkTargets : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, t :: ts => (t == 0 || x == 2^t) && checkTargets xs ts
  | _, _ => false

theorem checkTargets_sound (xs ts : List Nat) (h : checkTargets xs ts = true)
    (i : Nat) (hi : i < ts.length) (ht : ts[i]! ≠ 0) : xs[i]! = 2^ts[i]! := by
  induction xs generalizing ts i with
  | nil =>
    cases ts with
    | nil => simp at hi
    | cons t ts => simp [checkTargets] at h
  | cons x xs ih =>
    cases ts with
    | nil => simp at hi
    | cons t ts =>
      simp only [checkTargets, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      cases i with
      | zero => simpa using h.1.resolve_left (by simpa using ht)
      | succ i =>
        simpa using ih ts h.2 i (by simpa using hi) (by simpa using ht)

theorem row_of_target (n : Nat) (xs ts : Array Nat)
    (h : checkTargets xs.toList ts.toList = true) (hts : ts.size = n)
    (i j : Fin n) (hj : ts[i.val]! = j.val) (hne : j.val ≠ 0) :
    Thompson.BinaryMatrix.decode n xs i = Pi.single j 1 := by
  have lookup (a : Array Nat) (i : Nat) : a.toList[i]! = a[i]! := by
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  have ht : ts.toList[i.val]! = j.val := by simpa only [lookup] using hj
  have hr := checkTargets_sound xs.toList ts.toList h i.val
    (by simpa only [Array.length_toList, hts] using i.isLt) (ht ▸ hne)
  have hr' : xs[i.val]! = 2^j.val := by simpa only [ht, lookup] using hr
  funext l
  simp [Thompson.BinaryMatrix.decode, hr', Thompson.BinaryMatrix.bit,
    Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]

theorem row_realizations {k : Type*} [Field k] (n : Nat)
    (Q : Subalgebra k (Matrix (Fin (n+1)) (Fin (n+1)) k))
    (A B : Matrix (Fin (n+1)) (Fin (n+1)) k)
    (hA : A ∈ Q) (hB : B ∈ Q)
    (p : Fin n → Fin (n+1)) (actor : Fin n → Bool)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, (if actor i then A else B) (p i) = Pi.single i.succ 1) :
    ∀ i : Fin (n+1), ∃ R ∈ Q, vecMul (Pi.single 0 1) R = Pi.single i 1 := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, vecMul_one _⟩
    | succ i =>
      obtain ⟨R, hR, he⟩ := ih (p i) (hp i)
      refine ⟨R * (if actor i then A else B), Q.mul_mem hR ?_, ?_⟩
      · split <;> assumption
      · rw [← vecMul_vecMul, he, single_one_vecMul]
        exact hs i

theorem row_span {k n : Type*} [Field k] [Fintype n] [DecidableEq n]
    (Q : Subalgebra k (Matrix n n k)) (v : n → k)
    (h : ∀ i, ∃ R ∈ Q, vecMul v R = Pi.single i 1) :
    Submodule.span k (Set.range (fun R : Q => vecMul v R.val)) = ⊤ := by
  apply top_unique
  intro x _
  rw [show x = ∑ i, x i • Pi.single i 1 by
    ext j
    simp [Pi.single_apply]]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  obtain ⟨R,hR,he⟩ := h i
  exact Submodule.subset_span ⟨⟨R,hR⟩,he⟩
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792

/-- A finite-order unit on the complementary summand realizes the projector as
one minus a positive power of the singular operator. -/
theorem projector_mem {k R : Type*} [Field k] [Ring R] [Algebra k R] [Finite R]
    (Q : Subalgebra k R) (S P : R) (hS : S ∈ Q)
    (hSP : S * P = 0) (hPS : P * S = 0) (hP : P * P = P)
    (hunit : IsUnit (S + P)) : P ∈ Q := by
  have hpow (j : Nat) : (S + P)^(j+1) = S^(j+1) + P := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ih, add_mul, mul_add, mul_add, hPS, hP]
      have hz : S^(j+1) * P = 0 := by rw [pow_succ, mul_assoc, hSP, mul_zero]
      rw [hz, add_zero, zero_add, ← pow_succ]
  obtain ⟨j, hj, he⟩ := hunit.isOfFinOrder.exists_pow_eq_one
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hsum : S^(j+1) + P = 1 := (hpow j).symm.trans he
  have hP' : P = 1 - S^(j+1) := by rw [← hsum]; abel
  rw [hP']
  exact Q.sub_mem Q.one_mem (Q.pow_mem hS _)
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
open Matrix

def edgesFrom : Nat → List Nat → List Nat → List (Nat × Nat)
  | p, a :: as, b :: bs => (p,a) :: (p,b) :: edgesFrom (p+1) as bs
  | _, _, _ => []

def checkEdges (n : Nat) : Nat → List (Nat × Nat) → Bool
  | c, [] => c == n
  | c, (p,t) :: es =>
    if t = 0 then checkEdges n c es
    else (t == c && decide (p < c)) && checkEdges n (c+1) es

theorem checkEdges_sound (n c : Nat) (es : List (Nat × Nat))
    (h : checkEdges n c es = true) (j : Nat) (hc : c ≤ j) (hj : j < n) :
    ∃ p, p < j ∧ (p,j) ∈ es := by
  induction es generalizing c with
  | nil => simp only [checkEdges, beq_iff_eq] at h; omega
  | cons e es ih =>
    obtain ⟨p,t⟩ := e
    by_cases ht : t = 0
    · simp only [checkEdges, ht, ↓reduceIte] at h
      obtain ⟨q,hq,he⟩ := ih c h hc
      exact ⟨q,hq,List.mem_cons_of_mem _ he⟩
    · simp only [checkEdges, ht, ↓reduceIte, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq] at h
      by_cases hjc : j = c
      · refine ⟨p, ?_, ?_⟩
        · simpa only [hjc] using h.1.2
        · simp [hjc, h.1.1]
      · obtain ⟨q,hq,he⟩ := ih (c+1) h.2 (by omega)
        exact ⟨q,hq,List.mem_cons_of_mem _ he⟩

theorem edgesFrom_sound (p : Nat) (as bs : List Nat) (q j : Nat)
    (h : (q,j) ∈ edgesFrom p as bs) :
    ∃ i, i < as.length ∧ i < bs.length ∧ p+i=q ∧ (as[i]! = j ∨ bs[i]! = j) := by
  induction as generalizing bs p with
  | nil => simp [edgesFrom] at h
  | cons a as ih =>
    cases bs with
    | nil => simp [edgesFrom] at h
    | cons b bs =>
      simp only [edgesFrom, List.mem_cons] at h
      rcases h with h | h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨0, by simp, by simp, by simp, Or.inl (by simp)⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨0, by simp, by simp, by simp, Or.inr (by simp)⟩
      · obtain ⟨i,ha,hb,hp,ht⟩ := ih (p+1) bs h
        refine ⟨i+1, by simpa using ha, by simpa using hb, by omega, ?_⟩
        simpa using ht

theorem row_realizations_of_predecessor {k : Type*} [Field k] (n : Nat)
    (Q : Subalgebra k (Matrix (Fin (n+1)) (Fin (n+1)) k))
    (A B : Matrix (Fin (n+1)) (Fin (n+1)) k)
    (hA : A ∈ Q) (hB : B ∈ Q)
    (hs : ∀ i : Fin (n+1), i ≠ 0 → ∃ p, p < i ∧
      (A p = Pi.single i 1 ∨ B p = Pi.single i 1)) :
    ∀ i : Fin (n+1), ∃ R ∈ Q, vecMul (Pi.single 0 1) R = Pi.single i 1 := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i = 0
    · subst i
      exact ⟨1, Q.one_mem, vecMul_one _⟩
    · obtain ⟨p,hp,hs⟩ := hs i hi
      obtain ⟨R,hR,he⟩ := ih p hp
      rcases hs with ha | hb
      · refine ⟨R*A,Q.mul_mem hR hA,?_⟩
        rw [← vecMul_vecMul, he, single_one_vecMul]
        exact ha
      · refine ⟨R*B,Q.mul_mem hR hB,?_⟩
        rw [← vecMul_vecMul, he, single_one_vecMul]
        exact hb
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
