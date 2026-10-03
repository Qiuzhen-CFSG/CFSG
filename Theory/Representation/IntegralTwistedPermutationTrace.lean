module

public import Theory.Representation.IntegralPermutationTrace
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Integral permutation traces with a commuting weight

Let a permutation of two-power order commute with an integral idempotent and
with a finite-order operator. If the coefficient ring and its characteristic-two
residue field contain compatible primitive roots for the order of that operator,
the trace against the permutation and the operator equals the corresponding
weighted trace on any compatible fixed-index lifts.

Differences of distinct eigenvalues reduce to nonzero elements, hence are units.
Bezout's identity for the resulting coprime linear factors gives integral
polynomials with Kronecker-delta values on the eigenvalues. Evaluating them yields
idempotent spectral projectors and reconstructs the operator as their weighted
sum. Reduction followed by fixed-index restriction respects this construction.
Apply `Matrix.trace_permMatrix_mul_eq_trace_fixed_lift` to each projector times
the original idempotent, then take the weighted sum.

Source: the spectral-projector extension of the Brauer--Suzuki trace argument
used in Fong, *Some Sylow subgroups of order 32 and a characterization of U(3,3)*,
J. Algebra 6 (1967), p. 71, equation (6). The polynomial construction uses
Mathlib's finite coprime Bezout identity.
-/

public section

open Polynomial
open scoped BigOperators
noncomputable section

namespace Matrix
variable {R k X : Type*} [CommRing R] [Field k]
  [Fintype X] [DecidableEq X]

private theorem prod_linear_powers [IsDomain R] {m : ℕ} (hm : 0 < m)
    {ζ : R} (hζ : IsPrimitiveRoot ζ m) :
    (∏ i : Fin m, (Polynomial.X - C (ζ ^ i.val))) = (Polynomial.X : R[X]) ^ m - 1 := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  rw [Polynomial.X_pow_sub_one_eq_prod hm hζ]
  apply Finset.prod_bij (fun i _ => ζ ^ (i : Fin m).val)
  · intro i _
    rw [Polynomial.mem_nthRootsFinset hm]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · intro i _ j _ hij
    exact Fin.ext (hζ.pow_inj i.isLt j.isLt hij)
  · intro x hx
    obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hm 1).mp hx)
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, he⟩
  · intro i _
    rfl

private theorem exists_delta_polynomials {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (v : I → R) (hv : Pairwise (fun i j => IsUnit (v i - v j))) :
    ∃ p : I → R[X], ∀ i j, (p i).eval (v j) = if i = j then 1 else 0 := by
  classical
  have hc : Pairwise (fun i j => IsCoprime (Polynomial.X - C (v i)) (Polynomial.X - C (v j))) :=
    fun i j hij => Polynomial.isCoprime_X_sub_C_of_isUnit_sub (hv hij)
  obtain ⟨a, ha⟩ := exists_sum_eq_one_iff_pairwise_coprime'.mpr hc
  let p (i : I) : R[X] := a i * ∏ j ∈ ({i} : Finset I)ᶜ, (Polynomial.X - C (v j))
  have hsum : ∑ i, p i = 1 := ha
  have hzero (i j : I) (hij : i ≠ j) : (p i).eval (v j) = 0 := by
    dsimp [p]
    rw [eval_mul, eval_prod]
    have hz : (∏ x ∈ ({i} : Finset I)ᶜ, eval (v j) (Polynomial.X - C (v x))) = 0 :=
      Finset.prod_eq_zero (by simpa using hij.symm) (by simp)
    rw [hz, mul_zero]
  refine ⟨p, fun i j => ?_⟩
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hh := congrArg (Polynomial.eval (v i)) hsum
    rw [eval_finsetSum, eval_one] at hh
    rw [Finset.sum_eq_single i (fun j _ hji => hzero j i hji) (by simp)] at hh
    exact hh
  · simpa [hij] using hzero i j hij

private theorem aeval_eq_zero_of_eval_roots {I A : Type*} [Fintype I]
    [Ring A] [Algebra R A] (v : I → R)
    (hv : Pairwise (fun i j => IsUnit (v i - v j)))
    (T : A) (hT : aeval T (∏ i, (Polynomial.X - C (v i))) = 0)
    (p : R[X]) (hp : ∀ i, p.eval (v i) = 0) : aeval T p = 0 := by
  have hd : (∏ i, (Polynomial.X - C (v i))) ∣ p :=
    Fintype.prod_dvd_of_coprime
      (fun i j hij => Polynomial.isCoprime_X_sub_C_of_isUnit_sub (hv hij))
      (fun i => Polynomial.dvd_iff_isRoot.mpr (hp i))
  obtain ⟨q, rfl⟩ := hd
  rw [map_mul, hT, zero_mul]

private theorem commute_aeval {A : Type*} [Ring A] [Algebra R A]
    {T U : A} (h : Commute T U) (p : R[X]) : Commute (aeval T p) U := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add_left hq
  | monomial n r =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left r U).mul_left (h.pow_left n)

private theorem idempotent_mul_of_commute {A : Type*} [Monoid A]
    {P Q : A} (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (h : Commute P Q) : IsIdempotentElem (P * Q) := by
  change (P * Q) * (P * Q) = P * Q
  rw [h.symm.mul_mul_mul_comm, hP.eq, hQ.eq]


private theorem map_aeval_fixed [CharP k 2] (f : R →+* k)
    (σ : Equiv.Perm X) {n : ℕ} (hσ : σ ^ (2 ^ n) = 1)
    (T : Matrix X X R) (hT : Commute (σ.permMatrix R) T)
    (T₀ : Matrix {x // σ x = x} {x // σ x = x} R)
    (hmap : f.mapMatrix T₀ = (f.mapMatrix T).submatrix Subtype.val Subtype.val)
    (p : R[X]) :
    f.mapMatrix (aeval T₀ p) =
      (f.mapMatrix (aeval T p)).submatrix Subtype.val Subtype.val := by
  have hTk : Commute (σ.permMatrix k) (f.mapMatrix T) := by
    simpa only [RingHom.mapMatrix_apply, PEquiv.map_toMatrix] using hT.map f.mapMatrix
  have hpow (a : ℕ) :
      (f.mapMatrix (T ^ a)).submatrix Subtype.val Subtype.val = f.mapMatrix (T₀ ^ a) := by
    simp only [map_pow]
    induction a with
    | zero => simp only [pow_zero, submatrix_one _ Subtype.val_injective]
    | succ a ih =>
      rw [pow_succ, pow_succ,
        submatrix_fixed_mul σ hσ _ _ (hTk.pow_right a) hTk, ih, ← hmap]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, submatrix_add, Pi.add_apply] using congrArg₂ (· + ·) hp hq
  | monomial a r =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    ext i j
    change f (r * (T₀ ^ a) i j) = f (r * (T ^ a) i.val j.val)
    rw [map_mul, map_mul]
    congr 1
    exact congrArg (fun M => M i j) (hpow a).symm


private theorem spectral_evaluation {I A : Type*} [Fintype I] [DecidableEq I]
    [Ring A] [Algebra R A] (v : I → R)
    (hv : Pairwise (fun i j => IsUnit (v i - v j)))
    (p : I → R[X]) (hp : ∀ i j, (p i).eval (v j) = if i = j then 1 else 0)
    (T : A) (hT : aeval T (∏ i, (Polynomial.X - C (v i))) = 0) :
    (∀ i, IsIdempotentElem (aeval T (p i))) ∧
      (∑ i, v i • aeval T (p i)) = T := by
  constructor
  · intro i
    have hh := aeval_eq_zero_of_eval_roots v hv T hT (p i * p i - p i) (by
      intro j
      simp only [eval_sub, eval_mul, hp]
      split_ifs <;> simp)
    simpa only [map_sub, map_mul, sub_eq_zero, IsIdempotentElem] using hh
  · have hh := aeval_eq_zero_of_eval_roots v hv T hT
        ((∑ i, C (v i) * p i) - Polynomial.X) (by
          intro j
          simp [eval_finsetSum, hp])
    simpa only [map_sub, map_sum, map_mul, aeval_C, aeval_X,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sub_eq_zero] using hh

/-- Integral fixed-point trace comparison with a commuting finite-order weight.

The local operator and idempotent need only lift the fixed-index restrictions
of the corresponding residue matrices. The primitive-root hypothesis on the
residue ensures that distinct eigenvalues have unit differences. In particular,
no completeness or Henselian assumption is required. The usual invertibility
hypothesis on the order is retained in the interface, though the proof only
needs the stronger separation supplied by the primitive residue root. -/
theorem trace_permMatrix_mul_mul_eq_trace_fixed_lift [IsDomain R] [CharP k 2]
    (f : R →+* k) (hsurj : Function.Surjective f)
    (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (σ : Equiv.Perm X) {n : ℕ} (hσ : σ ^ (2 ^ n) = 1)
    (P T : Matrix X X R) (hP : IsIdempotentElem P)
    (hσP : Commute (σ.permMatrix R) P) (hσT : Commute (σ.permMatrix R) T)
    (hTP : Commute T P)
    (B T₀ : Matrix {x // σ x = x} {x // σ x = x} R)
    (hB : IsIdempotentElem B) (hT₀B : Commute T₀ B)
    (hBmap : f.mapMatrix B = (f.mapMatrix P).submatrix Subtype.val Subtype.val)
    (hTmap : f.mapMatrix T₀ = (f.mapMatrix T).submatrix Subtype.val Subtype.val)
    {m : ℕ} (hm : 0 < m) (hTm : T ^ m = 1) (hT₀m : T₀ ^ m = 1)
    (_hm_unit : IsUnit (m : R)) {ζ : R}
    (hζ : IsPrimitiveRoot ζ m) (hζk : IsPrimitiveRoot (f ζ) m) :
    trace (σ.permMatrix R * T * P) = trace (T₀ * B) := by
  classical
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  let v (i : Fin m) : R := ζ ^ i.val
  have hv : Pairwise (fun i j => IsUnit (v i - v j)) := by
    intro i j hij
    apply hf
    simp only [map_sub, v, map_pow]
    exact sub_ne_zero.mpr (fun hh => hij (Fin.ext (hζk.pow_inj i.isLt j.isLt hh)))
  obtain ⟨p, hp⟩ := exists_delta_polynomials v hv
  have hprod : (∏ i : Fin m, (Polynomial.X - C (v i))) = (Polynomial.X : R[X]) ^ m - 1 :=
    prod_linear_powers hm hζ
  obtain ⟨hE, hsumE⟩ := spectral_evaluation v hv p hp T (by rw [hprod]; simp [hTm])
  obtain ⟨hE₀, hsumE₀⟩ := spectral_evaluation v hv p hp T₀ (by rw [hprod]; simp [hT₀m])
  have htr (i : Fin m) :
      trace (σ.permMatrix R * (aeval T (p i) * P)) = trace (aeval T₀ (p i) * B) := by
    have hσE : Commute (σ.permMatrix R) (aeval T (p i)) :=
      (commute_aeval hσT.symm (p i)).symm
    apply trace_permMatrix_mul_eq_trace_fixed_lift f hsurj hf σ hσ
      (aeval T (p i) * P)
      (idempotent_mul_of_commute (hE i) hP (commute_aeval hTP (p i)))
      (hσE.mul_right hσP) (aeval T₀ (p i) * B)
      (idempotent_mul_of_commute (hE₀ i) hB (commute_aeval hT₀B (p i)))
    rw [map_mul, map_mul, map_aeval_fixed f σ hσ T hσT T₀ hTmap, hBmap]
    symm
    apply submatrix_fixed_mul σ hσ
    · simpa only [RingHom.mapMatrix_apply, PEquiv.map_toMatrix] using hσE.map f.mapMatrix
    · simpa only [RingHom.mapMatrix_apply, PEquiv.map_toMatrix] using hσP.map f.mapMatrix
  calc
    trace (σ.permMatrix R * T * P) =
        trace (σ.permMatrix R * (∑ i, v i • aeval T (p i)) * P) := by rw [hsumE]
    _ = ∑ i, v i * trace (σ.permMatrix R * (aeval T (p i) * P)) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, trace_sum,
        trace_smul, smul_eq_mul, mul_assoc]
    _ = ∑ i, v i * trace (aeval T₀ (p i) * B) := by simp_rw [htr]
    _ = trace ((∑ i, v i • aeval T₀ (p i)) * B) := by
      simp only [Finset.sum_mul, smul_mul_assoc, trace_sum, trace_smul, smul_eq_mul]
    _ = trace (T₀ * B) := by rw [hsumE₀]

end Matrix
