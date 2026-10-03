module

public import Theory.Representation.IntegralSpectralTrace

/-!
# Comparing integral projectors on fixed indices

Two commuting integral idempotents with equal reductions on the fixed indices
of a two-power permutation have equal twisted traces. The twist may be any
commuting finite-order operator whose order is a unit and whose eigenvalues
split in the coefficient domain. Apply integral spectral projectors to the
two mismatched summands; their fixed-index reductions vanish.

This is the projector-product form of the Brauer--Suzuki permutation-summand
trace argument, used for associated-block support in ABG III.5–6.
-/

public section
noncomputable section
open scoped BigOperators

namespace Matrix

variable {R k X : Type*} [CommRing R] [IsDomain R] [Field k] [CharP k 2]
  [Fintype X] [DecidableEq X]

/-- Vanishing of the fixed-index residue suffices for twisted trace vanishing;
the permutation need not be fixed-point-free. -/
theorem trace_permMatrix_mul_mul_eq_zero_of_fixed_reduction_eq_zero
    (f : R →+* k) (hsurj : Function.Surjective f)
    (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (σ : Equiv.Perm X) {a : ℕ} (hσ : σ ^ (2 ^ a) = 1)
    (U P : Matrix X X R) (hP : IsIdempotentElem P)
    (hTP : Commute (σ.permMatrix R) P) (hUP : Commute U P)
    (hTU : Commute (σ.permMatrix R) U)
    (hfix : (f.mapMatrix P).submatrix
      (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) = 0)
    {n : ℕ} (hn : n ≠ 0) (hU : U ^ n = 1)
    (hnunit : IsUnit (n : R)) (ζ : R) (hζ : IsPrimitiveRoot ζ n) :
    trace (σ.permMatrix R * U * P) = 0 := by
  classical
  let root : Rˣ := (hζ.isUnit hn).unit
  have hroot : IsPrimitiveRoot (root : R) n := by
    simpa only [root, IsUnit.unit_spec] using hζ
  let c : R := ↑(hnunit.unit⁻¹)
  have hc : c * n = 1 := by
    rw [← hnunit.unit_spec]
    exact Units.inv_mul hnunit.unit
  obtain ⟨E, hE, hsum, hUE, hcomm⟩ :=
    IntegralSpectral.exists_projectors hn root hroot c hc U hU
  have hmap (A : Matrix X X R) (hA : Commute (σ.permMatrix R) A) :
      Commute (σ.permMatrix k) (f.mapMatrix A) := by
    simpa only [RingHom.mapMatrix_apply, PEquiv.map_toMatrix] using hA.map f.mapMatrix
  have hzero (j : Fin n) : trace (σ.permMatrix R * (E j * P)) = 0 := by
    have hi : IsIdempotentElem (E j * P) :=
      IsIdempotentElem.mul_of_commute (hcomm P hUP.symm j).symm (hE j) hP
    have ht : Commute (σ.permMatrix R) (E j * P) :=
      (hcomm _ hTU j).mul_right hTP
    have hh := trace_permMatrix_mul_eq_trace_fixed_lift f hsurj hf σ hσ
      (E j * P) hi ht (0 : Matrix {x // σ x = x} {x // σ x = x} R)
      (by simp [IsIdempotentElem]) (by
        rw [map_zero, map_mul,
          submatrix_fixed_mul σ hσ _ _ (hmap _ (hcomm _ hTU j)) (hmap _ hTP),
          hfix, mul_zero])
    simpa only [trace_zero] using hh
  calc
    trace (σ.permMatrix R * U * P) =
        ∑ j, trace (σ.permMatrix R * (U * E j) * P) := by
      rw [← trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum,
        hsum, mul_one]
    _ = ∑ j : Fin n, ((↑(root⁻¹) : R) ^ (j : ℕ)) •
        trace (σ.permMatrix R * (E j * P)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hUE, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, trace_smul, mul_assoc]
    _ = 0 := by simp only [hzero, smul_zero, Finset.sum_const_zero]

/-- Equal fixed-index residues of commuting projectors give equal twisted
integral traces, without choosing an integral lift on the fixed indices. -/
theorem trace_permMatrix_mul_mul_eq_of_fixed_reduction_eq
    (f : R →+* k) (hsurj : Function.Surjective f)
    (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (σ : Equiv.Perm X) {a : ℕ} (hσ : σ ^ (2 ^ a) = 1)
    (U P Q : Matrix X X R) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPQ : Commute P Q)
    (hTP : Commute (σ.permMatrix R) P) (hTQ : Commute (σ.permMatrix R) Q)
    (hUP : Commute U P) (hUQ : Commute U Q)
    (hTU : Commute (σ.permMatrix R) U)
    (hfix : (f.mapMatrix P).submatrix
      (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) =
      (f.mapMatrix Q).submatrix (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val))
    {n : ℕ} (hn : n ≠ 0) (hU : U ^ n = 1)
    (hnunit : IsUnit (n : R)) (ζ : R) (hζ : IsPrimitiveRoot ζ n) :
    trace (σ.permMatrix R * U * P) = trace (σ.permMatrix R * U * Q) := by
  have hzero (A B : Matrix X X R) (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
      (hAB : Commute A B) (hTA : Commute (σ.permMatrix R) A)
      (hTB : Commute (σ.permMatrix R) B) (hUA : Commute U A) (hUB : Commute U B)
      (hab : (f.mapMatrix A).submatrix
          (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) =
        (f.mapMatrix B).submatrix (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val)) :
      trace (σ.permMatrix R * U * (A * (1 - B))) = 0 := by
    apply trace_permMatrix_mul_mul_eq_zero_of_fixed_reduction_eq_zero
      f hsurj hf σ hσ U (A * (1 - B))
      (IsIdempotentElem.mul_of_commute ((Commute.one_right A).sub_right hAB) hA hB.one_sub)
      (hTA.mul_right ((Commute.one_right _).sub_right hTB))
      (hUA.mul_right ((Commute.one_right _).sub_right hUB)) hTU _ hn hU hnunit ζ hζ
    have hmap (M : Matrix X X R) (hM : Commute (σ.permMatrix R) M) :
        Commute (σ.permMatrix k) (f.mapMatrix M) := by
      simpa only [RingHom.mapMatrix_apply, PEquiv.map_toMatrix] using hM.map f.mapMatrix
    have hBB : (f.mapMatrix B).submatrix
        (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) *
        (f.mapMatrix B).submatrix (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) =
        (f.mapMatrix B).submatrix (fun x : {x // σ x = x} => x.val) (fun x : {x // σ x = x} => x.val) := by
      rw [← submatrix_fixed_mul σ hσ _ _ (hmap _ hTB) (hmap _ hTB),
        ← map_mul, hB.eq]
    simp only [mul_sub, mul_one, map_sub, map_mul, submatrix_sub, Pi.sub_apply]
    rw [
      submatrix_fixed_mul σ hσ _ _ (hmap _ hTA) (hmap _ hTB), hab, hBB, sub_self]
  have hp := hzero P Q hP hQ hPQ hTP hTQ hUP hUQ hfix
  have hq := hzero Q P hQ hP hPQ.symm hTQ hTP hUQ hUP hfix.symm
  simp only [mul_sub, mul_one, trace_sub, ← mul_assoc, sub_eq_zero] at hp hq
  rw [hp, hq]
  rw [mul_assoc, hPQ.eq, ← mul_assoc]

end Matrix
