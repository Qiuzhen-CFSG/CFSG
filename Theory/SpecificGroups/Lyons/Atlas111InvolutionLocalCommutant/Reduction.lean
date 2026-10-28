module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCenterReduction

/-!
# Cyclic-vector reconstruction for the Lyons local commutant

The binary word tree gives a cyclic matrix Q. A polynomial R in its two
generators annihilates the seed vector. Every matrix commuting with the
generators commutes with R, so its seed column belongs to the kernel of R.
A two-dimensional kernel certificate and a right inverse for Q then determine
the entire commuting matrix. All numerical premises remain explicit here.

The word enumeration and index 55 come from the saved certificate search for
the literal ATLAS program `LyG1-max4W1`; source attribution is retained in
`../Atlas111InvolutionSource/` and `../Atlas111Source/`.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant
open Matrix
open scoped BigOperators


variable {n : ℕ} [NeZero n] {K : Type*} [CommRing K]

public abbrev LocalVector (n : ℕ) (K : Type*) := Fin n → K

@[expose] public def localSeed : LocalVector n K := Pi.single 0 1

@[expose] public def localWord {G : Type*} [Monoid G] (A B : G) : ℕ → G
  | 0 => 1
  | n + 1 => (if n % 2 = 0 then A
      else B) * localWord A B (n / 2)
termination_by n => n

public theorem localWord_commutes {G : Type*} [Monoid G] (A B M : G)
    (ha : Commute M A)
    (hb : Commute M B) (n : ℕ) :
    Commute M (localWord A B n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [localWord]; exact Commute.one_right M
    | succ n =>
      rw [localWord]
      apply Commute.mul_right _ (ih (n / 2) (by omega))
      split_ifs
      · exact ha
      · exact hb

@[expose] public def localCyclicMatrix (A B : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  fun i j => (localWord A B j.val *ᵥ (localSeed (n := n) (K := K))) i

@[expose] public def localAnnihilator (A B : Matrix (Fin n) (Fin n) K) (q : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  A * localWord A B 55 -
    ∑ j : Fin n, q j • localWord A B j.val

omit [NeZero n] in
public theorem localAnnihilator_commutes (A B M : Matrix (Fin n) (Fin n) K)
    (ha : Commute M A)
    (hb : Commute M B) (q : Fin n → K) :
    Commute M (localAnnihilator A B q) := by
  change M * (_ - _) = (_ - _) * M
  rw [mul_sub, sub_mul]
  apply congrArg₂ (· - ·)
  · exact (ha.mul_right (localWord_commutes A B M ha hb 55)).eq
  · rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_smul, Matrix.smul_mul, (localWord_commutes A B M ha hb j.val).eq]

@[expose] public def LocalCyclicCertificate (A B T : Matrix (Fin n) (Fin n) K) : Prop :=
  (∃ D : Matrix (Fin n) (Fin n) K, localCyclicMatrix A B * D = 1) ∧
  ∀ j : Fin n, localWord A B j.val *ᵥ
    (T *ᵥ (localSeed (n := n) (K := K))) =
    T *ᵥ (localWord A B j.val *ᵥ (localSeed (n := n) (K := K)))

@[expose] public def LocalKernelCertificate (A B T : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ q : Fin n → K,
    localAnnihilator A B q *ᵥ (localSeed (n := n) (K := K)) = 0 ∧
    ∀ x : LocalVector n K, localAnnihilator A B q *ᵥ x = 0 →
      ∃ u v : K, x = u • (localSeed (n := n) (K := K)) +
        v • (T *ᵥ (localSeed (n := n) (K := K)))

public theorem commutant_of_cyclic_kernel (A B T : Matrix (Fin n) (Fin n) K)
    (hc : LocalCyclicCertificate A B T) (hk : LocalKernelCertificate A B T) :
    ∀ M : Matrix (Fin n) (Fin n) K, Commute M A → Commute M B →
      ∃ u v : K, M = u • (1 : Matrix (Fin n) (Fin n) K) + v • T := by
  intro M ha hb
  rcases hc with ⟨⟨D, hD⟩, hT⟩
  rcases hk with ⟨q, hq, hker⟩
  have hmR := (localAnnihilator_commutes A B M ha hb q).eq
  have hzero : localAnnihilator A B q *ᵥ (M *ᵥ (localSeed (n := n) (K := K))) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hmR, ← Matrix.mulVec_mulVec, hq, Matrix.mulVec_zero]
  obtain ⟨u, v, huv⟩ := hker _ hzero
  refine ⟨u, v, ?_⟩
  have hcol (j : Fin n) :
      M *ᵥ (localWord A B j.val *ᵥ (localSeed (n := n) (K := K))) =
      (u • (1 : Matrix (Fin n) (Fin n) K) + v • T) *ᵥ (localWord A B j.val *ᵥ (localSeed (n := n) (K := K))) := by
    rw [Matrix.mulVec_mulVec, (localWord_commutes A B M ha hb j.val).eq,
      ← Matrix.mulVec_mulVec, huv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hT j]
  have hMQ : M * localCyclicMatrix A B = (u • (1 : Matrix (Fin n) (Fin n) K) + v • T) * localCyclicMatrix A B := by
    ext i j
    exact congrFun (hcol j) i
  calc
    M = M * (localCyclicMatrix A B * D) := by rw [hD, mul_one]
    _ = (M * localCyclicMatrix A B) * D := (mul_assoc _ _ _).symm
    _ = ((u • (1 : Matrix (Fin n) (Fin n) K) + v • T) * localCyclicMatrix A B) * D := by rw [hMQ]
    _ = (u • (1 : Matrix (Fin n) (Fin n) K) + v • T) := by rw [mul_assoc, hD, mul_one]
end Lyons.SimplicityCertificate.LocalCommutant

namespace Lyons.SimplicityCertificate

/-- A right inverse for the orbit basis and the involution's action on that basis. -/
@[expose] public def InvolutionLocalCyclicCertificate : Prop :=
  LocalCommutant.LocalCyclicCertificate
    (matrixRepresentation involutionLocalA) (matrixRepresentation involutionLocalB)
    (matrixRepresentation involutionLocalT)

/-- A word polynomial annihilating the seed with at most the expected kernel. -/
@[expose] public def InvolutionLocalKernelCertificate : Prop :=
  LocalCommutant.LocalKernelCertificate
    (matrixRepresentation involutionLocalA) (matrixRepresentation involutionLocalB)
    (matrixRepresentation involutionLocalT)

end Lyons.SimplicityCertificate
