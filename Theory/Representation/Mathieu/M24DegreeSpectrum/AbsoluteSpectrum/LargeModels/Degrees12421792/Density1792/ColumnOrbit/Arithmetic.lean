module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.CertificateData

/-!
# Soundness of ordered column and reconstruction certificates

An earlier-parent tree realizes its columns by left multiplication by words in
any containing algebra. Independently, sequential XOR combinations reconstructing
every coordinate vector prove that a packed column list spans. The arithmetic
is connected to vector addition over `ZMod 2`; no externally computed rank is
used. The concrete degree-1792 consumer is `ColumnOrbit.lean`.

Source matrices and conventions: `../source/README.md`; mathematical application:
James, *The modular characters of the Mathieu groups*, J. Algebra 27 (1973).
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnCertificate
open Thompson.BinaryMatrix Matrix

def vector (n x : Nat) : Fin n → ZMod 2 := fun i => bit x i.val

theorem vector_xor (n a b : Nat) : vector n (a ^^^ b) = vector n a + vector n b := by
  funext i
  exact bit_xor a b i.val

theorem vector_zero (n : Nat) : vector n 0 = 0 := by
  ext i
  simp [vector, bit]

theorem vector_two_pow (n : Nat) (i : Fin n) : vector n (2 ^ i.val) = Pi.single i 1 := by
  ext j
  simp [vector, bit, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]

/-- Linear combination by a packed coefficient row; scan the columns sequentially. -/
def select (a : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, k => (if a.testBit k then x else 0) ^^^ select a xs (k+1)

theorem vector_select_mem (n : Nat) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (xs : List Nat) (hxs : ∀ x ∈ xs, vector n x ∈ U) (a k : Nat) :
    vector n (select a xs k) ∈ U := by
  induction xs generalizing k with
  | nil => simpa only [select, vector_zero] using U.zero_mem
  | cons x xs ih =>
    rw [select, vector_xor]
    apply U.add_mem
    · split
      · exact hxs x (List.mem_cons_self ..)
      · simpa only [vector_zero] using U.zero_mem
    · exact ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) (k+1)

/-- Reconstruction of coordinate vectors is sufficient for spanning. -/
theorem eq_top_of_reconstruction (n : Nat)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (xs : List Nat)
    (hxs : ∀ x ∈ xs, vector n x ∈ U)
    (h : ∀ i : Fin n, ∃ a, select a xs 0 = 2 ^ i.val) : U = ⊤ := by
  apply top_unique
  intro x _
  have hcoord (i : Fin n) : Pi.single i (1 : ZMod 2) ∈ U := by
    obtain ⟨a, ha⟩ := h i
    rw [← vector_two_pow, ← ha]
    exact vector_select_mem n U xs hxs a 0
  rw [show x = ∑ i, x i • Pi.single i 1 by ext j; simp [Pi.single_apply]]
  exact U.sum_mem (fun i _ => U.smul_mem _ (hcoord i))

/-- Earlier-parent certificate, read without repeated indexed traversal. -/
def checkParents : Nat → List (Nat × Bool) → Bool
  | _, [] => true
  | c, (p, _) :: ps => decide (p < c) && checkParents (c+1) ps

theorem checkParents_sound (ps : List (Nat × Bool)) (c : Nat)
    (h : checkParents c ps = true) (i : Nat) (hi : i < ps.length) :
    ps[i]!.1 < c+i := by
  induction ps generalizing c i with
  | nil => simp at hi
  | cons p ps ih =>
    simp only [checkParents, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have ht := ih (c+1) h.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht

/-- An ordered predecessor tree gives literal algebra-orbit witnesses. -/
theorem orbit_reachable {k ι : Type*} [CommSemiring k] [Fintype ι] [DecidableEq ι]
    (n : Nat)
    (Q : Subalgebra k (Matrix ι ι k))
    (A B : Matrix ι ι k) (hA : A ∈ Q) (hB : B ∈ Q)
    (v : ι → k) (columns : Fin (n+1) → ι → k)
    (p : Fin n → Fin (n+1)) (actor : Fin n → Bool)
    (hp : ∀ i, p i < i.succ) (hzero : columns 0 = v)
    (hstep : ∀ i, (if actor i then A else B).mulVec (columns (p i)) = columns i.succ) :
    ∀ i, ∃ L ∈ Q, L.mulVec v = columns i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, (one_mulVec v).trans hzero.symm⟩
    | succ i =>
      obtain ⟨L, hL, he⟩ := ih (p i) (hp i)
      refine ⟨(if actor i then A else B) * L, Q.mul_mem ?_ hL, ?_⟩
      · split <;> assumption
      · rw [← mulVec_mulVec, he]
        exact hstep i

/-- Sequential verification of a block of coordinate reconstructions. -/
def checkReconstructions (xs : List Nat) : Nat → List Nat → Bool
  | _, [] => true
  | c, a :: as => (select a xs 0 == 2 ^ c) && checkReconstructions xs (c+1) as

theorem checkReconstructions_sound (xs as : List Nat) (c : Nat)
    (h : checkReconstructions xs c as = true) (i : Nat) (hi : i < as.length) :
    select as[i]! xs 0 = 2 ^ (c+i) := by
  induction as generalizing c i with
  | nil => simp at hi
  | cons a as ih =>
    simp only [checkReconstructions, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have ht := ih (c+1) h.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnCertificate
