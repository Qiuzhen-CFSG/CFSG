module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Algebra
public import Mathlib.Tactic.LinearCombination
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Matrices
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.ExteriorIndex

/-! The transported Frobenius functional is evaluated on the upper triangle of
an alternating form. Direct entry checks identify its coefficients with the
packed annihilator witness; the published exterior indexing reindexes the sum.
Source and witness conventions: ScalarCertificate/source/README.md. -/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
open ExteriorIndex




private instance finForall {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) := Nat.decidableForallFin P

private instance scalarEq (x y : ZMod 2) : Decidable (x = y) := ZMod.decidableEq 2 x y

set_option maxRecDepth 8192 in
private theorem upper_sum (f : Fin 112 → Fin 112 → ZMod 2) :
    (∑ k : Fin 6216, f (upperPair k).1 (upperPair k).2) =
      ∑ i : Fin 112, ∑ j : Fin 112, if i < j then f i j else 0 := by
  rw [← Fintype.sum_prod_type (f := fun p : Fin 112 × Fin 112 =>
    if p.1 < p.2 then f p.1 p.2 else 0)]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ => upperPair k)
  · intro k _
    simpa using upperPair_lt k
  · intro a _ b _ h
    apply Fin.ext
    simpa only [upperPair_index] using congrArg (fun p => exteriorIndex p.1 p.2) h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact ⟨upperIndex p, Finset.mem_univ _, upperPair_inverse p.1 p.2 hp⟩
  · intro k _
    rfl

theorem pairing_upper (F : Matrix (Fin 112) (Fin 112) (ZMod 2)) (r : ℕ) :
    pairing F (decodeExteriorForm r) =
      ∑ k : Fin 6216, (F (upperPair k).1 (upperPair k).2 +
        F (upperPair k).2 (upperPair k).1) * bit r k.val := by
  have h (i j : Fin 112) :
      F i j * decodeExteriorForm r i j =
      (if i < j then F i j * bit r (exteriorIndex i j) else 0) +
      (if j < i then F i j * bit r (exteriorIndex j i) else 0) := by
    by_cases hij : i < j
    · simp [decodeExteriorForm, bit, hij, not_lt_of_gt hij]
    · by_cases hji : j < i <;> simp [decodeExteriorForm, bit, hij, hji]
  unfold pairing
  simp_rw [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin 112 =>
    if j < i then F i j * bit r (exteriorIndex j i) else 0)]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  have hs := upper_sum (fun i j =>
    (F i j + F j i) * bit r (exteriorIndex i j))
  simp only [upperPair_index] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

private theorem phi_entries_check : ∀ i j : Fin 112, i < j →
    decodeRows 112 phiRows i j + decodeRows 112 phiRows j i =
      bit annihilatorBits (exteriorIndex i j) := by
  decide +kernel

theorem phi_upper_check (k : Fin 6216) :
    decodeRows 112 phiRows (upperPair k).1 (upperPair k).2 +
      decodeRows 112 phiRows (upperPair k).2 (upperPair k).1 =
      bit annihilatorBits k.val := by
  simpa only [upperPair_index] using
    phi_entries_check (upperPair k).1 (upperPair k).2 (upperPair_lt k)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
