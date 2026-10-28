module

public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients
import Mathlib.Tactic

/-!
# Three cyclic generators inside a syntheme displacement plane

The rows 72, 528 and 600 are the three nonzero vectors of a plane moved by
(01) in the actual fifteen-syntheme module. Each generates the augmentation
core under A₆: short sums of conjugates of row 72 give the coordinate
augmentation generators, row 528 is conjugate to row 72, and three conjugates
of row 600 sum to row 72. All finite identities below are kernel checked.
This replaces enumeration of the 63 hyperplanes in the six-dimensional
transposition displacement space by a three-vector certificate.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Lemma 13.8.34, printed p.968 (PDF p.985),
final transvection contradiction. The coordinate convention is that of the
parent's named `synthemeHom`, independently of the duad action.
-/

@[expose] public section
open BinaryPermutation Representation Module
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace Representation.SixLetterRadicalDisplacement.PermutationQuotients.TranspositionRank
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
private def corePaths : Fin 15 → List S :=
  ![[],
    [Equiv.swap 1 0 * Equiv.swap 1 4 * Equiv.swap 1 2 * Equiv.swap 0 5],
    [Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 1 3 * Equiv.swap 0 5],
    [Equiv.swap 1 0 * Equiv.swap 0 3],
    [Equiv.swap 1 0 * Equiv.swap 0 3, Equiv.swap 2 4 * Equiv.swap 0 5],
    [Equiv.swap 1 0 * Equiv.swap 0 3, Equiv.swap 2 0 * Equiv.swap 2 4 * Equiv.swap 1 3 * Equiv.swap 0 5],
    [Equiv.swap 4 5 * Equiv.swap 0 3],
    [Equiv.swap 4 5 * Equiv.swap 0 3, Equiv.swap 3 0 * Equiv.swap 3 2 * Equiv.swap 2 4 * Equiv.swap 0 5],
    [Equiv.swap 4 5 * Equiv.swap 0 3, Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 1 2 * Equiv.swap 0 5],
    [Equiv.swap 4 5 * Equiv.swap 0 3, Equiv.swap 2 1 * Equiv.swap 2 4 * Equiv.swap 1 0 * Equiv.swap 0 5],
    [Equiv.swap 1 0 * Equiv.swap 0 3, Equiv.swap 3 2 * Equiv.swap 2 4 * Equiv.swap 1 0 * Equiv.swap 0 5],
    [Equiv.swap 3 1 * Equiv.swap 2 4 * Equiv.swap 1 0 * Equiv.swap 0 5],
    [Equiv.swap 4 5 * Equiv.swap 0 3, Equiv.swap 1 0 * Equiv.swap 2 4 * Equiv.swap 1 3 * Equiv.swap 0 5],
    [Equiv.swap 1 0 * Equiv.swap 0 3, Equiv.swap 3 0 * Equiv.swap 1 4 * Equiv.swap 1 2 * Equiv.swap 0 5],
    [Equiv.swap 2 3 * Equiv.swap 3 0 * Equiv.swap 2 4 * Equiv.swap 0 5]]
private theorem corePaths_even (i : Fin 15) (g : S) (hg : g ∈ corePaths i) :
    g ∈ alternatingGroup (Fin 6) := by
  have h : ∀ i : Fin 15, ∀ g ∈ corePaths i, g ∈ alternatingGroup (Fin 6) := by decide +kernel
  exact h i g hg
private theorem corePaths_sum (i : Fin 15) :
    ((corePaths i).map (fun g => rho g (row 72))).sum =
      Pi.single i 1 - Pi.single 0 1 := by
  have h : ∀ i : Fin 15,
      ((corePaths i).map (fun g => rho g (row 72))).sum =
        Pi.single i 1 - Pi.single 0 1 := by decide +kernel
  exact h i

private def move528 : S := Equiv.swap 4 3 * Equiv.swap 3 5
private theorem move528_even : move528 ∈ alternatingGroup (Fin 6) := by decide
private theorem move528_row : rho move528 (row 528) = row 72 := by decide +kernel
private def moves600 : List S := [Equiv.swap 4 1 * Equiv.swap 1 0 * Equiv.swap 1 3 * Equiv.swap 0 5, Equiv.swap 3 0 * Equiv.swap 3 2 * Equiv.swap 2 4 * Equiv.swap 0 5, Equiv.swap 3 1 * Equiv.swap 2 4 * Equiv.swap 1 0 * Equiv.swap 0 5]
private theorem moves600_even : ∀ g ∈ moves600, g ∈ alternatingGroup (Fin 6) := by decide
private theorem moves600_row :
    (moves600.map (fun g => rho g (row 600))).sum = row 72 := by decide +kernel

private theorem core_le_of_differences (K : Submodule (ZMod 2) P)
    (h : ∀ i : Fin 15, Pi.single i 1 - Pi.single 0 1 ∈ K) : P0 ≤ K := by
  intro v hv
  have hz : ∑ i, v i = 0 := hv
  have he : (∑ i : Fin 15, v i • (Pi.single i 1 - Pi.single 0 1)) = v := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hz, zero_smul, sub_zero]
    ext j
    simp [Pi.single_apply, smul_eq_mul]
  rw [← he]
  exact K.sum_mem fun i _ => K.smul_mem _ (h i)

private theorem list_sum_mem (K : Submodule (ZMod 2) P) (s : List S) (v : P)
    (h : ∀ g ∈ s, rho g v ∈ K) : (s.map (fun g => rho g v)).sum ∈ K := by
  apply _root_.list_sum_mem
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  exact h g hg

private theorem core_le_of_row72 (K : Submodule (ZMod 2) P)
    (hinv : ∀ g : alternatingGroup (Fin 6), ∀ v ∈ K, rho g.val v ∈ K)
    (hseed : row 72 ∈ K) : P0 ≤ K := by
  apply core_le_of_differences K
  intro i
  rw [← corePaths_sum i]
  apply list_sum_mem K
  intro g hg
  exact hinv ⟨g, corePaths_even i g hg⟩ _ hseed

/-- Each of the three nonzero vectors of the selected displacement plane
forces an alternating-invariant submodule to contain the augmentation core. -/
theorem core_le_of_seed (K : Submodule (ZMod 2) P)
    (hinv : ∀ g : alternatingGroup (Fin 6), ∀ v ∈ K, rho g.val v ∈ K)
    (n : ℕ) (hn : n = 72 ∨ n = 528 ∨ n = 600) (hseed : row n ∈ K) : P0 ≤ K := by
  apply core_le_of_row72 K hinv
  rcases hn with rfl | rfl | rfl
  · exact hseed
  · rw [← move528_row]
    exact hinv ⟨move528, move528_even⟩ _ hseed
  · rw [← moves600_row]
    apply list_sum_mem K
    intro g hg
    exact hinv ⟨g, moves600_even g hg⟩ _ hseed

end Representation.SixLetterRadicalDisplacement.PermutationQuotients.TranspositionRank
