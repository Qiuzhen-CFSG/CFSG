module

public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients

/-!
# Invariant kernels in the fifteen-syntheme module

For each marked pair of involutions, one second displacement and thirteen
translates span the augmentation core. The displayed identities express every
vector `delta_i + delta_0` as a sum of these translates. All row identities and
alternating-group memberships are proved by kernel reduction against the actual
published syntheme action. The spanning argument then applies to any invariant
submodule, without a dimension or rank certificate as a hypothesis.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 13.8.34, printed p.968 (PDF p.985), using
13.8.4(5),(6). Witnesses were found by binary elimination; only the explicit
identities below are used in the proof.
-/

public section

open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace Representation.SixLetterRadicalDisplacement.PermutationQuotients

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem core_le_of_marked_pairs (K : Submodule (ZMod 2) P)
    (hp : ∀ i : Fin 15, Pi.single i (1 : ZMod 2) + Pi.single 0 1 ∈ K) : P0 ≤ K := by
  intro v hv
  have heq : (∑ i, v i • (Pi.single i (1 : ZMod 2) + Pi.single 0 1)) = v := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    have hsum : ∑ i, v i = 0 := hv
    rw [hsum, zero_smul, add_zero]
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single v
  rw [← heq]
  exact K.sum_mem fun i _ => K.smul_mem _ (hp i)

/-- The alternating-invariant kernel forced by the even radical contains the core. -/
theorem core_le_of_alternating_second_displacements (K : Submodule (ZMod 2) P)
    (hK : ∀ g : alternatingGroup (Fin 6), ∀ v ∈ K, rho g.val v ∈ K)
    (hsecond : ∀ v : P, rho (swap01 * swap23) (rho (swap01 * swap45) v - v) -
      (rho (swap01 * swap45) v - v) ∈ K) : P0 ≤ K := by
  have h0 : row 5392 ∈ K := by
    rw [← show rho (swap01 * swap23) (rho (swap01 * swap45) (row 16) - row 16) -
      (rho (swap01 * swap45) (row 16) - row 16) = row 5392 by decide]
    exact hsecond (row 16)
  have h1 : row 17442 ∈ K := by
    rw [← show rho ((Equiv.swap 0 1 * Equiv.swap 1 2)) (row 5392) = row 17442 by decide]
    exact hK ⟨(Equiv.swap 0 1 * Equiv.swap 1 2), by decide⟩ _ h0
  have h2 : row 17156 ∈ K := by
    rw [← show rho ((Equiv.swap 1 2 * Equiv.swap 2 3)) (row 5392) = row 17156 by decide]
    exact hK ⟨(Equiv.swap 1 2 * Equiv.swap 2 3), by decide⟩ _ h0
  have h3 : row 10320 ∈ K := by
    rw [← show rho ((Equiv.swap 2 3 * Equiv.swap 3 4)) (row 5392) = row 10320 by decide]
    exact hK ⟨(Equiv.swap 2 3 * Equiv.swap 3 4), by decide⟩ _ h0
  have h4 : row 17504 ∈ K := by
    rw [← show rho ((Equiv.swap 3 4 * Equiv.swap 4 5)) (row 5392) = row 17504 by decide]
    exact hK ⟨(Equiv.swap 3 4 * Equiv.swap 4 5), by decide⟩ _ h0
  have h5 : row 8864 ∈ K := by
    rw [← show rho ((Equiv.swap 1 2 * Equiv.swap 2 3) * (Equiv.swap 0 1 * Equiv.swap 1 2)) (row 5392) = row 8864 by decide]
    exact hK ⟨(Equiv.swap 1 2 * Equiv.swap 2 3) * (Equiv.swap 0 1 * Equiv.swap 1 2), by decide⟩ _ h0
  have h6 : row 4369 ∈ K := by
    rw [← show rho ((Equiv.swap 2 3 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 1 2)) (row 5392) = row 4369 by decide]
    exact hK ⟨(Equiv.swap 2 3 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 1 2), by decide⟩ _ h0
  have h7 : row 16652 ∈ K := by
    rw [← show rho ((Equiv.swap 3 4 * Equiv.swap 4 5) * (Equiv.swap 0 1 * Equiv.swap 1 2)) (row 5392) = row 16652 by decide]
    exact hK ⟨(Equiv.swap 3 4 * Equiv.swap 4 5) * (Equiv.swap 0 1 * Equiv.swap 1 2), by decide⟩ _ h0
  have h8 : row 10260 ∈ K := by
    rw [← show rho ((Equiv.swap 1 2 * Equiv.swap 2 3) * (Equiv.swap 1 2 * Equiv.swap 2 3)) (row 5392) = row 10260 by decide]
    exact hK ⟨(Equiv.swap 1 2 * Equiv.swap 2 3) * (Equiv.swap 1 2 * Equiv.swap 2 3), by decide⟩ _ h0
  have h9 : row 6154 ∈ K := by
    rw [← show rho ((Equiv.swap 2 3 * Equiv.swap 3 4) * (Equiv.swap 1 2 * Equiv.swap 2 3)) (row 5392) = row 6154 by decide]
    exact hK ⟨(Equiv.swap 2 3 * Equiv.swap 3 4) * (Equiv.swap 1 2 * Equiv.swap 2 3), by decide⟩ _ h0
  have h10 : row 5377 ∈ K := by
    rw [← show rho ((Equiv.swap 3 4 * Equiv.swap 4 5) * (Equiv.swap 1 2 * Equiv.swap 2 3)) (row 5392) = row 5377 by decide]
    exact hK ⟨(Equiv.swap 3 4 * Equiv.swap 4 5) * (Equiv.swap 1 2 * Equiv.swap 2 3), by decide⟩ _ h0
  have h11 : row 2186 ∈ K := by
    rw [← show rho ((Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 2 3 * Equiv.swap 3 4)) (row 5392) = row 2186 by decide]
    exact hK ⟨(Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 2 3 * Equiv.swap 3 4), by decide⟩ _ h0
  have h12 : row 17160 ∈ K := by
    rw [← show rho ((Equiv.swap 3 4 * Equiv.swap 4 5) * (Equiv.swap 3 4 * Equiv.swap 4 5)) (row 5392) = row 17160 by decide]
    exact hK ⟨(Equiv.swap 3 4 * Equiv.swap 4 5) * (Equiv.swap 3 4 * Equiv.swap 4 5), by decide⟩ _ h0
  have h13 : row 10308 ∈ K := by
    rw [← show rho ((Equiv.swap 2 3 * Equiv.swap 3 4) * (Equiv.swap 2 3 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 1 2)) (row 5392) = row 10308 by decide]
    exact hK ⟨(Equiv.swap 2 3 * Equiv.swap 3 4) * (Equiv.swap 2 3 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 1 2), by decide⟩ _ h0
  apply core_le_of_marked_pairs
  intro i
  -- These sums recover all fourteen augmentation generators.
  fin_cases i
  · convert K.zero_mem using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h1) h4) h8) h10) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem h0 h3) h10) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h2) h3) h10) h12) h13) using 1
    decide
  · convert (K.add_mem h0 h10) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h1) h2) h3) h4) h5) h7) h10) h11) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem h0 h8) h10) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h1 h3) h5) h8) h9) h10) h12) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h1) h3) h5) h6) h8) h11) h12) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h3) h7) h10) h12) h13) using 1
    decide
  · convert (K.add_mem h0 h6) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h2 h4) h5) h9) h10) h11) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h1 h3) h5) h8) h10) h11) h12) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h2 h3) h4) h5) h8) h9) h10) h11) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h1) h2) h3) h5) h6) h7) h8) h11) h13) using 1
    decide

/-- The symmetric-invariant kernel forced by the coordinate four-group contains the core. -/
theorem core_le_of_symmetric_second_displacements (K : Submodule (ZMod 2) P)
    (hK : ∀ g : S, ∀ v ∈ K, rho g v ∈ K)
    (hsecond : ∀ v : P, rho swap01 (rho swap23 v - v) -
      (rho swap23 v - v) ∈ K) : P0 ≤ K := by
  have h0 : row 1680 ∈ K := by
    rw [← show rho swap01 (rho swap23 (row 16) - row 16) -
      (rho swap23 (row 16) - row 16) = row 1680 by decide]
    exact hsecond (row 16)
  have h1 : row 2818 ∈ K := by
    rw [← show rho ((Equiv.swap 1 2)) (row 1680) = row 2818 by decide]
    exact hK ((Equiv.swap 1 2)) _ h0
  have h2 : row 1224 ∈ K := by
    rw [← show rho ((Equiv.swap 3 4)) (row 1680) = row 1224 by decide]
    exact hK ((Equiv.swap 3 4)) _ h0
  have h3 : row 12576 ∈ K := by
    rw [← show rho ((Equiv.swap 4 5)) (row 1680) = row 12576 by decide]
    exact hK ((Equiv.swap 4 5)) _ h0
  have h4 : row 24594 ∈ K := by
    rw [← show rho ((Equiv.swap 0 1) * (Equiv.swap 1 2)) (row 1680) = row 24594 by decide]
    exact hK ((Equiv.swap 0 1) * (Equiv.swap 1 2)) _ h0
  have h5 : row 3108 ∈ K := by
    rw [← show rho ((Equiv.swap 2 3) * (Equiv.swap 1 2)) (row 1680) = row 3108 by decide]
    exact hK ((Equiv.swap 2 3) * (Equiv.swap 1 2)) _ h0
  have h6 : row 2369 ∈ K := by
    rw [← show rho ((Equiv.swap 3 4) * (Equiv.swap 1 2)) (row 1680) = row 2369 by decide]
    exact hK ((Equiv.swap 3 4) * (Equiv.swap 1 2)) _ h0
  have h7 : row 8520 ∈ K := by
    rw [← show rho ((Equiv.swap 4 5) * (Equiv.swap 3 4)) (row 1680) = row 8520 by decide]
    exact hK ((Equiv.swap 4 5) * (Equiv.swap 3 4)) _ h0
  have h8 : row 22560 ∈ K := by
    rw [← show rho ((Equiv.swap 3 4) * (Equiv.swap 4 5)) (row 1680) = row 22560 by decide]
    exact hK ((Equiv.swap 3 4) * (Equiv.swap 4 5)) _ h0
  have h9 : row 420 ∈ K := by
    rw [← show rho ((Equiv.swap 3 4) * (Equiv.swap 2 3) * (Equiv.swap 1 2)) (row 1680) = row 420 by decide]
    exact hK ((Equiv.swap 3 4) * (Equiv.swap 2 3) * (Equiv.swap 1 2)) _ h0
  have h10 : row 2089 ∈ K := by
    rw [← show rho ((Equiv.swap 2 3) * (Equiv.swap 3 4) * (Equiv.swap 1 2)) (row 1680) = row 2089 by decide]
    exact hK ((Equiv.swap 2 3) * (Equiv.swap 3 4) * (Equiv.swap 1 2)) _ h0
  have h11 : row 16577 ∈ K := by
    rw [← show rho ((Equiv.swap 4 5) * (Equiv.swap 3 4) * (Equiv.swap 1 2)) (row 1680) = row 16577 by decide]
    exact hK ((Equiv.swap 4 5) * (Equiv.swap 3 4) * (Equiv.swap 1 2)) _ h0
  have h12 : row 16409 ∈ K := by
    rw [← show rho ((Equiv.swap 4 5) * (Equiv.swap 2 3) * (Equiv.swap 3 4) * (Equiv.swap 1 2)) (row 1680) = row 16409 by decide]
    exact hK ((Equiv.swap 4 5) * (Equiv.swap 2 3) * (Equiv.swap 3 4) * (Equiv.swap 1 2)) _ h0
  have h13 : row 8218 ∈ K := by
    rw [← show rho ((Equiv.swap 3 4) * (Equiv.swap 4 5) * (Equiv.swap 2 3) * (Equiv.swap 3 4) * (Equiv.swap 1 2)) (row 1680) = row 8218 by decide]
    exact hK ((Equiv.swap 3 4) * (Equiv.swap 4 5) * (Equiv.swap 2 3) * (Equiv.swap 3 4) * (Equiv.swap 1 2)) _ h0
  apply core_le_of_marked_pairs
  intro i
  -- These sums recover all fourteen augmentation generators.
  fin_cases i
  · convert K.zero_mem using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h1) h4) h5) h9) h12) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h4 h6) h9) h10) h11) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem h2 h5) h6) h9) using 1
    decide
  · convert (K.add_mem (K.add_mem h4 h12) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h1) h2) h7) h10) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h1) h3) h4) h5) h6) h8) h9) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h1) h2) h3) h8) h11) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h3 h4) h6) h7) h8) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem h1 h3) h8) h12) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem h2 h4) h11) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h1) h5) h6) h7) h9) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem h4 h8) h10) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem h0 h1) h2) h6) h13) using 1
    decide
  · convert (K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem h2 h4) h5) h6) h9) h13) using 1
    decide

end Representation.SixLetterRadicalDisplacement.PermutationQuotients
