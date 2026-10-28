module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Packed

/-!
# Sparse span certificates and native layer assembly

A list of selected rows certifies span membership without traversing all unused
coordinates. Mutual combinations give span equality. The literal finite-index
flattening then connects the checked displacement table to the canonical layer.
This supports the native invariant-subspace proof of KW (1988), Corollary 2.3.6.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open GeneratorCertificates

def sparseCombine {n : ℕ} (r : Vector ℕ n) (indices : List (Fin n)) : ℕ :=
  xorList (indices.map r.get)

theorem decode_sparseCombine_mem {n : ℕ} (r : Vector ℕ n) (indices : List (Fin n)) :
    decode (sparseCombine r indices) ∈ rowSpan r := by
  induction indices with
  | nil =>
    change decode 0 ∈ rowSpan r
    have he : decode 0 = 0 := by funext j; simp [decode,bit]
    rw [he]
    exact Submodule.zero_mem _
  | cons i indices ih =>
    change decode (r.get i ^^^ sparseCombine r indices) ∈ rowSpan r
    rw [decode_xor]
    exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_range_self i)) ih

theorem rowSpan_le_of_sparse {n k : ℕ} (r : Vector ℕ n) (s : Vector ℕ k)
    (c : Fin n → List (Fin k)) (hc : ∀ i, r.get i = sparseCombine s (c i)) :
    rowSpan r ≤ rowSpan s := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change decode (r.get i) ∈ rowSpan s
  rw [hc]
  exact decode_sparseCombine_mem s _

theorem rowSpan_eq_of_certificates {n k : ℕ} (r : Vector ℕ n) (s : Vector ℕ k)
    (forward : Fin n → ℕ) (reverse : Fin k → List (Fin n))
    (hf : ∀ i, r.get i = combine s (forward i))
    (hr : ∀ i, s.get i = sparseCombine r (reverse i)) : rowSpan r = rowSpan s :=
  le_antisymm (rowSpan_le_of_combine r s forward hf) (rowSpan_le_of_sparse s r reverse hr)

/-- A finite table of generator displacements computes the actual canonical
layer, including the literal flattening order of its pair of indices. -/
theorem next_layer_eq_step {n : ℕ} (k : ℕ) (r : Vector ℕ n)
    (step : Vector ℕ (n*8)) (hr : layer (nativeEight 0) k = rowSpan r)
    (he : ∀ i j, displacement (nativeGenerator j) (decode (r.get i)) =
      decode (step.get (finProdFinEquiv (i,j)))) :
    layer (nativeEight 0) (k+1) = rowSpan step := by
  rw [next_layer_rows k r hr]
  have hrange : Set.range (fun p : Fin n × Fin 8 =>
      displacement (nativeGenerator p.2) (decode (r.get p.1))) =
      Set.range (fun i : Fin (n*8) => decode (step.get i)) := by
    ext v
    constructor
    · rintro ⟨⟨i,j⟩,rfl⟩
      exact ⟨finProdFinEquiv (i,j), (he i j).symm⟩
    · rintro ⟨i,rfl⟩
      refine ⟨finProdFinEquiv.symm i, ?_⟩
      simpa only [Prod.mk.eta,Equiv.apply_symm_apply] using
        he (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  rw [hrange]
  rfl
end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
