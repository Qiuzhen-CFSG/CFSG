module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.Equations

/-!
# Linear consequences of mixed-space preservation

Frobenius orthogonality extends from the forty generators to their span.
Right multiplication and the pairing adjoint then give exactly the two
coefficient formulas used in the source certificate. See source/README.md.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
open LinearMembership GeneratorCertificates Binary

/-- A packed multiplication check proves the decoded matrix identity. -/
lemma product_of_scan {m n k : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m) (h : ∀ i, scan (xs.get i) ys.toList = zs.get i) :
    rectDecode n xs * rectDecode k ys = rectDecode k zs := by
  rw [← decode_mulRows]
  congr 1
  apply Vector.ext
  intro i hi
  exact (get_ofFn _ ⟨i,hi⟩).trans (h ⟨i,hi⟩)

/-- A single packed scan checks orthogonality to the entire generator family. -/
lemma annihilator_of_scan (cols : Vector ℕ 600)
    (hc : ∀ (i : Fin 600) (j : Fin 40),
      bit (cols.get i) j.val = flat (mixedGenerator j) i)
    (w : ℕ) (hw : scan w cols.toList = 0) :
    ∀ j, pairing (rectDecode 50 (slices 12 50 w)) (mixedGenerator j) = 0 := by
  intro j
  rw [decode_slices, ← ev_flat]
  calc
    ev (flat (mixedGenerator j)) w = ev (fun i => bit (cols.get i) j.val) w := by
      congr 1
      funext i
      exact (hc i j).symm
    _ = bit (scan w cols.toList) j.val := (bit_scan w cols j.val).symm
    _ = 0 := by rw [hw]; simp [bit]

/-- An annihilator vanishes on every right translate lying in the mixed span. -/
lemma right_vanishes (S : RestrictionMatrix) (hmixed : PreservesMixedSpace S)
    (W : MixedMatrix) (hW : ∀ j, pairing W (mixedGenerator j) = 0)
    (u : Fin 40) (r : ℕ)
    (hr : unflat (fun i : Fin 2500 => bit r i.val) = (mixedGenerator u)ᵀ * W) :
    ev (flat S) r = 0 := by
  rw [ev_flat, hr, ← pairing_mul_left]
  exact pairing_span mixedGenerator W hW _
    (hmixed _ (Submodule.subset_span ⟨u,rfl⟩))

/-- Adjoint preservation gives the transposed pairing coefficient. -/
lemma adjoint_vanishes (S : RestrictionMatrix)
    (hadjoint : PreservesMixedSpace (pairingAdjoint S))
    (W : MixedMatrix) (hW : ∀ j, pairing W (mixedGenerator j) = 0)
    (u : Fin 40) (r : ℕ)
    (hr : unflat (fun i : Fin 2500 => bit r i.val) =
      restrictionPairing * Wᵀ * (mixedGenerator u * pairingInverse)) :
    ev (flat S) r = 0 := by
  rw [ev_flat, hr, ← pairing_mixed_adjoint]
  exact pairing_span mixedGenerator W hW _
    (hadjoint _ (Submodule.subset_span ⟨u,rfl⟩))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
