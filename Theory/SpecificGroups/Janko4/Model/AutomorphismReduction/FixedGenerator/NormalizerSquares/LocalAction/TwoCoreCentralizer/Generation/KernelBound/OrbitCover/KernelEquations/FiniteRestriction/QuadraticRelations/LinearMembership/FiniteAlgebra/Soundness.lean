module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Geometry
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.FiniteAlgebra.Annihilators

/-! The selected finite equations follow from the three hypotheses.
The annihilators are verified on all forty mixed generators; the last two
equations are rows of the original reconstruction identity.
See ../source/README.md for the finite contract. -/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra
open GeneratorCertificates

private theorem ann_pairing (w : Fin 560) (u : Fin 40) :
    pairing (rectDecode 50 (annRows w)) (mixedGenerator u) = 0 := by
  have h := fast_pairing (annMasks.get w) (mixedMasks.get u)
  rw [mixedMasks_checked] at h
  have hz : bit (parity600 (annMasks.get w &&& mixedMasks.get u)) 0 = 0 := by
    simp only [bit, ann_checked w u, Bool.false_eq_true, ↓reduceIte]
  exact h.symm.trans hz

private theorem ann_mixed (w : Fin 560) (M : MixedMatrix) (hM : M ∈ mixedSpace) :
    pairing (rectDecode 50 (annRows w)) M = 0 :=
  pairing_span mixedGenerator _ (ann_pairing w) M hM

private theorem source_vanish (S : RestrictionMatrix)
    (hS : PreservesMixedSpace S) (hA : PreservesMixedSpace (pairingAdjoint S))
    (k : Fin 2373) : ev (flat S) (rawMasks.get ⟨k.val, by omega⟩) = 0 := by
  rw [ev_flat, ← decode_slices, ← sourceRows_checked]
  rcases hchoice : sourceChoice.get k with ⟨adj,u,w⟩
  cases adj
  · simp only [sourceRows, hchoice, Bool.false_eq_true, ↓reduceIte,
      decode_mulRows, decode_transRows]
    change pairing ((mixedGenerator ⟨u.val, by omega⟩)ᵀ * rectDecode 50 (annRows w)) S = 0
    rw [← pairing_mul_left]
    exact ann_mixed w _ (hS _ (Submodule.subset_span ⟨⟨u.val, by omega⟩,rfl⟩))
  · simp only [sourceRows, hchoice, ↓reduceIte, decode_mulRows]
    rw [← adjLeft_checked w, ← adjRight_checked u, decode_mulRows, decode_mulRows,
      decode_transRows]
    change pairing (restrictionPairing * (rectDecode 50 (annRows w))ᵀ *
      (mixedGenerator ⟨u.val, by omega⟩ * pairingInverse)) S = 0
    rw [← pairing_mixed_adjoint]
    exact ann_mixed w _ (hA _ (Submodule.subset_span ⟨⟨u.val, by omega⟩,rfl⟩))

private theorem chart_mulVec (x : Fin 22 → ZMod 2) :
    rectDecode 22 chartRows *ᵥ x = synthesize x := by
  rw [chartRows_checked]
  ext i
  simp [Matrix.mulVec, dotProduct, synthesize, Finset.sum_apply, mul_comm]

private theorem reconstruction_vanish (S : RestrictionMatrix)
    (h : restrictionImage S = synthesize (coordinates (restrictionImage S))) :
    rectDecode 50 reconstructionRows *ᵥ (S *ᵥ Pi.single 0 1) = 0 := by
  rw [← reconstructionRows_checked, decode_xor_rows, decode_mulRows,
    ← chartExtraction_checked, decode_mulRows, embeddingRows_checked]
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, chart_mulVec]
  change restrictionImage S + synthesize (coordinates (restrictionImage S)) = 0
  rw [← h]
  ext i
  exact CharTwo.add_self_eq_zero ((restrictionImage S) i)

private theorem reconstruction_source_vanish (S : RestrictionMatrix)
    (h : restrictionImage S = synthesize (coordinates (restrictionImage S)))
    (r : Fin 2) : ev (flat S) (rawMasks.get ⟨2373 + r.val, by omega⟩) = 0 := by
  rw [ev_flat, reconstructionSource_checked]
  have heq : pairing
      (fun i j => if j = 0 then rectDecode 50 reconstructionRows ⟨r.val, by omega⟩ i else 0) S =
      (rectDecode 50 reconstructionRows *ᵥ (S *ᵥ Pi.single 0 1)) ⟨r.val, by omega⟩ := by
    rw [Matrix.mulVec_single_one]
    simp [pairing, Matrix.mulVec, dotProduct]
  rw [heq, reconstruction_vanish S h]
  rfl

/-- The exact three premises imply all selected binary linear equations. -/
theorem raw_vanish (S : RestrictionMatrix)
    (hS : PreservesMixedSpace S) (hA : PreservesMixedSpace (pairingAdjoint S))
    (h : restrictionImage S = synthesize (coordinates (restrictionImage S))) :
    ∀ k, ev (flat S) (rawMasks.get k) = 0 := by
  intro k
  by_cases hk : k.val < 2373
  · exact source_vanish S hS hA ⟨k.val,hk⟩
  · have hr : k.val - 2373 < 2 := by omega
    have hidx : 2373 + (k.val - 2373) = k.val := by omega
    simpa only [hidx] using reconstruction_source_vanish S h ⟨k.val - 2373,hr⟩

/-- Every displayed kernel vector is in the original, unchanged target span. -/
theorem kernel_mem (k : Fin 125) :
    (unflat (fun i : Fin 2500 => bit (kernelMasks.get k) i.val) : RestrictionMatrix) ∈
      restrictionLinearSpace := by
  rw [← kernelMasks_checked k]
  apply combination_mem restrictionLinearBasis targetMasks
  intro j
  rw [← decode_slices, targetMasks_checked]
  rfl

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra
