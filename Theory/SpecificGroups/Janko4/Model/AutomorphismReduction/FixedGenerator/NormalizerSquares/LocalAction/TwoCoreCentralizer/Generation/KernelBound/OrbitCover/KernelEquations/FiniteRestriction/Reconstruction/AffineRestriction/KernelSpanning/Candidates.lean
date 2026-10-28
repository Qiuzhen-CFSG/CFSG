module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.KernelSpanning.BasisData

/-!
# Reconstruction vectors belong to the published candidate span

The 127 masks are checked combinations of the 124 affine directions, identity,
and the two scalar directions. Binary.combination_mem transports these exact
XOR identities to submodule membership. See KernelSpanning/source/README.md.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.KernelSpanning
open LinearMembership GeneratorCertificates Binary

def target (k : Fin 127) : RestrictionMatrix :=
  unflat (fun i => bit (targetRows.get k) i.val)

set_option maxRecDepth 100000 in
theorem target_affine_rows (k : Fin 124) :
    targetRows.get ⟨k.val, by omega⟩ = affineDirectionRows.get k := by
  have h : ∀ k : Fin 124,
      targetRows.get ⟨k.val, by omega⟩ = affineDirectionRows.get k := by decide +kernel
  exact h k

theorem target_affine (k : Fin 124) :
    target ⟨k.val, by omega⟩ = affineDirection k := by
  ext i j
  change bit (targetRows.get ⟨k.val, by omega⟩) (j.val + 50 * i.val) =
    bit (affineDirectionRows.get k) (50 * i.val + j.val)
  rw [target_affine_rows, Nat.add_comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem target_one : target 124 = 1 := by
  have h : ∀ i j : Fin 50,
      bit (targetRows.get 124) (50 * i.val + j.val) =
        (if i = j then (1 : ZMod 2) else 0) := by decide +kernel
  ext i j
  change bit (targetRows.get 124) (j.val + 50 * i.val) = _
  rw [Nat.add_comm, h]
  rfl

set_option maxRecDepth 100000 in
theorem target_scalar (k : Fin 2) :
    target ⟨125 + k.val, by omega⟩ = scalarDirection k := by
  have h : ∀ k : Fin 2,
      targetRows.get ⟨125 + k.val, by omega⟩ = scalarDirectionRows.get k := by
    decide +kernel
  ext i j
  change bit (targetRows.get ⟨125 + k.val, by omega⟩) (j.val + 50 * i.val) =
    bit (scalarDirectionRows.get k) (50 * i.val + j.val)
  rw [h, Nat.add_comm]

theorem target_mem (k : Fin 127) : target k ∈ candidateAlgebra := by
  by_cases hk : k.val < 124
  · have he : k = ⟨(⟨k.val,hk⟩ : Fin 124).val, by omega⟩ := rfl
    rw [he, target_affine]
    apply (show affineDirections ≤ candidateAlgebra from le_sup_left)
    exact Submodule.subset_span ⟨⟨k.val,hk⟩, rfl⟩
  · have hs : ∀ a : Fin 3 → ZMod 2, scalarLift a ∈ candidateAlgebra := by
      intro a
      apply (show LinearMap.range scalarLift ≤ candidateAlgebra from le_sup_right)
      exact ⟨a,rfl⟩
    have hcases : k = 124 ∨ k = 125 ∨ k = 126 := by
      have hlt := k.isLt
      rcases (show k.val = 124 ∨ k.val = 125 ∨ k.val = 126 by omega) with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases hcases with rfl | rfl | rfl
    · rw [target_one]
      simpa [scalarLift] using hs ![1,0,0]
    · rw [show (125 : Fin 127) = ⟨125 + (0 : Fin 2).val, by omega⟩ from rfl,
        target_scalar]
      simpa [scalarLift] using hs ![0,1,0]
    · rw [show (126 : Fin 127) = ⟨125 + (1 : Fin 2).val, by omega⟩ from rfl,
        target_scalar]
      simpa [scalarLift] using hs ![0,0,1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem combinations (k : Fin 127) :
    bs.get k = scan (coeff.get k) targetRows.toList := by
  have h : ∀ k : Fin 127, bs.get k = scan (coeff.get k) targetRows.toList := by
    decide +kernel
  exact h k

theorem basis_mem (k : Fin 127) :
    unflat (fun i : Fin (50*50) => bit (bs.get k) i.val) ∈ candidateAlgebra := by
  rw [combinations]
  have hspan : Submodule.span (ZMod 2) (Set.range target) ≤ candidateAlgebra := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact target_mem j
  exact hspan (combination_mem target targetRows (fun _ => rfl) (coeff.get k))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.KernelSpanning
