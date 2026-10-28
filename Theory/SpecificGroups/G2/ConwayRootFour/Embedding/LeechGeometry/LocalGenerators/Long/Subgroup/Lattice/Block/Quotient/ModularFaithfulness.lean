module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient.Restriction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient.ModularFaithfulness.Certificates

/-!
# Faithfulness of restriction on the modular block group

The reduced generators preserve an explicitly checked finite vector set.
Three translates of each of e₂, e₄, e₅ by the invariant row space distinguish
that seed within the set. Thus a generated matrix fixing the invariant rows
also fixes all three seeds. An explicit inverse to this six-row frame forces
the matrix to be the identity.

This proves the literal modular kernel bound required by `matrixQuotient`.
It is independent of the integral sign-kernel argument and needs no group
recognition, Hermitian-form premise, or orbit-cardinality assertion.

Numerical source: John Bray's ATLAS `6L34G1-Ar6aB0.M`, with the original row
conventions in `MatrixData`. The finite data, checked certificates, and their
reproducible source are in the `ModularFaithfulness` submodules.
-/

public section
open Atlas.Algebra Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block
namespace ModularFaithfulness

private def vectors : Set Row := Set.range point

private abbrev red := Matrix.GeneralLinearGroup.map (n := Fin 6) reductionScalars
private theorem vec_cancel (g : GL (Fin 6) GoldenFour) (v : Row) :
    (v ᵥ* g.val) ᵥ* g⁻¹.val = v := by
  rw [Matrix.vecMul_vecMul]
  have h : g.val * g⁻¹.val = (1 : Matrix _ _ GoldenFour) :=
    congrArg (fun x : GL (Fin 6) GoldenFour => x.val) (mul_inv_cancel g)
  rw [h, Matrix.vecMul_one]

private theorem invariant (g : matrixGroup) : ∀ v ∈ vectors, v ᵥ* (reduction g).val ∈ vectors := by
  obtain ⟨g, hg⟩ := g
  change ∀ v ∈ vectors, v ᵥ* (red g).val ∈ vectors
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, (stepA i).symm⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, (stepB i).symm⟩
  | one => simp
  | mul g h _ _ hg hh =>
    intro v hv
    simpa only [map_mul, GeneralLinearGroup.coe_mul, ← Matrix.vecMul_vecMul] using
      hh _ (hg _ hv)
  | inv g _ hg =>
    have hi : Function.Injective (fun v : Row => v ᵥ* (red g).val) := by
      intro v w hvw
      have h := congrArg (fun u => u ᵥ* (red g)⁻¹.val) hvw
      simpa only [vec_cancel] using h
    have hs : vectors.Finite := Set.finite_range point
    have hsurj := ((hs.injOn_iff_bijOn_of_mapsTo hg).mp hi.injOn).surjOn
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hsurj hv
    simpa only [map_inv, vec_cancel] using hw

private theorem admissible_of_mem {v : Row} (hv : v ∈ vectors) : admissible v := by
  obtain ⟨j, rfl⟩ := hv
  exact point_admissible j

private theorem seed_fixed (g : matrixGroup)
    (h : modularRows * (reduction g).val = modularRows) (i : Fin 3) :
    seed i ᵥ* (reduction g).val = seed i := by
  have hshift (k : Fin 3) : shift i k ᵥ* (reduction g).val = shift i k := by
    rw [coefficients_eq, Matrix.vecMul_vecMul, h]
  have hseed : seed i ∈ vectors := ⟨seedIndex i, seed_eq i⟩
  obtain ⟨j, hj⟩ := invariant g _ hseed
  rw [← hj]
  apply distinguish i j
  intro k
  have hmem : seed i + shift i k ∈ vectors := ⟨shiftIndex i k, shift_eq i k⟩
  have hm := invariant g _ hmem
  rw [Matrix.add_vecMul, hshift, ← hj] at hm
  exact admissible_of_mem hm

private theorem faithful (g : matrixGroup)
    (h : modularRows * (reduction g).val = modularRows) : reduction g = 1 := by
  have hs := seed_fixed g h
  have ht : frame * (reduction g).val = frame := by
    funext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2
    · exact hs 0
    · exact hs 1
    · exact hs 2
  apply Units.ext
  change (reduction g).val = (1 : Matrix _ _ GoldenFour)
  have hh := congrArg (fun m => frameInverse * m) ht
  simpa only [← Matrix.mul_assoc, frame_inverse, Matrix.one_mul] using hh

end ModularFaithfulness

/-- Fixing the displayed three-space pointwise forces the entire reduction to be trivial. -/
theorem reduction_eq_one_of_modularRows (g : matrixGroup)
    (h : modularRows * (reduction g).val = modularRows) : reduction g = 1 :=
  ModularFaithfulness.faithful g h

/-- Restriction to the invariant three-space is faithful on the modular matrix image. -/
theorem matrixQuotient_ker_le_reduction_ker : matrixQuotient.ker ≤ reduction.ker := by
  intro g hg
  exact MonoidHom.mem_ker.mpr
    (reduction_eq_one_of_modularRows g ((matrixQuotient_mem_ker_iff g).mp hg))

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block
