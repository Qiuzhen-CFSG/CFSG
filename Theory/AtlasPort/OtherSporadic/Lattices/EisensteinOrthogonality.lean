/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinOrthogonality.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinScalar
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Eisenstein Orthogonality

Nonzero mutually Hermitian-orthogonal vectors are linearly independent over the rational Eisenstein field. Applying the Hermitian pairing to a dependence proves independence and the bound of 12 vectors.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinOrthogonality.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators

/-- The Hermitian form is scalar-linear in its second argument. -/
def eisensteinHermitianLinearRight (x : EisensteinRationalCoordinates) :
    EisensteinRationalCoordinates →ₗ[EisensteinRational] EisensteinRational where
  toFun := eisensteinHermitian x
  map_add' y z := by
    simp [eisensteinHermitian, mul_add, Finset.sum_add_distrib, smul_add]
  map_smul' a z := by
    simp only [eisensteinHermitian, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_smul_comm, RingHom.id_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Positivity of the real trace form makes the Hermitian self-pairing nonzero. -/
theorem eisensteinHermitian_self_ne_zero
    {x : EisensteinRationalCoordinates} (hx : x ≠ 0) : eisensteinHermitian x x ≠ 0 := by
  intro h
  apply hx
  apply (eisensteinBilinear_self_eq_zero x).mp
  unfold eisensteinBilinear
  rw [h]
  simp [eisensteinReal]

/-- A finite nonzero mutually Hermitian-orthogonal family is independent over
Q(omega). This uses the actual positive Hermitian form, without enumeration. -/
theorem eisenstein_orthogonal_linearIndependent
    {ι : Type*} [Fintype ι] (v : ι → EisensteinRationalCoordinates)
    (hne : ∀ i, v i ≠ 0)
    (horth : ∀ i j, i ≠ j → eisensteinHermitian (v i) (v j) = 0) :
    LinearIndependent EisensteinRational v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (eisensteinHermitianLinearRight (v i)) hc
  rw [map_sum, map_zero] at h
  simp only [map_smul, smul_eq_mul] at h
  have hs : (∑ j, c j * eisensteinHermitian (v i) (v j)) =
      c i * eisensteinHermitian (v i) (v i) := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [horth i j (Ne.symm hji), mul_zero]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  change (∑ j, c j * eisensteinHermitian (v i) (v j)) = 0 at h
  rw [hs] at h
  exact (mul_eq_zero.mp h).resolve_right (eisensteinHermitian_self_ne_zero (hne i))

/-- The scalar rank of the actual rational Eisenstein coordinate space is twelve. -/
theorem eisensteinRationalCoordinates_scalar_finrank :
    Module.finrank EisensteinRational EisensteinRationalCoordinates = 12 := by
  simp [EisensteinRationalCoordinates]

/-- There are at most twelve mutually Hermitian-orthogonal nonzero scalar lines. -/
theorem eisenstein_orthogonal_card_le_twelve
    {ι : Type*} [Fintype ι] (v : ι → EisensteinRationalCoordinates)
    (hne : ∀ i, v i ≠ 0)
    (horth : ∀ i j, i ≠ j → eisensteinHermitian (v i) (v j) = 0) :
    Fintype.card ι ≤ 12 := by
  have h := (eisenstein_orthogonal_linearIndependent v hne horth).fintype_card_le_finrank
  rwa [eisensteinRationalCoordinates_scalar_finrank] at h

end Atlas.Lattices
