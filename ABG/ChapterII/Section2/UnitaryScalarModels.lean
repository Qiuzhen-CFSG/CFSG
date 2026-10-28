module
public import ABG.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Norm-one scalars in the actual GU2 model

A scalar matrix preserves the standard Hermitian form exactly when its
scalar has norm one, equivalently its `(p^n+1)`-st power is one. Thus the
corresponding roots of unity embed as a central subgroup of the existing
`GU2 p n hn`. This constructs the actual scalar factors used in ABG
Chapter II, Section 2, article pages 16-17 and Lemma 1(v).

The conjugate transpose of a scalar matrix is the q-Frobenius scalar.
The Hermitian equation therefore reduces to the scalar norm equation;
injectivity of scalar matrices gives the reverse implication. Restricting
the existing GL2 scalar homomorphism then supplies the embedding,
injectivity, and centrality. The original field, Frobenius involution,
and unitary subgroup instances are retained. No special-unitary/special-
linear identification or scalar-subgroup cardinality is assumed.
-/

namespace ABG

open Matrix.GeneralLinearGroup

public theorem scalar_mem_GU2_iff
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (c : (GaloisField p (2 * n))ˣ) :
    scalar (Fin 2) c ∈ (unitaryForm 2 p n hn).unitarySubgroup ↔
      c ^ (p ^ n + 1) = 1 := by
  rw [(unitaryForm 2 p n hn).mem_unitarySubgroup_iff]
  have hconj :
      (unitaryForm 2 p n hn).conjTranspose
        ((scalar (Fin 2) c : GL (Fin 2) (GaloisField p (2 * n))) :
          Matrix (Fin 2) (Fin 2) (GaloisField p (2 * n))) =
      Matrix.scalar (Fin 2) ((c : GaloisField p (2 * n)) ^ (p ^ n)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [unitaryForm, BenderSuzuki.MatrixGroups.HermitianForm.conjTranspose,
        coe_scalar, Matrix.scalar_apply, iterateFrobenius_def]
    · simp [unitaryForm, BenderSuzuki.MatrixGroups.HermitianForm.conjTranspose,
        coe_scalar, Matrix.scalar_apply, hij, Ne.symm hij]
  rw [hconj]
  change Matrix.scalar (Fin 2) ((c : GaloisField p (2 * n)) ^ (p ^ n)) * 1 *
    Matrix.scalar (Fin 2) (c : GaloisField p (2 * n)) = 1 ↔ _
  rw [mul_one, ← map_mul, ← map_one (Matrix.scalar (Fin 2)), Matrix.scalar_inj]
  rw [← pow_succ]
  exact (Units.val_injective.eq_iff (a := c ^ (p ^ n + 1)) (b := 1))

public noncomputable def GU2Scalar
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    rootsOfUnity (p ^ n + 1) (GaloisField p (2 * n)) →* GU2 p n hn :=
  { toFun c := ⟨scalar (Fin 2) c.val, (scalar_mem_GU2_iff p n hn c.val).mpr c.property⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' a b := Subtype.ext (map_mul _ a.val b.val) }

public theorem GU2Scalar_apply_val
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (c : rootsOfUnity (p ^ n + 1) (GaloisField p (2 * n))) :
    (GU2Scalar p n hn c).val = scalar (Fin 2) c.val := by rfl

public theorem GU2Scalar_injective
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Function.Injective (GU2Scalar p n hn) := by
  intro a b h
  apply Subtype.ext
  apply Units.ext
  have h' := congrArg (fun A : GU2 p n hn => A.val.val 0 0) h
  simpa [GU2Scalar, coe_scalar, Matrix.scalar_apply] using h'

public theorem GU2Scalar_range_le_center
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    (GU2Scalar p n hn).range ≤ Subgroup.center (GU2 p n hn) := by
  rintro A ⟨c, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro B
  apply Subtype.ext
  exact (scalar_commute c.val B.val).symm

end ABG
