module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Transfer
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Model
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Singer.TraceForm
public import Theory.FieldTheory.QuadraticFrobeniusFixed

/-!
# The full special-unitary Singer torus over the Ree coefficient field

For q = 2^(2m+1), multiplication on GF(q⁶) embeds the full group of
(q²−q+1)-st roots of unity in SU₃(q). The preceding modules construct the
literal GF(q²)-algebra, its three-dimensional regular action, and its
nondegenerate trace Hermitian form. The actual q-Frobenius has fixed field
of order q, so Huppert II.10.4 gives an orthonormal basis. Conjugating the
regular matrices by that basis realizes the action in `Three.form m`,
with its original coefficient field, identity matrix and conjugation.

`singer_subgroup` applies the exact parameter-to-subgroup transfer. The
final Ree consumer `nonempty_tori_of_special_embedding` needs only the
independent faithful embedding of this full SU₃ into Ree. No exceptional
descent, order formula or classification premise is asserted here.
In particular q=8 gives a subgroup of order 57, retaining the scalar three.

Sources: GLS3 §4.10 and §6.5, refs/KGroup/GLS3/chapter4.tex and chapter6.tex.
Theorem 6.5.3(c) motivates the order; existence is proved by the field action.
-/

@[expose] public noncomputable section

open Matrix BenderSuzuki.MatrixGroups
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary

namespace Singer

/-- The stored q-Frobenius on the literal coefficient field has q fixed elements. -/
theorem fixed_card (m : ℕ) :
    Nat.card {x : Three.QuadraticField m // (Three.form m).conj x = x} =
      2 ^ (2 * m + 1) := by
  change Nat.card (FixedBy.subfield (GaloisField 2 ((2 * m + 1) * 2))
    (iterateFrobeniusEquiv (GaloisField 2 ((2 * m + 1) * 2)) 2 (2 * m + 1))) = _
  rw [Nat.mul_comm (2 * m + 1) 2]
  exact GaloisField.card_fixedBy_quadraticFrobenius 2 (2 * m + 1) (by omega)

/-- The trace form admits an orthonormal basis over its original coefficient field. -/
theorem exists_normalizingMatrix (m : ℕ) :
    ∃ C : GL (Fin 3) (Three.QuadraticField m),
      (traceHermitianForm m).conjTranspose C.val * traceGram m * C.val = 1 :=
  BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 3 (traceHermitianForm m)
    (2 ^ (2 * m + 1)) (Three.quadraticField_card m) (fixed_card m)

/-- A chosen orthonormal basis, as a change-of-basis matrix in the regular coordinates. -/
def normalizingMatrix (m : ℕ) : GL (Fin 3) (Three.QuadraticField m) :=
  Classical.choose (exists_normalizingMatrix m)

theorem normalizingMatrix_spec (m : ℕ) :
    (traceHermitianForm m).conjTranspose (normalizingMatrix m).val * traceGram m *
      (normalizingMatrix m).val = 1 :=
  Classical.choose_spec (exists_normalizingMatrix m)

/-- The identity form after normalization is literally the Ree consumer's form. -/
theorem identityGram_eq_form (m : ℕ) :
    HermitianForm.IdentityGram.identityGram (traceHermitianForm m) = Three.form m := rfl

/-- Change of basis to the exact identity-form special unitary group. -/
def identityFormEquiv (m : ℕ) :
    (traceHermitianForm m).specialSubgroup ≃* (Three.form m).specialSubgroup :=
  HermitianForm.IdentityGram.specialEquiv (traceHermitianForm m)
    (normalizingMatrix m) (normalizingMatrix_spec m)

end Singer

/-- The faithful multiplication action, expressed in an orthonormal basis.
It is defined for all m, including the source range 1 ≤ m. -/
def singerParameterHom (m : ℕ) : SingerParameters.Group m →* (Three.form m).specialSubgroup :=
  (Singer.identityFormEquiv m).toMonoidHom.comp (Singer.regularUnitaryHom m)

theorem singerParameterHom_injective (m : ℕ) : Function.Injective (singerParameterHom m) :=
  (Singer.identityFormEquiv m).injective.comp (Singer.regularUnitaryHom_injective m)

/-- The target matrix is the explicit basis conjugate of regular multiplication. -/
theorem singerParameterHom_apply (m : ℕ) (u : SingerParameters.Group m) :
    (singerParameterHom m u : GL (Fin 3) (Three.QuadraticField m)) =
      (Singer.normalizingMatrix m)⁻¹ *
        (Singer.regularUnitaryHom m u : GL (Fin 3) (Three.QuadraticField m)) *
          Singer.normalizingMatrix m :=
  HermitianForm.IdentityGram.specialEquiv_apply (Singer.traceHermitianForm m)
    (Singer.normalizingMatrix m) (Singer.normalizingMatrix_spec m) (Singer.regularUnitaryHom m u)

/-- Existence of the requested faithful action on the literal full SU₃ model. -/
theorem exists_singer_parameter_embedding (m : ℕ) :
    ∃ f : SingerParameters.Group m →* (Three.form m).specialSubgroup, Function.Injective f :=
  ⟨singerParameterHom m, singerParameterHom_injective m⟩

/-- The actual cyclic subgroup of full Singer order, with no scalar quotient. -/
theorem singer_subgroup (m : ℕ) :
    ∃ T : Subgroup (Three.form m).specialSubgroup,
      IsCyclic T ∧ Nat.card T = SingerParameters.order m :=
  singer_subgroup_of_parameters (singerParameterHom m) (singerParameterHom_injective m)

/-- Both literal Ree tori from the independently supplied full-SU₃ embedding.
The Singer-action premise of `nonempty_tori_of_parameter_embedding` is discharged. -/
theorem nonempty_tori_of_special_embedding {m : ℕ}
    (j : (Three.form m).specialSubgroup →* Model m) (hj : Function.Injective j) :
    Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)) ∧
      Nonempty (CyclicTorusEmbedding m ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1)) :=
  nonempty_tori_of_parameter_embedding j hj (singerParameterHom m) (singerParameterHom_injective m)

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary
