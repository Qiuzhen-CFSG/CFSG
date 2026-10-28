module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.OctonionPair.Automorphisms
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
public import Theory.Representation.G2NaturalSemilinear

/-!
# A Frobenius-compatible octonion pair for the Hall--Janko presentation

We construct explicit elements `x` and `y` of the literal split-octonion
model over `GaloisField 2 2`. They satisfy all five ATLAS J2G1-P2 relators;
`x` is nonidentity and fixed by coefficient Frobenius, while Frobenius sends
`y` to its inverse. The universal presentation map is applied to this pair.

The proof checks matrices over the computable quadratic field of four elements,
then transports along a genuine ring equivalence. The faithful coordinate
matrix representation identifies field transport with entrywise transport;
ring homomorphisms preserve squares, giving exactly the specified Frobenius.

This supplies the octonion input to `InnerRealization.markedOfRelations` for
Aschbacher--Smith K.4.5, printed p.460/PDF p.471. Presentation exactness and
final marked-embedding assembly remain with that consumer. No presentation
injectivity, carrier simplicity, or module recognition is assumed here.

Sources, original witness data, and ATLAS attribution/license are preserved in
`InnerRealization/source/README.md` and `OctonionPair/source/README.md`.
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.OctonionPair
open Atlas.G2.Natural.BinarySemilinear

theorem coeff_relations : Presentation.Relations a b := by
  intro i
  fin_cases i
  · change a ^ 2 = 1
    apply matrixHom_injective
    simpa only [map_pow, map_one, matrixHom_a] using MatrixCertificates.aMatrix_sq
  · change b ^ 3 = 1
    apply matrixHom_injective
    simpa only [map_pow, map_one, matrixHom_b] using MatrixCertificates.bMatrix_cube
  · change (a * b) ^ 7 = 1
    apply matrixHom_injective
    simpa only [map_pow, map_mul, map_one, matrixHom_a, matrixHom_b] using
      MatrixCertificates.ab_seventh
  · change (a⁻¹ * b⁻¹ * a * b) ^ 12 = 1
    apply matrixHom_injective
    simpa only [map_pow, map_mul, map_one, matrixHom_a, matrixHom_b,
      matrixHom_a_inv, matrixHom_b_inv] using MatrixCertificates.commutator_twelfth
  · change Presentation.longWord a b ^ 6 = 1
    apply matrixHom_injective
    simpa only [Presentation.longWord, map_pow, map_mul, map_one, matrixHom_a,
      matrixHom_b, matrixHom_b_inv] using MatrixCertificates.longWord_sixth

/-- A genuine ring equivalence, obtained from the two checked cardinalities. -/
noncomputable def coeffEquiv : Coeff ≃+* GaloisField 2 2 := by
  letI := Fintype.ofFinite (GaloisField 2 2)
  exact FiniteField.ringEquivOfCardEq (by
    rw [coeff_card, ← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
    norm_num)

/-- The short-root matrix, transported to the specified G₂(4) carrier. -/
noncomputable def x : Atlas.G2.Model (GaloisField 2 2) := Atlas.G2.fieldEquiv coeffEquiv a

/-- The displayed order-three matrix, transported to the specified carrier. -/
noncomputable def y : Atlas.G2.Model (GaloisField 2 2) := Atlas.G2.fieldEquiv coeffEquiv b

theorem relations : Presentation.Relations x y := by
  intro i
  change Presentation.relatorValues ((Atlas.G2.fieldEquiv coeffEquiv).toMonoidHom a)
    ((Atlas.G2.fieldEquiv coeffEquiv).toMonoidHom b) i = 1
  rw [← Presentation.map_relatorValues (Atlas.G2.fieldEquiv coeffEquiv).toMonoidHom,
    coeff_relations i, map_one]

theorem x_ne_one : x ≠ 1 := by
  intro h
  apply a_ne_one
  apply (Atlas.G2.fieldEquiv coeffEquiv).injective
  rw [map_one]
  change (Atlas.G2.fieldEquiv coeffEquiv) a = 1 at h
  exact h

/-- Field transport commutes with squaring, independent of the chosen field isomorphism. -/
theorem coeffEquiv_square (c : Coeff) : coeffEquiv (c ^ 2) = fourFrobenius (coeffEquiv c) :=
  map_pow coeffEquiv c 2

theorem x_frobenius : x = Atlas.G2.fieldEquiv fourFrobenius x := by
  apply matrixHom_injective
  simp only [x, matrixHom_fieldEquiv, matrixHom_a]
  ext i j
  change coeffEquiv (aMatrix i j) = fourFrobenius (coeffEquiv (aMatrix i j))
  rw [← coeffEquiv_square, aMatrix_square_entry]

theorem y_inv_frobenius : y⁻¹ = Atlas.G2.fieldEquiv fourFrobenius y := by
  apply matrixHom_injective
  rw [y, ← map_inv, matrixHom_fieldEquiv, matrixHom_fieldEquiv, matrixHom_fieldEquiv,
    matrixHom_b_inv, matrixHom_b]
  ext i j
  change coeffEquiv (bInvMatrix i j) = fourFrobenius (coeffEquiv (bMatrix i j))
  rw [← coeffEquiv_square, bMatrix_square_entry]

/-- Actual application to the existing universal presentation map. -/
noncomputable def toOctonions : Presentation.UniversalGroup →* Atlas.G2.Model (GaloisField 2 2) :=
  Presentation.toGroup x y relations

@[simp] theorem toOctonions_zero : toOctonions (PresentedGroup.of 0) = x :=
  Presentation.toGroup_zero _ _ _

@[simp] theorem toOctonions_one : toOctonions (PresentedGroup.of 1) = y :=
  Presentation.toGroup_one _ _ _

theorem exists_pair : ∃ x y : Atlas.G2.Model (GaloisField 2 2),
    Presentation.Relations x y ∧ x ≠ 1 ∧ x = Atlas.G2.fieldEquiv fourFrobenius x ∧
      y⁻¹ = Atlas.G2.fieldEquiv fourFrobenius y :=
  ⟨x, y, relations, x_ne_one, x_frobenius, y_inv_frobenius⟩

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.OctonionPair
