module

public import Theory.Character.ModularBlock.BlockConjugationTrace
public import Theory.Character.ModularBlock.CharacterProjectorDefs
public import Theory.Character.ModularBlock.ResidueKernel
public import Theory.LinearAlgebra.Matrix.IdempotentLift
public import Theory.Representation.IntegralPermutationTrace
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Integral matrices for the Brauer conjugation trace

Right multiplication by a central idempotent is an idempotent matrix
commuting with the permutation of the group basis induced by conjugation.
Its fixed-basis submatrix is the multiplication matrix of the centralizer
restriction after reduction. These statements supply the group-algebra
interface to the integral permutation-summand trace comparison.

The integral permutation-summand theorem compares the conjugation trace with
the trace of an idempotent lifting the fixed-basis matrix. Applying the
complex coefficient embedding gives the Brauer conjugation-trace comparison,
with exact equality rather than merely equality after reduction.

Source application: Fong, *Some Sylow subgroups of order 32 and a
characterization of U(3,3)*, J. Algebra 6 (1967), p. 71, equation (6),
citing Brauer--Suzuki, Section I.
-/

public section
noncomputable section

namespace ModularBlock.BrauerConjugationTrace

open scoped BigOperators
open PrincipalBlockConstruction BrauerBlockReduction
attribute [local instance] Fintype.ofFinite

variable {G R : Type*} [Group G] [Finite G] [CommRing R]

/-- The matrix of right multiplication in the group basis. -/
@[expose] def rightMatrix (e : MonoidAlgebra R G) : Matrix G G R :=
  fun i j => e.coeff (j⁻¹ * i)

/-- The coefficient formula agrees with the canonical group-algebra basis. -/
theorem rightMatrix_eq_toMatrix [DecidableEq G] (e : MonoidAlgebra R G) :
    rightMatrix e = LinearMap.toMatrix (MonoidAlgebra.basis G R)
      (MonoidAlgebra.basis G R) (LinearMap.mulRight R e) := by
  classical
  ext i j
  simp only [LinearMap.toMatrix_apply, LinearMap.mulRight_apply]
  change e.coeff (j⁻¹ * i) = (MonoidAlgebra.single j 1 * e).coeff i
  simp

/-- An idempotent group-algebra element gives an idempotent matrix. -/
theorem rightMatrix_isIdempotent (e : MonoidAlgebra R G)
    (he : IsIdempotentElem e) : IsIdempotentElem (rightMatrix e) := by
  classical
  have hp : IsIdempotentElem (LinearMap.mulRight R e) := by
    change (LinearMap.mulRight R e).comp (LinearMap.mulRight R e) = _
    rw [← LinearMap.mulRight_mul, he]
  rw [rightMatrix_eq_toMatrix]
  exact hp.map (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G R))

/-- Conjugation acts as a permutation of the canonical group basis. -/
@[expose] def conjugationPerm (y : G) : Equiv.Perm G :=
  (MulAut.conj y).toEquiv

omit [Finite G] in
@[simp] theorem conjugationPerm_apply (y x : G) :
    conjugationPerm y x = y * x * y⁻¹ := rfl

omit [Finite G] in
/-- The conjugation permutation has two-power order when the element does. -/
theorem conjugationPerm_pow_eq_one (y : G) {n : ℕ}
    (hy : y ^ (2 ^ n) = 1) : conjugationPerm y ^ (2 ^ n) = 1 := by
  change (MulAut.toPerm G (MulAut.conj y)) ^ (2 ^ n) = 1
  rw [← map_pow, ← map_pow, hy, map_one, map_one]

omit [Finite G] in
/-- Fixed group-basis vectors are precisely the centralizer elements. -/
theorem conjugationPerm_fixed_iff (y x : G) :
    conjugationPerm y x = x ↔ x ∈ Subgroup.centralizer ({y} : Set G) := by
  rw [conjugationPerm_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (fun z => z * y) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h'.symm
  · intro h
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]

omit [Finite G] in
/-- Centrality gives simultaneous conjugation invariance of matrix entries. -/
theorem rightMatrix_conjugation_invariant (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) (y i j : G) :
    rightMatrix e (conjugationPerm y i) (conjugationPerm y j) =
      rightMatrix e i j := by
  dsimp [rightMatrix, conjugationPerm]
  have harg : (y * j * y⁻¹)⁻¹ * (y * i * y⁻¹) = y * (j⁻¹ * i) * y⁻¹ := by
    group
  change e.coeff ((y * j * y⁻¹)⁻¹ * (y * i * y⁻¹)) = _
  rw [harg]
  exact CentralIdempotentSupport.coeff_conj_eq_of_mem_center e he y (j⁻¹ * i)

/-- Right multiplication by a central element commutes with the
permutation matrix for conjugation. -/
theorem rightMatrix_commute_conjugation [DecidableEq G]
    (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) (y : G) :
    Commute ((conjugationPerm y).permMatrix R) (rightMatrix e) := by
  change (conjugationPerm y).permMatrix R * rightMatrix e =
    rightMatrix e * (conjugationPerm y).permMatrix R
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simpa only [Equiv.apply_symm_apply, Matrix.submatrix_apply, id_eq] using
    rightMatrix_conjugation_invariant e he y i ((conjugationPerm y).symm j)

omit [Finite G] in
/-- The inverse conjugation permutation has the same fixed basis. -/
theorem conjugationPerm_inv_fixed_iff (y x : G) :
    conjugationPerm y⁻¹ x = x ↔ x ∈ Subgroup.centralizer ({y} : Set G) := by
  rw [conjugationPerm_fixed_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa only [inv_inv] using (show Commute x y⁻¹ from h).inv_right.eq
  · intro h
    exact (show Commute x y from h).inv_right.eq

/-- The row-permutation convention for `permMatrix` computes the
conjugation trace at the inverse element. -/
theorem trace_permMatrix_mul_rightMatrix [DecidableEq G]
    (e : MonoidAlgebra R G) (y : G) :
    Matrix.trace ((conjugationPerm y).permMatrix R * rightMatrix e) =
      LinearMap.trace R (MonoidAlgebra R G)
        (BlockConjugationTrace.projectedConjugation e y⁻¹) := by
  rw [BlockConjugationTrace.trace_projectedConjugation]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply,
    rightMatrix, conjugationPerm_apply, id_eq, inv_inv, mul_assoc]

omit [Finite G] in
/-- Right multiplication commutes with coefficient extension. -/
theorem rightMatrix_mapRingHom {S : Type*} [CommRing S]
    (f : R →+* S) (e : MonoidAlgebra R G) :
    rightMatrix (MonoidAlgebra.mapRingHom G f e) = (rightMatrix e).map f := by
  ext i j
  simp [rightMatrix]

/-- Matrix trace recovers the regular projection trace. -/
theorem trace_rightMatrix (e : MonoidAlgebra R G) :
    Matrix.trace (rightMatrix e) =
      LinearMap.trace R (MonoidAlgebra R G) (LinearMap.mulRight R e) := by
  classical
  rw [rightMatrix_eq_toMatrix,
    LinearMap.trace_eq_matrix_trace R (MonoidAlgebra.basis G R)]

/-- The coefficientwise Brauer hypothesis gives the actual reduced
fixed-basis submatrix, rather than just its trace. -/
theorem rightMatrix_centralizer_reduce
    (d : PrincipalCongruenceBlockData G) (y : G)
    (e : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
    (b : MonoidAlgebra (Localization.AtPrime d.primeIdeal)
      (Subgroup.centralizer ({y} : Set G)))
    (h : ∀ x : Subgroup.centralizer ({y} : Set G),
      localizationToResidue d (b.coeff x) =
        localizationToResidue d (e.coeff (x : G))) :
    (rightMatrix b).map (localizationToResidue d) =
      ((rightMatrix e).map (localizationToResidue d)).submatrix
        (fun x : Subgroup.centralizer ({y} : Set G) => (x : G))
        (fun x : Subgroup.centralizer ({y} : Set G) => (x : G)) := by
  ext i j
  exact h (j⁻¹ * i)

/-- Two integral group-algebra idempotents with equal reductions have
exactly equal ordinary projection traces after complex extension. -/
theorem projection_trace_eq_of_reduce_eq
    (d : PrincipalCongruenceBlockData G)
    (e b : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
    (he : IsIdempotentElem e) (hb : IsIdempotentElem b)
    (h : ∀ x : G, localizationToResidue d (e.coeff x) =
      localizationToResidue d (b.coeff x)) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
      (LinearMap.mulRight ℂ (MonoidAlgebra.mapRingHom G
        (IsotypicLattice.localizationToComplex d) e)) =
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
      (LinearMap.mulRight ℂ (MonoidAlgebra.mapRingHom G
        (IsotypicLattice.localizationToComplex d) b)) := by
  classical
  have hf (r : Localization.AtPrime d.primeIdeal)
      (hr : localizationToResidue d r ≠ 0) : IsUnit r := by
    by_contra hn
    exact hr ((BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit d r).mpr hn)
  have hm : (localizationToResidue d).mapMatrix (rightMatrix e) =
      (localizationToResidue d).mapMatrix (rightMatrix b) := by
    ext i j
    exact h (j⁻¹ * i)
  have ht := Matrix.trace_eq_of_idempotent_map_eq (localizationToResidue d) hf
    (rightMatrix e) (rightMatrix b) (rightMatrix_isIdempotent e he)
    (rightMatrix_isIdempotent b hb) hm
  rw [← trace_rightMatrix, ← trace_rightMatrix, rightMatrix_mapRingHom,
    rightMatrix_mapRingHom, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace, ht]

/-- The integral Brauer trace comparison for an idempotent and a lift of its
centralizer restriction. Only the ambient idempotent needs to be central. -/
theorem integral_conjugation_trace_eq
    (d : PrincipalCongruenceBlockData G) (y : G)
    (hy : ∃ n : ℕ, y ^ (2 ^ n) = 1)
    (e : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
    (b : MonoidAlgebra (Localization.AtPrime d.primeIdeal)
      (Subgroup.centralizer ({y} : Set G)))
    (he : IsIdempotentElem e) (hec : e ∈ Set.center (MonoidAlgebra _ G))
    (hb : IsIdempotentElem b)
    (h : ∀ x : Subgroup.centralizer ({y} : Set G),
      localizationToResidue d (b.coeff x) =
        localizationToResidue d (e.coeff (x : G))) :
    LinearMap.trace (Localization.AtPrime d.primeIdeal)
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
      (BlockConjugationTrace.projectedConjugation e y) =
    LinearMap.trace (Localization.AtPrime d.primeIdeal)
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal)
        (Subgroup.centralizer ({y} : Set G)))
      (LinearMap.mulRight (Localization.AtPrime d.primeIdeal) b) := by
  classical
  let : Fintype (Subgroup.centralizer ({y} : Set G)) := Fintype.ofFinite _
  let : Field (principalResidueField d) := Ideal.Quotient.field d.primeIdeal
  obtain ⟨n, hn⟩ := hy
  have hsurj : Function.Surjective (localizationToResidue d) := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap _ (Localization.AtPrime d.primeIdeal) a,
      localizationToResidue_algebraMap d a⟩
  have hf (r : Localization.AtPrime d.primeIdeal)
      (hr : localizationToResidue d r ≠ 0) : IsUnit r := by
    by_contra hn
    exact hr ((BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit d r).mpr hn)
  let q : {x // conjugationPerm y⁻¹ x = x} ≃
      Subgroup.centralizer ({y} : Set G) :=
    Equiv.subtypeEquivRight (conjugationPerm_inv_fixed_iff y)
  let B := (rightMatrix b).submatrix q q
  have hB : IsIdempotentElem B := by
    change (rightMatrix b).submatrix q q * (rightMatrix b).submatrix q q =
      (rightMatrix b).submatrix q q
    rw [Matrix.submatrix_mul_equiv, (rightMatrix_isIdempotent b hb).eq]
  have hBmap : (localizationToResidue d).mapMatrix B =
      ((localizationToResidue d).mapMatrix (rightMatrix e)).submatrix
        Subtype.val Subtype.val := by
    ext i j
    exact h ((q j)⁻¹ * q i)
  have hσ := conjugationPerm_pow_eq_one y⁻¹ (n := n)
    (by simp only [inv_pow, hn, inv_one])
  have ht := Matrix.trace_permMatrix_mul_eq_trace_fixed_lift
    (localizationToResidue d) hsurj hf (conjugationPerm y⁻¹) hσ
    (rightMatrix e) (rightMatrix_isIdempotent e he)
    (rightMatrix_commute_conjugation e hec y⁻¹) B hB hBmap
  have htrace : Matrix.trace B = Matrix.trace (rightMatrix b) :=
    Fintype.sum_equiv q _ _ (fun _ => rfl)
  rw [trace_permMatrix_mul_rightMatrix, inv_inv, htrace] at ht
  exact ht.trans (trace_rightMatrix b)

/-- The characteristic-zero Brauer conjugation trace equals the regular
projection trace of any integral idempotent lifting the centralizer reduction.
This follows from integral permutation summands, without an orthogonality
or decomposition-matrix hypothesis. -/
theorem conjugation_trace_eq
    (d : PrincipalCongruenceBlockData G) (y : G)
    (hy : ∃ n : ℕ, y ^ (2 ^ n) = 1)
    (e : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
    (b : MonoidAlgebra (Localization.AtPrime d.primeIdeal)
      (Subgroup.centralizer ({y} : Set G)))
    (he : IsIdempotentElem e) (hec : e ∈ Set.center (MonoidAlgebra _ G))
    (hb : IsIdempotentElem b)
    (h : ∀ x : Subgroup.centralizer ({y} : Set G),
      localizationToResidue d (b.coeff x) =
        localizationToResidue d (e.coeff (x : G))) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
      (BlockConjugationTrace.projectedConjugation
        (MonoidAlgebra.mapRingHom G (IsotypicLattice.localizationToComplex d) e) y) =
    LinearMap.trace ℂ (MonoidAlgebra ℂ (Subgroup.centralizer ({y} : Set G)))
      (LinearMap.mulRight ℂ (MonoidAlgebra.mapRingHom _
        (IsotypicLattice.localizationToComplex d) b)) := by
  have ht := congrArg (IsotypicLattice.localizationToComplex d)
    (integral_conjugation_trace_eq d y hy e b he hec hb h)
  rw [BlockConjugationTrace.trace_projectedConjugation, ← trace_rightMatrix] at ht ⊢
  simpa only [map_sum, MonoidAlgebra.coeff_mapRingHom, rightMatrix_mapRingHom,
    AddMonoidHom.map_trace] using ht

end ModularBlock.BrauerConjugationTrace
