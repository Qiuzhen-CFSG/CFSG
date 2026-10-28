module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.IntegralSpectrum.FiniteOrder
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Transport of the integral spectral obstruction to the reference action

The Singer matrix is annihilated by Φ₆₃: its 63rd power is one, while its
ninth and twenty-first powers have no fixed vectors, allowing cancellation
of all the other cyclotomic factors. A Singer equality for the padded action
also forces every padding vector to vanish, so the intrinsic eigenspace
contains a nonzero vector. Polynomial evaluation transports that vector
through the literal binary inclusion and the central quotient map.

The integral action is written in the original `leechBasis`. Its reduction
is conjugate to `leechModTwoRepresentation` by `leechModTwoLinearEquiv`,
which reduces lattice basis coordinates, not ambient integer coordinates.
The integral-matrix obstruction gives invertibility of Φ₆₃ after reduction
in rank less than φ(63) = 36. Applying it to the rank-24 Leech lattice proves
the unconditional Singer exclusion, independently of special-linear image
containment and the sign-kernel theorem.

Source consumer: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and
49.5, p.283. The imported ATLAS lattice basis and quotient maps retain their
attribution and license in `LICENSES/ATLAS.txt`.
-/

@[expose] public noncomputable section
open Polynomial Matrix
open Atlas.Algebra Atlas.Conway Atlas.Lattices Atlas.Codes
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long

private theorem unit_cyclotomic_of_power (n d : ℕ) (hd : d ∣ n)
    (hn : (referenceSinger ^ n - 1).det ≠ 0) :
    IsUnit (aeval referenceSinger (cyclotomic d ℤ)) := by
  have hdvd : cyclotomic d ℤ ∣ X ^ n - 1 :=
    (cyclotomic.dvd_X_pow_sub_one d ℤ).trans
      (by obtain ⟨k, rfl⟩ := hd; simpa [pow_mul] using sub_one_dvd_pow_sub_one (X ^ d : ℤ[X]) k)
  obtain ⟨p, hp⟩ := hdvd
  have he := congrArg (aeval referenceSinger) hp
  simp only [map_sub, map_pow, aeval_X, map_one, map_mul] at he
  rw [he, Matrix.det_mul] at hn
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).1)

/-- All proper cyclotomic factors can be cancelled using the ninth- and
twenty-first-power determinant tests. -/
theorem referenceSinger_cyclotomic_aeval : aeval referenceSinger (cyclotomic 63 ℤ) = 0 := by
  have hf := prod_cyclotomic_eq_X_pow_sub_one (by decide : 0 < 63) ℤ
  rw [show Nat.divisors 63 = {1,3,7,9,21,63} by decide] at hf
  simp [Finset.prod_insert] at hf
  have hfac : cyclotomic 63 ℤ *
      (cyclotomic 1 ℤ * cyclotomic 3 ℤ * cyclotomic 7 ℤ *
        cyclotomic 9 ℤ * cyclotomic 21 ℤ) = X ^ 63 - 1 := by
    rw [← hf]
    simp only [cyclotomic_one, cyclotomic_three]
    ring
  have hu := ((((unit_cyclotomic_of_power 9 1 (by decide)
      referenceSinger_ninth_sub_one_det_ne_zero).mul
    (unit_cyclotomic_of_power 9 3 (by decide)
      referenceSinger_ninth_sub_one_det_ne_zero)).mul
    (unit_cyclotomic_of_power 21 7 (by decide)
      referenceSinger_twentyFirst_sub_one_det_ne_zero)).mul
    (unit_cyclotomic_of_power 9 9 (by decide)
      referenceSinger_ninth_sub_one_det_ne_zero)).mul
    (unit_cyclotomic_of_power 21 21 (by decide)
      referenceSinger_twentyFirst_sub_one_det_ne_zero)
  have he := congrArg (aeval referenceSinger) hfac
  simp only [map_mul, map_sub, map_pow, aeval_X, map_one,
    referenceSinger_pow_sixtyThree, sub_self] at he
  exact hu.mul_right_cancel (he.trans (zero_mul _).symm)

private theorem referencePadded_fixed_eq_zero_of_singer (g : referenceCentralizer) (hg : referenceMatrixAction g = referenceSinger)
    (v : ReferencePadded) (hv : referencePaddedAction g v = v) : v = 0 := by
  have he : (referenceSinger - 1) *ᵥ referenceBasis.repr v = 0 := by
    rw [← hg, Matrix.sub_mulVec, Matrix.one_mulVec]
    change (LinearMap.toMatrix referenceBasis referenceBasis
      (referencePaddedAction g).toLinearMap) *ᵥ referenceBasis.repr v -
        referenceBasis.repr v = 0
    rw [LinearMap.toMatrix_mulVec_repr]
    change (referenceBasis.repr (referencePaddedAction g v) : Fin 3 → F) - _ = _
    rw [hv, sub_self]
  have hz := Matrix.eq_zero_of_mulVec_eq_zero referenceSinger_sub_one_det_ne_zero he
  apply referenceBasis.repr.injective
  ext i
  simpa using congrFun hz i

private theorem addHom_aeval_int {K L V W : Type*}
    [Field K] [Field L] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module L W]
    (f : V →+ W) (T : Module.End K V) (U : Module.End L W)
    (h : ∀ v, f (T v) = U (f v)) (p : ℤ[X]) (v : V) :
    f (aeval T p v) = aeval U p (f v) := by
  have hp (n : ℕ) (w : V) : f ((T ^ n) w) = (U ^ n) (f w) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, h, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n z =>
    simpa [aeval_monomial, algebraMap_int_eq, Module.End.mul_apply] using
      congrArg (fun w : W => z • w) (hp n v)

/-- A Singer matrix equality eliminates every trivial padding coordinate. -/
theorem referencePadding_eq_zero_of_singer (g : referenceCentralizer) (hg : referenceMatrixAction g = referenceSinger)
    (v : ReferencePadding) : v = 0 := by
  exact congrArg Prod.snd (referencePadded_fixed_eq_zero_of_singer g hg (0, v) (by
    change ((referenceEigenAction referenceScalar g) 0, v) = (0, v)
    rw [map_zero]))

private theorem referenceNatural_nonzero_of_singer (g : referenceCentralizer) (hg : referenceMatrixAction g = referenceSinger) :
    ∃ v : ReferenceNatural, v ≠ 0 := by
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F)
    (M := ReferencePadded)).mp (by rw [referencePadded_finrank]; decide)
  refine ⟨v.1, fun hz => hv ?_⟩
  exact Prod.ext hz (referencePadding_eq_zero_of_singer g hg v.2)

private theorem referencePadded_cyclotomic_aeval_of_singer (g : referenceCentralizer) (hg : referenceMatrixAction g = referenceSinger) :
    aeval (referencePaddedAction g).toLinearMap (cyclotomic 63 ℤ) = 0 := by
  apply (LinearMap.toMatrixAlgEquiv referenceBasis).injective
  rw [map_zero]
  have he := aeval_algHom_apply
    ((LinearMap.toMatrixAlgEquiv referenceBasis).restrictScalars ℤ)
    (referencePaddedAction g).toLinearMap (cyclotomic 63 ℤ)
  change aeval (referenceMatrixAction g) (cyclotomic 63 ℤ) = _ at he
  rw [hg, referenceSinger_cyclotomic_aeval] at he
  exact he.symm

private theorem referenceNatural_cyclotomic_aeval_of_singer (g : referenceCentralizer) (hg : referenceMatrixAction g = referenceSinger)
    (v : ReferenceNatural) :
    aeval (referenceEigenAction referenceScalar g).toLinearMap (cyclotomic 63 ℤ) v = 0 := by
  have he := addHom_aeval_int (LinearMap.fst F ReferenceNatural ReferencePadding).toAddMonoidHom
    (referencePaddedAction g).toLinearMap
    (referenceEigenAction referenceScalar g).toLinearMap
    (fun _ => rfl) (cyclotomic 63 ℤ) (v, 0)
  rw [referencePadded_cyclotomic_aeval_of_singer g hg] at he
  exact he.symm

private def naturalToBinary : ReferenceNatural →+ LeechModTwo where
  toFun v := v.val.val
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A Singer equality produces a nonzero Φ₆₃-kernel vector for any actual
integral lift, using exactly the published central quotient and binary action. -/
theorem referenceSinger_lift_cyclotomic_kernel (g : referenceCentralizer) (hg : referenceMatrixAction g = referenceSinger)
    (k : LeechIsometryGroup) (hk : leechCentralProjection k = g.val) :
    ∃ v : LeechModTwo, v ≠ 0 ∧
      aeval (leechModTwoRepresentation k).toLinearMap (cyclotomic 63 ℤ) v = 0 := by
  obtain ⟨v, hv⟩ := referenceNatural_nonzero_of_singer g hg
  refine ⟨naturalToBinary v, ?_, ?_⟩
  · intro hz
    apply hv
    exact Subtype.ext (Subtype.ext hz)
  · have he := addHom_aeval_int naturalToBinary
      (referenceEigenAction referenceScalar g).toLinearMap
      (leechModTwoRepresentation k).toLinearMap (fun w => by
        change quotientModTwoRepresentation g.val w.val.val =
          leechModTwoRepresentation k w.val.val
        rw [← hk, quotientModTwoRepresentation_compatible]) (cyclotomic 63 ℤ) v
    rw [referenceNatural_cyclotomic_aeval_of_singer g hg, map_zero] at he
    exact he.symm

/-- Injectivity on the actual reduced lattice action excludes the Singer matrix. -/
theorem referenceSingerExcluded_of_integral_cyclotomic_injective
    (hint : ∀ k : LeechIsometryGroup, Function.Injective
      (aeval (leechModTwoRepresentation k).toLinearMap (cyclotomic 63 ℤ))) :
    ReferenceSingerExcluded := by
  intro g hg
  obtain ⟨k, hk⟩ := leechCentralProjection_surjective g.val
  obtain ⟨v, hv, he⟩ := referenceSinger_lift_cyclotomic_kernel g hg k hk
  exact hv (hint k (he.trans (map_zero _).symm))

private def integralLeechMatrix : LeechIsometryGroup →* Matrix Omega Omega ℤ :=
  (LinearMap.toMatrixAlgEquiv leechBasis).toMonoidHom.comp
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp leechIsometries.subtype)

private theorem integralLeechMatrix_finite (g : LeechIsometryGroup) :
    IsOfFinOrder (integralLeechMatrix g) := by
  exact integralLeechMatrix.isOfFinOrder (isOfFinOrder_of_finite g)

private theorem binary_coordinates_reduce (x : leech) :
    leechModTwoLinearEquiv (leechReduction x) =
      fun i => (leechBasis.repr x i : Bit) := rfl

private theorem integralLeechMatrix_reduction (g : LeechIsometryGroup) (v : LeechModTwo) :
    leechModTwoLinearEquiv (leechModTwoRepresentation g v) =
      (integralLeechMatrix g).map (Int.castRingHom Bit) *ᵥ leechModTwoLinearEquiv v := by
  obtain ⟨x, rfl⟩ := leechReduction_surjective v
  rw [leechModTwoRepresentation_reduce, binary_coordinates_reduce, binary_coordinates_reduce]
  have he := LinearMap.toMatrix_mulVec_repr leechBasis leechBasis g.val.toLinearMap x
  change (integralLeechMatrix g) *ᵥ (fun i => leechBasis.repr x i) =
    (fun i => leechBasis.repr (g.val x) i) at he
  ext i
  exact (congrArg (fun v : Omega → ℤ => (v i : Bit)) he.symm).trans
    ((Int.castRingHom Bit).map_mulVec _ _ _)

/-- Apply a finite-order integral-matrix obstruction through the original
lattice basis and its exact reduction modulo twice the lattice. -/
theorem leech_cyclotomic_injective_of_integralMatrix
    (hint : ∀ A : Matrix Omega Omega ℤ, IsOfFinOrder A →
      IsUnit (aeval (A.map (Int.castRingHom Bit)) (cyclotomic 63 ℤ)))
    (g : LeechIsometryGroup) :
    Function.Injective (aeval (leechModTwoRepresentation g).toLinearMap (cyclotomic 63 ℤ)) := by
  let A := (integralLeechMatrix g).map (Int.castRingHom Bit)
  have hu := (hint (integralLeechMatrix g) (integralLeechMatrix_finite g)).map
    Matrix.toLinAlgEquiv'.toMonoidHom
  have he := aeval_algHom_apply (Matrix.toLinAlgEquiv'.restrictScalars ℤ) A
    (cyclotomic 63 ℤ)
  change aeval (Matrix.toLinAlgEquiv' A) (cyclotomic 63 ℤ) =
    Matrix.toLinAlgEquiv' (aeval A (cyclotomic 63 ℤ)) at he
  change IsUnit (Matrix.toLinAlgEquiv' (aeval A (cyclotomic 63 ℤ))) at hu
  rw [← he] at hu
  have hi := LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hu)
  intro v w hvw
  apply leechModTwoLinearEquiv.injective
  apply hi
  have hv := addHom_aeval_int leechModTwoLinearEquiv.toAddMonoidHom
    (leechModTwoRepresentation g).toLinearMap (Matrix.toLinAlgEquiv' A)
    (integralLeechMatrix_reduction g) (cyclotomic 63 ℤ) v
  have hw := addHom_aeval_int leechModTwoLinearEquiv.toAddMonoidHom
    (leechModTwoRepresentation g).toLinearMap (Matrix.toLinAlgEquiv' A)
    (integralLeechMatrix_reduction g) (cyclotomic 63 ℤ) w
  exact hv.symm.trans ((congrArg leechModTwoLinearEquiv hvw).trans hw)

/-- The general matrix premise suffices for the literal reference
centralizer action; it requires no special-linear image or sign-kernel input. -/
theorem referenceSingerExcluded_of_integralMatrix_cyclotomic_unit
    (hint : ∀ A : Matrix Omega Omega ℤ, IsOfFinOrder A →
      IsUnit (aeval (A.map (Int.castRingHom Bit)) (cyclotomic 63 ℤ))) :
    ReferenceSingerExcluded :=
  referenceSingerExcluded_of_integral_cyclotomic_injective (leech_cyclotomic_injective_of_integralMatrix hint)

/-- The rank-24 integral Leech action excludes the Singer matrix from the
actual padded eigenspace action of the full reference centralizer. This
discharges the integral premise of
`referenceEigenAction_det_of_block_and_integral_obstruction`. -/
theorem referenceSingerExcluded : ReferenceSingerExcluded := by
  apply referenceSingerExcluded_of_integralMatrix_cyclotomic_unit
  intro A hA
  exact integralMatrix_cyclotomic63_isUnit A hA (by decide)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
