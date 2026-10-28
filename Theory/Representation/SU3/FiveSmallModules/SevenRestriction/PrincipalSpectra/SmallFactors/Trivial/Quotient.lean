module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Trivial.Certificate
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Trivial.Actors
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.ActorCoverage

/-!
# Seven-spectra on the literal augmentation quotient

The existing realization supplies coordinates from augmentation/middleSpace
to twenty-dimensional column space. Conjugating the actual quotient action
through this equivalence identifies the two generators, hence a³bab, with
the checked binary matrices after scalar transport to the original field.
Characteristic polynomials commute with the prime-field map. The six checked
powers and the existing Sylow actor-coverage theorem give the polynomial for
every actual order-seven group element. No alternate diagnostic factor is used.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open Matrix Polynomial
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Trivial
open Degrees.TrivialCalculation
open Degrees.TrivialCalculation.MiddleFactors
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
universe v
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
attribute [local irreducible] binaryWord factor20
attribute [local irreducible] sevenPolynomial sevenSpectrum
private theorem polynomial_map {R S : Type*} [Field R] [Field S] (f : R →+* S) :
    (sevenPolynomial R).map f = sevenPolynomial S := by
  simp only [sevenPolynomial, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_one]
private theorem spectrum_map {R S : Type*} [Field R] [Field S] (f : R →+* S) (d : ℕ) :
    (sevenSpectrum R d).map f = sevenSpectrum S d := by
  unfold sevenSpectrum
  have hl : (sevenPolynomial R ^ 3).map f = sevenPolynomial S ^ 3 :=
    (Polynomial.map_pow f 3).trans (congrArg (fun p : S[X] => p ^ 3) (polynomial_map f))
  have hx : ((X : R[X]) - C 1).map f = (X : S[X]) - C 1 :=
    (Polynomial.map_sub f).trans (congrArg₂ (fun p q : S[X] => p - q)
      (Polynomial.map_X f) ((Polynomial.map_C f).trans (congrArg Polynomial.C (map_one f))))
  have hr : (((X : R[X]) - C 1) ^ (d - 18)).map f = ((X : S[X]) - C 1) ^ (d - 18) :=
    (Polynomial.map_pow f (d - 18)).trans (congrArg (fun p : S[X] => p ^ (d - 18)) hx)
  exact (Polynomial.map_mul f).trans (congrArg₂ (fun p q : S[X] => p * q) hl hr)

variable (K : Type v) [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
private theorem cast_pow_charpoly (M : Matrix (Fin 20) (Fin 20) (ZMod 2)) (n : ℕ) :
    ((CycleCertificate.castMatrix K M) ^ n).charpoly =
      ((M ^ n).charpoly).map (ZMod.castHom (dvd_refl 2) K) := by
  rw [← map_pow]
  exact Matrix.charpoly_map _ _

omit [Finite K] in
theorem cast_binaryWord_power_charpoly (k : Fin 6) :
    ((CycleCertificate.castMatrix K binaryWord) ^ (k.val + 1)).charpoly = sevenSpectrum K 20 := by
  have hs := spectrum_map (ZMod.castHom (dvd_refl 2) K) 20
  exact (cast_pow_charpoly K binaryWord (k.val + 1)).trans
    ((congrArg (Polynomial.map (ZMod.castHom (dvd_refl 2) K))
      (binaryWord_power_charpoly k)).trans hs)

noncomputable def quotientCoordinates : Coordinates K :=
  Realization.coordinates K (Classical.choice Realization.coset_enumeration)
    Twenty.canonical_borel_coset_card
    ((Classical.choice Realization.coset_enumeration).generates_of_borel
      Twenty.canonical_borel_coset_card Realization.tableBorel_le_generated)

variable {K}
noncomputable def coordinateAction (c : Coordinates K) :
    CanonicalGroup →* Matrix (Fin 20) (Fin 20) K :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp
    (c.upper.conjRingEquiv.toMonoidHom.comp (within c.space augmentationKernel).quotientRepresentation)

omit [Finite K] in
theorem coordinateAction_actor (c : Coordinates K) (j : Fin 2) :
    coordinateAction c (c.actors j) = CycleCertificate.castMatrix K (factor20 j) := by
  apply Matrix.toLin'.injective
  change Matrix.toLin' (LinearMap.toMatrix' (c.upper.conj
    ((within c.space augmentationKernel).quotientRepresentation (c.actors j)))) = _
  rw [Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  change c.upper ((within c.space augmentationKernel).quotientRepresentation (c.actors j)
    (c.upper.symm v)) = (CycleCertificate.castMatrix K (factor20 j)).mulVec v
  rw [c.upper_action, c.upper.apply_symm_apply]

omit [Finite K] in
theorem coordinateAction_charpoly (c : Coordinates K) (x : CanonicalGroup) :
    (coordinateAction c x).charpoly =
      ((within c.space augmentationKernel).quotientRepresentation x).charpoly := by
  change (LinearMap.toMatrix' (c.upper.conj
    ((within c.space augmentationKernel).quotientRepresentation x))).charpoly = _
  exact (Matrix.charpoly_toLin' _).symm.trans
    ((congrArg LinearMap.charpoly (Matrix.toLin'_toMatrix' _)).trans
      (c.upper.charpoly_conj ((within c.space augmentationKernel).quotientRepresentation x)))

theorem coordinateAction_sevenActor :
    coordinateAction (quotientCoordinates K) sevenActor = CycleCertificate.castMatrix K binaryWord := by
  rw [sevenActor_word, map_mul, map_mul, map_mul, map_pow]
  have ha (j : Fin 2) : coordinateAction (quotientCoordinates K) (Realization.actor j) =
      CycleCertificate.castMatrix K (factor20 j) := coordinateAction_actor (quotientCoordinates K) j
  rw [ha, ha]
  simp only [binaryWord, map_mul, map_pow]

theorem upper_sevenActor_power_charpoly (k : Fin 6) :
    ((within (quotientCoordinates K).space augmentationKernel).quotientRepresentation
      (sevenActor ^ (k.val + 1))).charpoly = sevenSpectrum K 20 := by
  rw [← coordinateAction_charpoly, map_pow, coordinateAction_sevenActor]
  exact cast_binaryWord_power_charpoly K k

/-- The six certificates cover every actual order-seven actor on the literal quotient. -/
theorem upper_charpoly (x : CanonicalGroup) (hx : orderOf x = 7) :
    ((within (quotientCoordinates K).space augmentationKernel).quotientRepresentation x).charpoly =
      sevenSpectrum K 20 := by
  apply charpoly_of_order_seven_generator_powers canonicalInputForm
    (by exact GaloisField.card 5 (2 * 1) (by decide))
    _ sevenActor sevenActor_order _ _ x hx
  intro k hk0 hk7
  have he : (k - 1) + 1 = k := by omega
  simpa only [he] using upper_sevenActor_power_charpoly (K := K) ⟨k - 1, by omega⟩
end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Trivial
