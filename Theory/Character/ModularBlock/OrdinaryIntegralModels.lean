module

public import Theory.Character.ModularBlock.CyclotomicDVR
public import Theory.Character.ModularBlock.PrincipalSelector
public import Theory.Representation.IntegralModels

/-!
# From cyclotomic field models to integral models

The prescribed cyclotomic order and its localization have the same fraction
field. Its embedding into the complex numbers extends the localization map.
An ordinary character realized over this fraction field therefore admits a
model over the prescribed local ring with exactly the same complex character
and dimension.

The local ring is a DVR by `CyclotomicDVR`; the invariant-lattice theorem in
`Representation.IntegralModels` applies over its fraction field. Compatibility
of traces with coefficient maps identifies the resulting complex character.
This is the lattice step of Serre, *Linear Representations of Finite Groups*,
Chapter 15. The cyclotomic field-of-definition theorem is a separate input.
-/

public section

noncomputable section
namespace ModularBlock.OrdinaryIntegralModels
open PrincipalBlockConstruction BlockOrthogonality
variable {G : Type*} [Group G] [Finite G]
variable (d : PrincipalCongruenceBlockData G)

/-- The fraction field of the cyclotomic integer order, also the fraction field
of its localization at the prescribed prime. -/
abbrev coefficientField := FractionRing (cyclotomicOrder d.eta)

/-- The embedding extending the prescribed embedding of the local order. -/
def coefficientFieldToComplex : coefficientField d →+* ℂ :=
  IsFractionRing.lift (localizationToComplex_injective d)

@[simp] theorem coefficientFieldToComplex_algebraMap
    (x : Localization.AtPrime d.primeIdeal) :
    coefficientFieldToComplex d (algebraMap _ (coefficientField d) x) =
      localizationToComplex d.primeIdeal x :=
  IsFractionRing.lift_algebraMap _ _

@[simp] theorem coefficientFieldToComplex_order
    (x : cyclotomicOrder d.eta) :
    coefficientFieldToComplex d (algebraMap _ (coefficientField d) x) = (x : ℂ) := by
  rw [IsScalarTower.algebraMap_apply (cyclotomicOrder d.eta)
    (Localization.AtPrime d.primeIdeal) (coefficientField d),
    coefficientFieldToComplex_algebraMap, localizationToComplex_algebraMap]

/-- A cyclotomic fraction-field model gives an integral model of the same rank
and the same complex character. -/
theorem exists_integral_model_of_fraction_model (i : d.I) {n : ℕ}
    (ρ : Representation (coefficientField d) G (Fin n → coefficientField d))
    (hχ : d.chi i = characterClassFunction
      (Representation.mapCoefficients (coefficientFieldToComplex d) ρ)) :
    ∃ (m : ℕ) (σ : Representation (Localization.AtPrime d.primeIdeal) G
        (Fin m → Localization.AtPrime d.primeIdeal)),
      m = n ∧ d.chi i = characterClassFunction
        (Representation.mapCoefficients (localizationToComplex d.primeIdeal) σ) := by
  let R := Localization.AtPrime d.primeIdeal
  let K := coefficientField d
  let : IsDiscreteValuationRing R :=
    CyclotomicDVR.cyclotomicOrderAtPrime_isDiscreteValuationRing d
  obtain ⟨m, σ, hm, hσ⟩ := Representation.exists_integral_model_trace R ρ
  refine ⟨m, σ, ?_, ?_⟩
  · simpa [K] using hm
  · rw [hχ]
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    change LinearMap.trace ℂ _ (Representation.mapCoefficients (coefficientFieldToComplex d) ρ g) =
      LinearMap.trace ℂ _ (Representation.mapCoefficients (localizationToComplex d.primeIdeal) σ g)
    rw [Representation.mapCoefficients_trace, Representation.mapCoefficients_trace,
      ← hσ g, Representation.mapCoefficients_trace]
    exact coefficientFieldToComplex_algebraMap d _
end ModularBlock.OrdinaryIntegralModels
