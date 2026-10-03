module

public import Theory.Character.CyclotomicModels
public import Theory.Character.ModularBlock.OrdinaryIntegralModels
public import Theory.Character.BrauerInduction
public import Theory.Character.FieldModelSums

/-!
# Induced linear models over the ordinary coefficient field

The monomial models constructed in `Character.CyclotomicModels` descend to
the prescribed fraction field of the cyclotomic order. Compatibility of its
embedding into the complex numbers with the order embedding identifies each
induced character exactly. This is the coefficient adapter for the monomial
step of Serre, *Linear Representations of Finite Groups*, Chapter 12.

The irreducible field-of-definition theorem below combines integral Brauer
induction with descent from virtual to actual field models.
The invariant-lattice theorem then gives a model over the prescribed local
ring with the same complex character.
-/

public section

noncomputable section
namespace ModularBlock.OrdinaryCyclotomicModels
open PrincipalBlockConstruction OrdinaryIntegralModels
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]
variable (d : PrincipalCongruenceBlockData G)

/-- Every induced subgroup linear character has a model over the prescribed field. -/
theorem exists_induced_linear_model (H : Subgroup G) (χ : H →* ℂ) :
    ∃ (n : ℕ) (ρ : Representation (coefficientField d) G (Fin n → coefficientField d)),
      ∀ g, (Representation.mapCoefficients (coefficientFieldToComplex d) ρ).character g =
        inducedClassFunction H χ g := by
  apply Representation.exists_induced_linear_model_of_range
    (coefficientFieldToComplex d) (coefficientFieldToComplex d).injective H χ
  intro h
  let z : cyclotomicOrder d.eta :=
    ⟨χ h, Representation.linear_value_mem_cyclotomicOrder d.eta_spec H χ h⟩
  exact ⟨algebraMap _ (coefficientField d) z, coefficientFieldToComplex_order d z⟩

/-- Every ordinary irreducible character has a model over the prescribed
fraction field of the cyclotomic order. -/
theorem exists_field_model (i : d.I) :
    ∃ (n : ℕ) (ρ : Representation (coefficientField d) G
        (Fin n → coefficientField d)),
      d.chi i = characterClassFunction
        (Representation.mapCoefficients (coefficientFieldToComplex d) ρ) := by
  classical
  obtain ⟨r, H, linear, a, ha⟩ :=
    BrauerInduction.exists_integral_induction (d.chi i) (d.complete.1 i)
  choose m ρ hρ using fun j => exists_induced_linear_model d (H j) (linear j)
  have hsum : d.chi i = ∑ j, (a j : ℂ) •
      characterClassFunction
        (Representation.mapCoefficients (coefficientFieldToComplex d) (ρ j)) := by
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    rw [ha g]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    exact (hρ j g).symm
  obtain ⟨n, σ, hσ⟩ :=
    Representation.exists_model_of_isConjCharacter_of_sum_int_smul
      (coefficientFieldToComplex d) (d.complete.1 i).1 m ρ a hsum
  exact ⟨n, σ, hσ.symm⟩

/-- Every ordinary irreducible character has a model over the prescribed
localization of the cyclotomic order. -/
theorem exists_integral_model (i : d.I) :
    ∃ (m : ℕ) (σ : Representation (Localization.AtPrime d.primeIdeal) G
        (Fin m → Localization.AtPrime d.primeIdeal)),
      d.chi i = characterClassFunction
        (Representation.mapCoefficients (BlockOrthogonality.localizationToComplex d.primeIdeal) σ) := by
  obtain ⟨n, ρ, hρ⟩ := exists_field_model d i
  obtain ⟨m, σ, _, hσ⟩ := exists_integral_model_of_fraction_model d i ρ hρ
  exact ⟨m, σ, hσ⟩
end ModularBlock.OrdinaryCyclotomicModels
