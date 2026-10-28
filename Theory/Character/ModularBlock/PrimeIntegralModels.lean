module

public import Theory.Character.ModularBlock.CyclotomicDVR
public import Theory.Character.ModularBlock.PrincipalSelector
public import Theory.Character.CyclotomicModels
public import Theory.Character.BrauerInduction
public import Theory.Character.FieldModelSums
public import Theory.Representation.IntegralModels
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Integral ordinary-character models at an arbitrary cyclotomic prime

Every ordinary irreducible character has a matrix model over the localization
of the group-order cyclotomic order at any nonzero prime. Brauer induction
first gives a virtual sum of induced linear models over the fraction field;
virtual-character descent makes it an actual model. The invariant lattice
over the local Dedekind ring then gives integral matrices with the same
complex character.

For a maximal ideal above a rational prime `p`, the finite residue field
embeds into the literal `AlgebraicClosure (ZMod p)`. The resulting reduction
map has the same domain as the complex embedding. No assertion about
irreducibility after reduction is made here.

This extends the adapters in `OrdinaryCyclotomicModels.lean` and
`OrdinaryIntegralModels.lean` without requiring characteristic-two block data.
Source: Serre, *Linear Representations of Finite Groups*, Chapters 12 and 15.
-/

public section
noncomputable section
namespace ModularBlock.PrimeIntegralModels
open BlockOrthogonality
attribute [local instance] Fintype.ofFinite

variable {η : ℂ} (P : Ideal (cyclotomicOrder η)) [P.IsPrime]

/-- The canonical embedding of the localized order is injective. -/
theorem localizationToComplex_injective :
    Function.Injective (localizationToComplex P) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    P.primeCompl (localizationToComplex P)).2
  intro x y
  constructor
  · intro h
    exact congrArg (localizationToComplex P) h
  · intro h
    have hcoe : (x : ℂ) = (y : ℂ) := by
      simpa only [localizationToComplex_algebraMap] using h
    have hxy : x = y := Subtype.ext hcoe
    rw [hxy]

/-- The fraction field of the cyclotomic order and its localizations. -/
abbrev coefficientField (η : ℂ) := FractionRing (cyclotomicOrder η)

/-- The fraction-field embedding extending the chosen localization embedding. -/
def coefficientFieldToComplex : coefficientField η →+* ℂ :=
  IsFractionRing.lift (localizationToComplex_injective P)

@[simp] theorem coefficientFieldToComplex_algebraMap
    (x : Localization.AtPrime P) :
    coefficientFieldToComplex P (algebraMap _ (coefficientField η) x) =
      localizationToComplex P x :=
  IsFractionRing.lift_algebraMap _ _

@[simp] theorem coefficientFieldToComplex_order (x : cyclotomicOrder η) :
    coefficientFieldToComplex P (algebraMap _ (coefficientField η) x) = (x : ℂ) := by
  rw [IsScalarTower.algebraMap_apply (cyclotomicOrder η)
    (Localization.AtPrime P) (coefficientField η),
    coefficientFieldToComplex_algebraMap, localizationToComplex_algebraMap]

variable {G : Type*} [Group G] [Finite G]

private theorem exists_induced_linear_model
    (hη : IsPrimitiveRoot η (Nat.card G)) (H : Subgroup G) (χ : H →* ℂ) :
    ∃ (n : ℕ) (ρ : Representation (coefficientField η) G (Fin n → coefficientField η)),
      ∀ g, (Representation.mapCoefficients (coefficientFieldToComplex P) ρ).character g =
        inducedClassFunction H χ g := by
  apply Representation.exists_induced_linear_model_of_range
    (coefficientFieldToComplex P) (coefficientFieldToComplex P).injective H χ
  intro h
  let z : cyclotomicOrder η :=
    ⟨χ h, Representation.linear_value_mem_cyclotomicOrder hη H χ h⟩
  exact ⟨algebraMap _ (coefficientField η) z, coefficientFieldToComplex_order P z⟩

/-- An ordinary irreducible has a model over the cyclotomic fraction field. -/
theorem exists_field_model (hη : IsPrimitiveRoot η (Nat.card G))
    (χ : ConjClassFunction G) (hχ : IsIrreducibleConjCharacter χ) :
    ∃ (n : ℕ) (ρ : Representation (coefficientField η) G (Fin n → coefficientField η)),
      χ = characterClassFunction
        (Representation.mapCoefficients (coefficientFieldToComplex P) ρ) := by
  classical
  obtain ⟨r, H, linear, a, ha⟩ := BrauerInduction.exists_integral_induction χ hχ
  choose m ρ hρ using fun j => exists_induced_linear_model P hη (H j) (linear j)
  have hsum : χ = ∑ j, (a j : ℂ) • characterClassFunction
      (Representation.mapCoefficients (coefficientFieldToComplex P) (ρ j)) := by
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
      (coefficientFieldToComplex P) hχ.1 m ρ a hsum
  exact ⟨n, σ, hσ.symm⟩

/-- An ordinary irreducible has an integral model at any nonzero cyclotomic prime. -/
theorem exists_integral_model (hη : IsPrimitiveRoot η (Nat.card G)) (hP : P ≠ ⊥)
    (χ : ConjClassFunction G) (hχ : IsIrreducibleConjCharacter χ) :
    ∃ (m : ℕ) (σ : Representation (Localization.AtPrime P) G
        (Fin m → Localization.AtPrime P)),
      χ = characterClassFunction (Representation.mapCoefficients (localizationToComplex P) σ) := by
  let : IsDedekindDomain (cyclotomicOrder η) :=
    CyclotomicDVR.cyclotomicOrder_isDedekindDomain (Nat.card_pos (α := G)).ne' hη
  let : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (cyclotomicOrder η) hP (Localization.AtPrime P)
  obtain ⟨n, ρ, hρ⟩ := exists_field_model P hη χ hχ
  obtain ⟨m, σ, _, hσ⟩ := Representation.exists_integral_model_trace (Localization.AtPrime P) ρ
  refine ⟨m, σ, ?_⟩
  rw [hρ]
  ext c
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
  change LinearMap.trace ℂ _ (Representation.mapCoefficients (coefficientFieldToComplex P) ρ g) =
    LinearMap.trace ℂ _ (Representation.mapCoefficients (localizationToComplex P) σ g)
  rw [Representation.mapCoefficients_trace, Representation.mapCoefficients_trace,
    ← hσ g, Representation.mapCoefficients_trace]
  exact coefficientFieldToComplex_algebraMap P _

omit [P.IsPrime] in
private theorem primeIdeal_ne_bot (p : ℕ) [Fact p.Prime]
    (hp : (p : cyclotomicOrder η) ∈ P) : P ≠ ⊥ := by
  intro hP
  rw [hP, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp

/-- Reduction into the algebraic closure of the prime field at the chosen prime. -/
theorem exists_residueMap {n : ℕ} (hn : n ≠ 0) (hη : IsPrimitiveRoot η n)
    [P.IsMaximal] (p : ℕ) [Fact p.Prime] (hp : (p : cyclotomicOrder η) ∈ P) :
    Nonempty (Localization.AtPrime P →+* AlgebraicClosure (ZMod p)) := by
  let k := cyclotomicOrder η ⧸ P
  let : Field k := Ideal.Quotient.field P
  let : Finite k := CyclotomicDVR.cyclotomicOrder_quotient_finite hn hη P
    (primeIdeal_ne_bot P p hp)
  let : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    change Ideal.Quotient.mk P (p : cyclotomicOrder η) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let f : k →+* AlgebraicClosure (ZMod p) :=
    (IsAlgClosed.lift : k →ₐ[ZMod p] AlgebraicClosure (ZMod p)).toRingHom
  let q : Localization.AtPrime P →+* k :=
    IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
      (g := Ideal.Quotient.mk P) (fun y =>
        isUnit_iff_ne_zero.mpr (Ideal.Quotient.eq_zero_iff_mem.not.mpr y.2))
  exact ⟨f.comp q⟩

end ModularBlock.PrimeIntegralModels
