module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.DefectZero.IntegralData
public import Theory.Character.ModularBlock.PrimeIntegralModels
public import Theory.Character.ModularBlock.PrimeCongruence

/-!
# Compatible integral models for the four defect-zero rows

Starting with genuine ordinary characters, choose a maximal ideal above eleven
in the group-order cyclotomic order. The generic cyclotomic field-of-definition
and invariant-lattice construction realizes all four rows over this one local
domain. Evaluation at the identity fixes their ranks as 77, 77, 77 and 209.
The finite residue field embeds in the literal `ElevenClosure`.

The particular fifth root of the supplied ordinary table belongs to the same
order because five divides 175560. Its image in the localization therefore
lifts that root under the complex embedding, keeping the fifth-root periods
compatible across all four rows.

This supplies the integral-model input to the defect-zero reduction argument.
Irreducibility after reduction remains a separate theorem. Source: Serre,
*Linear Representations of Finite Groups*, Chapters 12 and 15; Janko,
J. Algebra 3 (1966), 147–186. Row conventions are in `../../Source.md`.
-/

noncomputable section
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.DefectZero
open ModularBlock

variable {G : Type*} [Group G] [Finite G]

/-- The four ordinary rows admit compatible integral models over one domain,
with reduction into `ElevenClosure` and the prescribed fifth root. The ring
and both instances are bundled as existential witnesses for downstream use. -/
public theorem exists_integralModels (d : OrdinaryData G) (horder : Nat.card G = 175560) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R), Nonempty (IntegralModels d R) := by
  classical
  let η : ℂ := Complex.exp (2 * Real.pi * Complex.I / Nat.card G)
  have hη : IsPrimitiveRoot η (Nat.card G) :=
    Complex.isPrimitiveRoot_exp _ (Nat.card_pos (α := G)).ne'
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨P, hPmax, hPover⟩ := PrimeBlockConstruction.exists_maximalIdeal_above_prime hη 11
  let : P.IsMaximal := hPmax
  have hp : (11 : cyclotomicOrder η) ∈ P := by
    let : P.LiesOver (Ideal.span ({(11 : ℤ)} : Set ℤ)) := hPover
    have h := (Ideal.mem_of_liesOver P
      (Ideal.span ({(11 : ℤ)} : Set ℤ)) (11 : ℤ)).mp
      (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_ofNat] using h
  have hP : P ≠ ⊥ := by
    intro hP
    rw [hP, Ideal.mem_bot] at hp
    exact (by norm_num : (11 : cyclotomicOrder η) ≠ 0) hp
  obtain ⟨residue⟩ := PrimeIntegralModels.exists_residueMap P
    (Nat.card_pos (α := G)).ne' hη 11 hp
  let R := Localization.AtPrime P
  have hmodels : ∀ i : Fin 4, ∃ σ : Representation R G (Fin (defectZeroDegree i) → R),
      d.chi (row i) = characterClassFunction
        (Representation.mapCoefficients (BlockOrthogonality.localizationToComplex P) σ) := by
    intro i
    obtain ⟨m, σ, hσ⟩ := PrimeIntegralModels.exists_integral_model P hη hP
      (d.chi (row i)) (d.complete.1 (row i))
    have hm : m = defectZeroDegree i := by
      have h := congrFun hσ (ConjClasses.mk 1)
      rw [d.degree_value, ordinaryDegree_row] at h
      change (defectZeroDegree i : ℂ) = (Representation.mapCoefficients
        (BlockOrthogonality.localizationToComplex P) σ).character 1 at h
      rw [Representation.char_one] at h
      simpa using (Nat.cast_injective h).symm
    subst m
    exact ⟨σ, hσ⟩
  choose σ hσ using hmodels
  let ζ : cyclotomicOrder η := ⟨d.rootFive,
    primitive_root_mem_cyclotomicOrder_of_dvd hη (Nat.card_pos (α := G)).ne'
      d.rootFive_primitive (by rw [horder]; decide)⟩
  refine ⟨R, inferInstance, inferInstance, ⟨{
    complex := BlockOrthogonality.localizationToComplex P
    complex_injective := PrimeIntegralModels.localizationToComplex_injective P
    residue := residue
    rootFive := algebraMap _ R ζ
    rootFive_complex := ?_
    rep := σ
    character_eq := hσ }⟩⟩
  exact BlockOrthogonality.localizationToComplex_algebraMap P ζ

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.DefectZero
