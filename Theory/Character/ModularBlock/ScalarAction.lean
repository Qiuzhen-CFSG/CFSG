module

public import Theory.Character.ModularBlock.PrincipalSelector
public import Theory.Character.ModularBlock.ScalarCongruence

/-!
# Localized central characters give representation scalar actions

A central group-algebra element is the sum of its constant class
coefficients times conjugacy-class sums. After embedding the localized
cyclotomic order in the complex numbers, each class sum acts on an
irreducible representation by its ordinary central-character value.
Linearity therefore identifies the full action with the localized
central-character scalar. This links the integral congruence definition
to multiplicativity of the actual representation action.

Ported from lines 418-498 of
`c3503435:glauberman_zStar/Submission/ZStar/BlockPrimitivity.lean`.
Class-sum actions and localization maps are the existing shared constructions.
-/

public section
noncomputable section
namespace ModularBlock.BlockPrimitivity
open BlockOrthogonality
attribute [local instance] Fintype.ofFinite
open scoped BigOperators

private theorem mapRingHom_smul
    {G : Type*} [Group G]
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (a : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G f (r • a) =
      f r • MonoidAlgebra.mapRingHom G f a := by
  ext g
  simp [MonoidAlgebra.coeff_mapRingHom]


private theorem center_eq_sum_classCoefficient_smul_classSum
    {R G : Type*} [CommRing R] [Group G] [Finite G]
    (z : Subring.center (MonoidAlgebra R G)) :
    (z : MonoidAlgebra R G) =
      ∑ c : ConjClasses G,
        CentralScalarCongruence.centralClassCoefficient z c • classSum R c := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  ext g
  change (z : MonoidAlgebra R G).coeff g =
    (∑ c : ConjClasses G,
      CentralScalarCongruence.centralClassCoefficient z c • classSum R c).coeff g
  simp only [MonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply']
  change (z : MonoidAlgebra R G).coeff g = ∑ c : ConjClasses G,
    CentralScalarCongruence.centralClassCoefficient z c * (classSum R c).coeff g
  simp only [classSum_coeff, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (ConjClasses.mk g)]
  · simpa using (CentralScalarCongruence.centralClassCoefficient_eq
      z (ConjClasses.mk g) g rfl).symm
  · intro c _hc hc
    rw [if_neg (Ne.symm hc)]
  · simp


theorem localizedCentralScalar_action
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I) {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi i = (characterClassFunction ρ))
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)
          (z : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)) =
      localizationToComplex d.primeIdeal
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  have hρirr : Representation.IsIrreducible ρ := by
    apply (irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using (d.complete.1 i).2
  let : Representation.IsIrreducible ρ := hρirr
  let : Nontrivial (Fin n → ℂ) :=
    irreducible_nontrivial (ρ := ρ)
  rw [center_eq_sum_classCoefficient_smul_classSum z]
  calc
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)
          (∑ c : ConjClasses G,
            CentralScalarCongruence.centralClassCoefficient z c •
              classSum (Localization.AtPrime d.primeIdeal) c)) =
        ∑ c : ConjClasses G,
          localizationToComplex d.primeIdeal
              (CentralScalarCongruence.centralClassCoefficient z c) •
            ρ.asAlgebraHom (classSum ℂ c) := by
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro c _hc
          rw [mapRingHom_smul, mapRingHom_classSum, map_smul]
    _ = ∑ c : ConjClasses G,
          localizationToComplex d.primeIdeal
              (CentralScalarCongruence.centralClassCoefficient z c) •
            (BlockPreliminaries.ordinaryCentralCharacterValue
                (d.chi i) c • (1 : Module.End ℂ (Fin n → ℂ))) := by
          apply Finset.sum_congr rfl
          intro c _hc
          obtain ⟨a, ha, rfl⟩ := classSum_action_eq_centralCharacter ρ c
          rw [ha, ← hρ]
    _ = localizationToComplex d.primeIdeal
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
          unfold CentralScalarCongruence.localizedCentralScalar
          rw [map_sum, Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro c _hc
          simp only [map_mul, localizationToComplex_algebraMap, smul_smul]
          rfl


end ModularBlock.BlockPrimitivity

