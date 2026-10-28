module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Reduction
public import Theory.Character.ModularBlock.ScalarCongruence
public import Theory.Character.ModularBlock.DVRDenominators
public import Theory.Character.ModularBlock.CentralLift

/-!
# Central scalar algebra at an arbitrary congruence prime

The class-sum formula computes the scalar action on each ordinary irreducible.
It respects products and subtraction; character orthogonality reconstructs the
coefficients. This is the scalar algebra needed for the principal block's
primitivity, with the specified prime and projector retained throughout.

Adapted from `ModularBlock/ScalarAction.lean`, `ScalarAlgebra.lean` and
`ScalarReconstruction.lean`, themselves ported from
`public/lean-eval/glauberman_zStar` at c3503435. Source: Feit III.8--9.
-/

public section
noncomputable section
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
open ModularBlock ModularBlock.PrimeBlockConstruction
open ModularBlock.PrincipalBlockConstruction ModularBlock.BlockOrthogonality
attribute [local instance] Fintype.ofFinite
open scoped BigOperators
variable {p : ℕ}

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
    (d : PrimeCongruenceBlockData p G)
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



private theorem smul_one_injective
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V] :
    Function.Injective
      (fun a : ℂ => a • (1 : Module.End ℂ V)) := by
  intro a b hab
  apply FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ V)
  simpa [Algebra.algebraMap_eq_smul_one] using hab


theorem localizedCentralScalar_mul
    {G : Type*} [Group G] [Finite G]
    (d : PrimeCongruenceBlockData p G)
    (i : d.I)
    (z w : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)) :
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
        d.primeIdeal (d.chi i) (d.complete.1 i) (z * w) =
      CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z *
        CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) w := by
  rcases (d.complete.1 i).1 with ⟨n, ρ, hρ⟩
  have hρirr : Representation.IsIrreducible ρ := by
    apply (irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using (d.complete.1 i).2
  let : Representation.IsIrreducible ρ := hρirr
  let : Nontrivial (Fin n → ℂ) :=
    irreducible_nontrivial (ρ := ρ)
  have hz := localizedCentralScalar_action d i ρ hρ z
  have hw := localizedCentralScalar_action d i ρ hρ w
  have hzw := localizedCentralScalar_action d i ρ hρ (z * w)
  have hscalar :
      localizationToComplex d.primeIdeal
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) (z * w)) =
        localizationToComplex d.primeIdeal
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) z) *
          localizationToComplex d.primeIdeal
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) w) := by
    apply smul_one_injective
      (V := Fin n → ℂ)
    change
      localizationToComplex d.primeIdeal
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) (z * w)) •
          (1 : Module.End ℂ (Fin n → ℂ)) =
        (localizationToComplex d.primeIdeal
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) z) *
          localizationToComplex d.primeIdeal
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) w)) •
          (1 : Module.End ℂ (Fin n → ℂ))
    calc
      _ = ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal) (z * w)) :=
        hzw.symm
      _ = ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal) z) *
          ρ.asAlgebraHom
            (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal) w) := by
        rw [map_mul, map_mul]
      _ = _ := by rw [hz, hw]; simp [Algebra.smul_def]
  apply PrimeIntegralModels.localizationToComplex_injective d.primeIdeal
  simpa using hscalar

/-- Localized central-character scalars preserve subtraction. -/

theorem localizedCentralScalar_sub
    {G : Type*} [Group G] [Finite G]
    (d : PrimeCongruenceBlockData p G)
    (i : d.I)
    (z w : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)) :
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
        d.primeIdeal (d.chi i) (d.complete.1 i) (z - w) =
      CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z -
        CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) w := by
  classical
  rw [CentralScalarCongruence.localizedCentralScalar,
    CentralScalarCongruence.localizedCentralScalar,
    CentralScalarCongruence.localizedCentralScalar,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  change
    (z.1.coeff (CentralScalarCongruence.classRepresentative c) -
        w.1.coeff (CentralScalarCongruence.classRepresentative c)) * _ =
      z.1.coeff (CentralScalarCongruence.classRepresentative c) * _ -
        w.1.coeff (CentralScalarCongruence.classRepresentative c) * _
  exact sub_mul _ _ _


theorem localizedCentralScalar_pow_of_pos
    {G : Type*} [Group G] [Finite G]
    (d : PrimeCongruenceBlockData p G)
    (i : d.I)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (N : ℕ) (hN : 0 < N) :
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
        d.primeIdeal (d.chi i) (d.complete.1 i) (z ^ N) =
      CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z ^ N := by
  induction N using Nat.case_strong_induction_on with
  | hz => omega
  | hi N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp
      · rw [pow_succ, pow_succ, localizedCentralScalar_mul]
        rw [ih N (by omega) (Nat.pos_of_ne_zero hN0)]


end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
