module

public import Theory.Character.ModularBlock.PrincipalElement

/-!
# Integral character-projector numerators

For each irreducible character in the chosen complete family, the function
`g ↦ chi(1) * chi(g⁻¹)` gives the denominator-cleared primitive projector.
Character-value integrality places its coefficients in the cyclotomic
localization, and conjugacy invariance proves centrality. Extension through
the canonical localization embedding yields the corresponding complex
numerator. Coefficient specification lemmas expose these values while the
finite-support implementation remains private.

The generic group-algebra trace and complete-family orthogonality wrappers
reuse existing results. The coefficient-change centrality and injectivity
lemmas support the projector's scaled-idempotence proof in the next module.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/IsotypicLattice.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.IsotypicLattice

universe u v

attribute [local instance] Fintype.ofFinite

open PrincipalBlockConstruction

/-- Trace of an arbitrary group-algebra element in a representation. -/
theorem groupAlgebra_trace
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (z : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (rho.asAlgebraHom z) =
      ∑ g : G, z.coeff g * rho.character g :=
  BlockOrthogonality.groupAlgebra_trace rho z

/-- Orthogonality inside a fixed complete irreducible character family. -/
theorem completeFamily_inner
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I] [DecidableEq I]
    (chi : I → ConjClassFunction G)
    (hchi : IsCompleteIrreducibleCharacterFamily chi)
    (i j : I) :
    classFunctionInner (chi i) (chi j) =
      if i = j then 1 else 0 :=
  completeFamily_orthonormal hchi i j

/-- A coefficient function constant under conjugation defines a central
group-algebra element. -/
theorem mem_center_of_coeff_conj_invariant
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (a : MonoidAlgebra R G)
    (ha : ∀ x y : G, a.coeff (x * y * x⁻¹) = a.coeff y) :
    a ∈ Set.center (MonoidAlgebra R G) := by
  classical
  rw [Semigroup.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single g r =>
      ext x
      rw [MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply]
      have hcoeff : a.coeff (g⁻¹ * x) = a.coeff (x * g⁻¹) := by
        simpa [mul_assoc] using ha g⁻¹ (x * g⁻¹)
      rw [hcoeff]
      exact mul_comm _ _

theorem mapRingHom_mem_center
    {R S : Type u} {G : Type v}
    [CommRing R] [CommRing S] [Group G]
    (f : R →+* S) (a : MonoidAlgebra R G)
    (ha : a ∈ Set.center (MonoidAlgebra R G)) :
    MonoidAlgebra.mapRingHom G f a ∈
      Set.center (MonoidAlgebra S G) := by
  rw [Semigroup.mem_center_iff] at ha ⊢
  intro b
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single g r =>
      let x : MonoidAlgebra R G := MonoidAlgebra.single g 1
      have hx := congrArg (MonoidAlgebra.mapRingHom G f) (ha x)
      rw [map_mul, map_mul] at hx
      have hsingle :
          (MonoidAlgebra.single g r : MonoidAlgebra S G) =
            r • MonoidAlgebra.single g 1 := by simp
      rw [hsingle, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      exact congrArg (fun z : MonoidAlgebra S G ↦ r • z)
        (by simpa [x] using hx)

theorem mapRingHom_injective
    {R S : Type u} {G : Type v}
    [CommRing R] [CommRing S] [Group G]
    (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (MonoidAlgebra.mapRingHom G f) := by
  intro a b hab
  ext g
  apply hf
  simpa only [MonoidAlgebra.coeff_mapRingHom] using
    congrArg (fun z : MonoidAlgebra S G ↦ z.coeff g) hab

section CharacterProjector

variable {G : Type u} [Group G] [Finite G]

instance principalPrime_isPrime
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

/-- The canonical embedding of the localized cyclotomic order into `ℂ`. -/
@[expose] noncomputable def localizationToComplex
    (d : PrincipalCongruenceBlockData G) :
    Localization.AtPrime d.primeIdeal →+* ℂ :=
  BlockOrthogonality.localizationToComplex d.primeIdeal

@[simp] theorem localizationToComplex_algebraMap
    (d : PrincipalCongruenceBlockData G)
    (a : cyclotomicOrder d.eta) :
    localizationToComplex d
        (algebraMap _ (Localization.AtPrime d.primeIdeal) a) = (a : ℂ) := by
  exact BlockOrthogonality.localizationToComplex_algebraMap d.primeIdeal a

theorem localizationToComplex_injective
    (d : PrincipalCongruenceBlockData G) :
    Function.Injective (localizationToComplex d) := by
  exact BlockOrthogonality.localizationToComplex_injective d

/-- An irreducible character value in the chosen cyclotomic order. -/
noncomputable def characterValueInCyclotomicOrder
    (d : PrincipalCongruenceBlockData G) (i : d.I) (g : G) :
    cyclotomicOrder d.eta := by
  refine ⟨d.chi i (ConjClasses.mk g), ?_⟩
  rcases (d.complete.1 i).1 with ⟨n, rho, hrho⟩
  rw [hrho]
  exact representation_character_mem_cyclotomicOrder
    d.eta_spec rho g

@[simp] theorem coe_characterValueInCyclotomicOrder
    (d : PrincipalCongruenceBlockData G) (i : d.I) (g : G) :
    ((characterValueInCyclotomicOrder d i g :
      cyclotomicOrder d.eta) : ℂ) =
        d.chi i (ConjClasses.mk g) := by
  rfl

/-- The denominator-cleared primitive character projector. -/
noncomputable def characterProjectorNumerator
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    MonoidAlgebra (Localization.AtPrime d.primeIdeal) G :=
  MonoidAlgebra.ofCoeff
    ((Finsupp.equivFunOnFinite :
      (G →₀ Localization.AtPrime d.primeIdeal) ≃
        (G → Localization.AtPrime d.primeIdeal)).symm
      (fun g ↦
        algebraMap (cyclotomicOrder d.eta)
          (Localization.AtPrime d.primeIdeal)
          (characterValueInCyclotomicOrder d i 1 *
            characterValueInCyclotomicOrder d i g⁻¹)))

@[simp] theorem characterProjectorNumerator_apply
    (d : PrincipalCongruenceBlockData G) (i : d.I) (g : G) :
    (characterProjectorNumerator d i).coeff g =
      algebraMap (cyclotomicOrder d.eta)
        (Localization.AtPrime d.primeIdeal)
        (characterValueInCyclotomicOrder d i 1 *
          characterValueInCyclotomicOrder d i g⁻¹) := by
  classical
  change (MonoidAlgebra.ofCoeff
      ((Finsupp.equivFunOnFinite :
        (G →₀ Localization.AtPrime d.primeIdeal) ≃
          (G → Localization.AtPrime d.primeIdeal)).symm
        (fun x ↦
          algebraMap (cyclotomicOrder d.eta)
            (Localization.AtPrime d.primeIdeal)
            (characterValueInCyclotomicOrder d i 1 *
              characterValueInCyclotomicOrder d i x⁻¹)))).coeff g = _
  rw [MonoidAlgebra.coeff_ofCoeff]
  simp

theorem characterProjectorNumerator_mem_center
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    characterProjectorNumerator d i ∈
      Set.center
        (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) := by
  apply mem_center_of_coeff_conj_invariant
  intro x y
  simp only [characterProjectorNumerator_apply]
  congr 2
  apply Subtype.ext
  change d.chi i (ConjClasses.mk (x * y * x⁻¹)⁻¹) =
    d.chi i (ConjClasses.mk y⁻¹)
  apply congrArg (d.chi i)
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  apply isConj_iff.mpr
  refine ⟨x⁻¹, ?_⟩
  simp [mul_assoc]

noncomputable def complexCharacterProjectorNumerator
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff
    ((Finsupp.equivFunOnFinite : (G →₀ ℂ) ≃ (G → ℂ)).symm
      (fun g ↦ d.chi i (ConjClasses.mk (1 : G)) *
        d.chi i (ConjClasses.mk g⁻¹)))

@[simp] theorem complexCharacterProjectorNumerator_apply
    (d : PrincipalCongruenceBlockData G) (i : d.I) (g : G) :
    (complexCharacterProjectorNumerator d i).coeff g =
      d.chi i (ConjClasses.mk (1 : G)) *
        d.chi i (ConjClasses.mk g⁻¹) := by
  classical
  change (MonoidAlgebra.ofCoeff
      ((Finsupp.equivFunOnFinite : (G →₀ ℂ) ≃ (G → ℂ)).symm
        (fun x ↦ d.chi i (ConjClasses.mk (1 : G)) *
          d.chi i (ConjClasses.mk x⁻¹)))).coeff g = _
  rw [MonoidAlgebra.coeff_ofCoeff]
  simp

theorem map_characterProjectorNumerator
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    MonoidAlgebra.mapRingHom G (localizationToComplex d)
        (characterProjectorNumerator d i) =
      complexCharacterProjectorNumerator d i := by
  classical
  ext x
  rw [MonoidAlgebra.coeff_mapRingHom,
    characterProjectorNumerator_apply,
    complexCharacterProjectorNumerator_apply]
  simp

theorem complexCharacterProjectorNumerator_mem_center
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    complexCharacterProjectorNumerator d i ∈
      Set.center (MonoidAlgebra ℂ G) := by
  rw [← map_characterProjectorNumerator d i]
  exact mapRingHom_mem_center (localizationToComplex d)
    (characterProjectorNumerator d i)
    (characterProjectorNumerator_mem_center d i)

end CharacterProjector
end ModularBlock.IsotypicLattice
