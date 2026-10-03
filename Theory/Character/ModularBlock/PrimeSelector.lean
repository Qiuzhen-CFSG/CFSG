module

public import Theory.Character.ModularBlock.PrimeCongruence
public import Theory.Character.ModularBlock.PrincipalSelector
public import Theory.Character.ModularBlock.CentralCoefficient

/-!
# Localized projectors for arbitrary congruence blocks

For a prime ideal above `p`, every ordinary congruence block is selected by a
central idempotent over the localized cyclotomic order. Separating class sums
have invertible central-character differences between distinct blocks.
Products of normalized separating factors, followed by the complement of a
product of complements, act by exactly the indicator of the chosen block.
Character expansion proves idempotence and computes every coefficient.

The construction adapts `PrincipalSelector.lean` and `PrincipalElement.lean`,
ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BlockOrthogonality.lean` (revision `c3503435`).
The root construction follows `MixedBrauerTrace.lean`.
Source: Brauer--Tuan, *On simple groups of finite order I* (1945), equation (2.3).
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.PrimeBlockConstruction
open BlockPreliminaries PrincipalBlockConstruction BlockOrthogonality

variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-- The chosen maximal ideal is prime, so localization at it is available. -/
instance PrimeCongruenceBlockData.primeIdeal_isPrime
    (d : PrimeCongruenceBlockData p G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

namespace PrimeSelector
attribute [local instance] Fintype.ofFinite

universe u v

private theorem single_one_mul_eq_smul
    {G : Type u} [Group G]
    {R : Type v} [CommRing R]
    (r : R) (a : MonoidAlgebra R G) :
    MonoidAlgebra.single 1 r * a = r • a := by
  ext g
  simp [MonoidAlgebra.coeff_single_mul_apply]

private theorem smul_sub_smul_eq
    {M : Type v} [AddCommGroup M] [Module ℂ M]
    (a b c : ℂ) (x : M) :
    a • (b • x - c • x) = (a * (b - c)) • x := by
  calc
    a • (b • x - c • x) = a • ((b - c) • x) := by
      exact congrArg (fun y : M => a • y) (sub_smul b c x).symm
    _ = (a * (b - c)) • x := smul_smul a (b - c) x

private theorem exists_separating_class
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b) :
    ∃ c : ConjClasses G,
      centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) c -
        centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) c ∉ d.primeIdeal := by
  classical
  have hij : ¬ SameTwoBlock d.eta_spec d.primeIdeal
      (d.chi i) (d.chi j) (d.complete.1 i) (d.complete.1 j) := by
    intro h
    apply hj
    apply (d.mem_blockOf_iff j b).2
    exact sameTwoBlock_trans d.eta_spec d.primeIdeal
      (sameTwoBlock_symm d.eta_spec d.primeIdeal
        h)
      ((d.mem_blockOf_iff i b).1 hi)
  by_contra hsep
  apply hij
  apply (sameTwoBlock_iff d.eta_spec d.primeIdeal
    (d.chi i) (d.chi j) (d.complete.1 i) (d.complete.1 j)).2
  intro c
  by_contra hc
  exact hsep ⟨c, hc⟩

private noncomputable def separatingClass
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b) : ConjClasses G :=
  Classical.choose (exists_separating_class d b hi hj)

private theorem separatingClass_spec
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b) :
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d b hi hj) -
        centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d b hi hj) ∉ d.primeIdeal :=
  Classical.choose_spec (exists_separating_class d b hi hj)

private noncomputable def localizedCentralCharacter
    (d : PrimeCongruenceBlockData p G) (i : d.I) (c : ConjClasses G) :
    cyclotomicOrderAtPrime d.primeIdeal :=
  algebraMap _ _ (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
    (d.complete.1 i) c)

private theorem localizationToComplex_localizedCentralCharacter
    (d : PrimeCongruenceBlockData p G) (i : d.I) (c : ConjClasses G) :
    localizationToComplex d.primeIdeal (localizedCentralCharacter d i c) =
      (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
        (d.complete.1 i) c : ℂ) := by
  exact localizationToComplex_algebraMap d.primeIdeal _

private noncomputable def denominatorInverse
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b) :
    cyclotomicOrderAtPrime d.primeIdeal := by
  let a := centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
      (d.complete.1 i) (separatingClass d b hi hj) -
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
      (d.complete.1 j) (separatingClass d b hi hj)
  let hmem : a ∈ d.primeIdeal.primeCompl :=
    show a ∉ d.primeIdeal from separatingClass_spec d b hi hj
  exact IsLocalization.mk' (Localization.AtPrime d.primeIdeal) 1 ⟨a, hmem⟩

private theorem denominatorInverse_map
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b) :
    localizationToComplex d.primeIdeal
        (denominatorInverse d b hi hj) =
      ((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d b hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d b hi hj) : ℂ))⁻¹ := by
  classical
  let a := centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
      (d.complete.1 i) (separatingClass d b hi hj) -
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
      (d.complete.1 j) (separatingClass d b hi hj)
  let hmem : a ∈ d.primeIdeal.primeCompl :=
    separatingClass_spec d b hi hj
  have h := congrArg (localizationToComplex d.primeIdeal)
    (IsLocalization.mk'_spec (Localization.AtPrime d.primeIdeal) 1 ⟨a, hmem⟩)
  apply eq_inv_of_mul_eq_one_left
  simpa only [map_mul, localizationToComplex_algebraMap, map_one,
    denominatorInverse, a, map_sub, Subring.coe_one] using h

private noncomputable def localizedGroupAlgebraToComplex
    (d : PrimeCongruenceBlockData p G) :
    MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G →+*
      MonoidAlgebra ℂ G :=
  MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)

/-- A localized class-sum polynomial which acts as `1` on `i` and as `0`
on `j`. -/
private noncomputable def separatingFactor
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b) :
    MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G :=
  MonoidAlgebra.single 1 (denominatorInverse d b hi hj) *
    (classSum (cyclotomicOrderAtPrime d.primeIdeal)
        (separatingClass d b hi hj) -
      MonoidAlgebra.single 1
        (localizedCentralCharacter d j (separatingClass d b hi hj)))

private theorem map_separatingFactor
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b) :
    localizedGroupAlgebraToComplex d (separatingFactor d b hi hj) =
      (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d b hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d b hi hj) : ℂ))⁻¹) •
        (classSum ℂ (separatingClass d b hi hj) -
          (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
            (d.complete.1 j) (separatingClass d b hi hj) : ℂ) • 1) := by
  classical
  simp only [separatingFactor, localizedGroupAlgebraToComplex, map_mul,
    map_sub, MonoidAlgebra.mapRingHom_single, mapRingHom_classSum]
  rw [show localizationToComplex d.primeIdeal
      (denominatorInverse d b hi hj) =
        ((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d b hi hj) : ℂ) -
          (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
            (d.complete.1 j) (separatingClass d b hi hj) : ℂ))⁻¹ by
      exact denominatorInverse_map d b hi hj]
  have hsingle (r : ℂ) :
      (MonoidAlgebra.single 1 r : MonoidAlgebra ℂ G) = r • 1 := by
    simp [MonoidAlgebra.one_def]
  calc
    MonoidAlgebra.single 1
          (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
            (d.complete.1 i) (separatingClass d b hi hj) : ℂ) -
              (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
                (d.complete.1 j) (separatingClass d b hi hj) : ℂ))⁻¹) *
        (classSum ℂ (separatingClass d b hi hj) -
          MonoidAlgebra.single 1
            (localizationToComplex d.primeIdeal
              (localizedCentralCharacter d j (separatingClass d b hi hj)))) =
      (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d b hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d b hi hj) : ℂ))⁻¹) •
        (classSum ℂ (separatingClass d b hi hj) -
          MonoidAlgebra.single 1
            (localizationToComplex d.primeIdeal
              (localizedCentralCharacter d j (separatingClass d b hi hj)))) := by
      exact single_one_mul_eq_smul _ _
    _ = (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d b hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d b hi hj) : ℂ))⁻¹) •
        (classSum ℂ (separatingClass d b hi hj) -
          (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
            (d.complete.1 j) (separatingClass d b hi hj) : ℂ) • 1) := by
      rw [localizationToComplex_localizedCentralCharacter,
        hsingle]

private theorem separatingFactor_comm
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b)
    (a : MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :
    a * separatingFactor d b hi hj = separatingFactor d b hi hj * a := by
  classical
  rw [separatingFactor]
  have hdenom :
      a * MonoidAlgebra.single 1 (denominatorInverse d b hi hj) =
        MonoidAlgebra.single 1 (denominatorInverse d b hi hj) * a := by
    ext x
    simp [mul_comm]
  let x := classSum (cyclotomicOrderAtPrime d.primeIdeal)
      (separatingClass d b hi hj) -
    MonoidAlgebra.single 1
      (localizedCentralCharacter d j (separatingClass d b hi hj))
  have hx : a * x = x * a := by
    have hclass : classSum (cyclotomicOrderAtPrime d.primeIdeal)
        (separatingClass d b hi hj) ∈
        Set.center (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
      (Semigroup.mem_center_iff).2
        (classSum_comm (cyclotomicOrderAtPrime d.primeIdeal)
          (separatingClass d b hi hj))
    have hscalar : MonoidAlgebra.single 1
        (localizedCentralCharacter d j (separatingClass d b hi hj)) ∈
        Set.center (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) := by
      apply (Semigroup.mem_center_iff).2
      intro b
      ext g
      simp [mul_comm]
    have hxcenter : x ∈
        Set.center (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) := by
      dsimp only [x]
      rw [sub_eq_add_neg]
      exact Set.add_mem_center hclass (Set.neg_mem_center hscalar)
    exact (Semigroup.mem_center_iff.mp hxcenter) a
  calc
    a * (MonoidAlgebra.single 1 (denominatorInverse d b hi hj) * x) =
        (a * MonoidAlgebra.single 1 (denominatorInverse d b hi hj)) * x :=
      (mul_assoc _ _ _).symm
    _ = (MonoidAlgebra.single 1 (denominatorInverse d b hi hj) * a) * x := by
      rw [hdenom]
    _ = MonoidAlgebra.single 1 (denominatorInverse d b hi hj) * (a * x) :=
      mul_assoc _ _ _
    _ = MonoidAlgebra.single 1 (denominatorInverse d b hi hj) * (x * a) := by
      rw [hx]
    _ = (MonoidAlgebra.single 1 (denominatorInverse d b hi hj) * x) * a :=
      (mul_assoc _ _ _).symm

private theorem separatingDifference_ne_zero
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b) :
    (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d b hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d b hi hj) : ℂ) ≠ 0 := by
  intro hzero
  apply separatingClass_spec d b hi hj
  have hzero' :
      centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d b hi hj) -
        centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d b hi hj) = 0 := by
    apply Subtype.ext
    exact hzero
  rw [hzero']
  exact d.primeIdeal.zero_mem

private theorem separatingFactor_action
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b)
    (l : d.I) {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (separatingFactor d b hi hj)) =
      (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d b hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d b hi hj) : ℂ))⁻¹ *
        ((centralCharacterInCyclotomicOrder d.eta_spec (d.chi l)
          (d.complete.1 l) (separatingClass d b hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d b hi hj) : ℂ))) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  have hρirr : Representation.IsIrreducible ρ := by
    apply (irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using (d.complete.1 l).2
  let : Representation.IsIrreducible ρ := hρirr
  let c := separatingClass d b hi hj
  obtain ⟨a, ha, haeq⟩ := classSum_action_eq_centralCharacter ρ c
  have hclass : ρ.asAlgebraHom (classSum ℂ c) =
      (centralCharacterInCyclotomicOrder d.eta_spec (d.chi l)
        (d.complete.1 l) c : ℂ) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
    calc
      ρ.asAlgebraHom (classSum ℂ c) =
          a • (1 : Module.End ℂ (Fin n → ℂ)) := ha
      _ = ordinaryCentralCharacterValue (characterClassFunction ρ) c •
          (1 : Module.End ℂ (Fin n → ℂ)) := by rw [haeq]
      _ = (centralCharacterInCyclotomicOrder d.eta_spec (d.chi l)
            (d.complete.1 l) c : ℂ) •
          (1 : Module.End ℂ (Fin n → ℂ)) := by
        apply congrArg (fun z : ℂ =>
          z • (1 : Module.End ℂ (Fin n → ℂ)))
        change ordinaryCentralCharacterValue (characterClassFunction ρ) c =
          ordinaryCentralCharacterValue (d.chi l) c
        exact congrArg (fun χ : ConjClassFunction G =>
          ordinaryCentralCharacterValue χ c) hρ.symm
  dsimp only [c] at hclass
  rw [map_separatingFactor]
  rw [map_smul, map_sub, map_smul, map_one, hclass]
  exact smul_sub_smul_eq _ _ _ _

private theorem separatingFactor_action_self
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi i = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (separatingFactor d b hi hj)) = 1 := by
  rw [separatingFactor_action d b hi hj i ρ hρ]
  rw [inv_mul_cancel₀ (separatingDifference_ne_zero d b hi hj)]
  exact one_smul ℂ _

private theorem separatingFactor_action_other
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi j = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (separatingFactor d b hi hj)) = 0 := by
  rw [separatingFactor_action d b hi hj j ρ hρ]
  simp

private abbrev blockCharacterIndex (d : PrimeCongruenceBlockData p G) (b : d.I) :=
  {i : d.I // i ∈ d.blockOf b}

private abbrev outsideCharacterIndex (d : PrimeCongruenceBlockData p G) (b : d.I) :=
  {j : d.I // j ∉ d.blockOf b}

private instance localizedCenterCommRing
    (d : PrimeCongruenceBlockData p G) :
    CommRing (Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) :=
  @Subring.instCommRingSubtypeMemCenter _
    (inferInstance : Ring
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G))

private noncomputable def separatingFactorCenter
    (d : PrimeCongruenceBlockData p G) (b : d.I)
    {i j : d.I} (hi : i ∈ d.blockOf b) (hj : j ∉ d.blockOf b) :
    Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  ⟨separatingFactor d b hi hj,
    (Semigroup.mem_center_iff).2 (separatingFactor_comm d b hi hj)⟩

/-- A central localized element which acts as `1` on one prescribed block
character and as `0` on every character outside the block. -/
private noncomputable def characterSelector
    (d : PrimeCongruenceBlockData p G) (b : d.I) (i : blockCharacterIndex d b) :
    Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  ∏ j : outsideCharacterIndex d b,
    separatingFactorCenter d b i.property j.property

private theorem characterSelector_action_self
    (d : PrimeCongruenceBlockData p G) (b : d.I) (i : blockCharacterIndex d b)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi i.1 = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (characterSelector d b i :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 1 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  change Φ (characterSelector d b i) = 1
  have hprod (s : Finset (outsideCharacterIndex d b)) :
      Φ (∏ j ∈ s, separatingFactorCenter d b i.property j.property) = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj, map_mul, ih, mul_one]
        change ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
          (separatingFactor d b i.property j.property)) = 1
        exact separatingFactor_action_self d b i.property j.property ρ hρ
  simpa only [characterSelector] using hprod Finset.univ

private theorem characterSelector_action_outside
    (d : PrimeCongruenceBlockData p G) (b : d.I) (i : blockCharacterIndex d b)
    (l : d.I) (hl : l ∉ d.blockOf b)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (characterSelector d b i :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 0 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  let j₀ : outsideCharacterIndex d b := ⟨l, hl⟩
  change Φ (characterSelector d b i) = 0
  rw [characterSelector]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j : outsideCharacterIndex d b =>
      separatingFactorCenter d b i.property j.property)
    (Finset.mem_univ j₀)]
  rw [map_mul]
  have hzero : Φ (separatingFactorCenter d b i.property j₀.property) = 0 := by
    change ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
      (separatingFactor d b i.property hl)) = 0
    exact separatingFactor_action_other d b i.property hl ρ hρ
  rw [hzero, zero_mul]

/-- The localized central element whose irreducible scalars are the
characteristic function of the chosen congruence block. -/
private noncomputable def localizedBlockIndicatorCenter
    (d : PrimeCongruenceBlockData p G) (b : d.I) :
    Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  1 - ∏ i : blockCharacterIndex d b, (1 - characterSelector d b i)

private theorem localizedBlockIndicator_action_mem
    (d : PrimeCongruenceBlockData p G) (b : d.I) (l : d.I) (hl : l ∈ d.blockOf b)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (localizedBlockIndicatorCenter d b :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 1 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  let i₀ : blockCharacterIndex d b := ⟨l, hl⟩
  change Φ (localizedBlockIndicatorCenter d b) = 1
  rw [localizedBlockIndicatorCenter, map_sub, map_one]
  have hfactor : Φ (1 - characterSelector d b i₀) = 0 := by
    rw [map_sub, map_one]
    change 1 - ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
      (characterSelector d b i₀ : A)) = 0
    rw [characterSelector_action_self d b i₀ ρ hρ]
    exact sub_self 1
  have hproduct :
      Φ (∏ i : blockCharacterIndex d b, (1 - characterSelector d b i)) = 0 := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i : blockCharacterIndex d b => 1 - characterSelector d b i)
      (Finset.mem_univ i₀)]
    rw [map_mul, hfactor, zero_mul]
  rw [hproduct, sub_zero]

private theorem localizedBlockIndicator_action_not_mem
    (d : PrimeCongruenceBlockData p G) (b : d.I) (l : d.I) (hl : l ∉ d.blockOf b)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (localizedBlockIndicatorCenter d b :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 0 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  change Φ (localizedBlockIndicatorCenter d b) = 0
  rw [localizedBlockIndicatorCenter, map_sub, map_one]
  have hprod (s : Finset (blockCharacterIndex d b)) :
      Φ (∏ i ∈ s, (1 - characterSelector d b i)) = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, map_mul, ih, mul_one]
        rw [map_sub, map_one]
        change 1 - ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
          (characterSelector d b i : A)) = 1
        rw [characterSelector_action_outside d b i l hl ρ hρ]
        exact sub_zero 1
  rw [hprod Finset.univ, sub_self]

/-- The integral-localized block element. -/
noncomputable def localizedBlockElement
    (d : PrimeCongruenceBlockData p G) (b : d.I) :
    MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G :=
  localizedBlockIndicatorCenter d b

/-- The complex block central element obtained by extending
coefficients from the localized cyclotomic order. -/
private noncomputable def blockElement
    (d : PrimeCongruenceBlockData p G) (b : d.I) : MonoidAlgebra ℂ G :=
  localizedGroupAlgebraToComplex d (localizedBlockElement d b)

private theorem blockElement_action
    (d : PrimeCongruenceBlockData p G) (b : d.I) (l : d.I)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (blockElement d b) =
      (if l ∈ d.blockOf b then (1 : ℂ) else 0) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  by_cases hl : l ∈ d.blockOf b
  · rw [if_pos hl, one_smul]
    exact localizedBlockIndicator_action_mem d b l hl ρ hρ
  · rw [if_neg hl, zero_smul]
    exact localizedBlockIndicator_action_not_mem d b l hl ρ hρ

private theorem map_localized_center_comm
    (d : PrimeCongruenceBlockData p G)
    (z : Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G))
    (a : MonoidAlgebra ℂ G) :
    a * localizedGroupAlgebraToComplex d
          (z : MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) =
      localizedGroupAlgebraToComplex d
          (z : MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      have hz := (Semigroup.mem_center_iff.mp z.property)
        (MonoidAlgebra.single g
          (1 : cyclotomicOrderAtPrime d.primeIdeal))
      have hzmap := congrArg (localizedGroupAlgebraToComplex d) hz
      have hzmap' :
          (MonoidAlgebra.single g (1 : ℂ)) *
              localizedGroupAlgebraToComplex d
                (z : MonoidAlgebra
                  (cyclotomicOrderAtPrime d.primeIdeal) G) =
            localizedGroupAlgebraToComplex d
                (z : MonoidAlgebra
                  (cyclotomicOrderAtPrime d.primeIdeal) G) *
              MonoidAlgebra.single g (1 : ℂ) := by
        simpa [localizedGroupAlgebraToComplex] using hzmap
      rw [show (MonoidAlgebra.single g r : MonoidAlgebra ℂ G) =
        r • MonoidAlgebra.single g 1 by simp]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      rw [hzmap']

theorem localizedBlockElement_mem_center
    (d : PrimeCongruenceBlockData p G) (b : d.I) :
    localizedBlockElement d b ∈
      Set.center
        (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  (localizedBlockIndicatorCenter d b).property

private theorem blockElement_comm
    (d : PrimeCongruenceBlockData p G) (b : d.I) (a : MonoidAlgebra ℂ G) :
    a * blockElement d b = blockElement d b * a :=
  map_localized_center_comm d (localizedBlockIndicatorCenter d b) a

private theorem blockElement_mem_center
    (d : PrimeCongruenceBlockData p G) (b : d.I) :
    blockElement d b ∈ Set.center (MonoidAlgebra ℂ G) :=
  (Semigroup.mem_center_iff).2 (blockElement_comm d b)

theorem localizationToComplex_injective
    (d : PrimeCongruenceBlockData p G) :
    Function.Injective (localizationToComplex d.primeIdeal) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    d.primeIdeal.primeCompl (localizationToComplex d.primeIdeal)).2
  intro x y
  constructor
  · intro h
    exact congrArg (localizationToComplex d.primeIdeal) h
  · intro h
    have hcoe : (x : ℂ) = (y : ℂ) := by
      simpa only [localizationToComplex_algebraMap] using h
    have hxy : x = y := Subtype.ext hcoe
    rw [hxy]

private theorem localizedGroupAlgebraToComplex_injective
    (d : PrimeCongruenceBlockData p G) :
    Function.Injective (localizedGroupAlgebraToComplex d) := by
  intro x y hxy
  ext g
  apply localizationToComplex_injective d
  have hg := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff g) hxy
  simpa [localizedGroupAlgebraToComplex,
    MonoidAlgebra.coeff_mapRingHom] using hg

private theorem blockElement_coeff_eq_localized
    (d : PrimeCongruenceBlockData p G) (b : d.I) (g : G) :
    (blockElement d b).coeff g =
      localizationToComplex d.primeIdeal
        ((localizedBlockElement d b).coeff g) := by
  change (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)
      (localizedBlockElement d b)).coeff g =
    localizationToComplex d.primeIdeal
      ((localizedBlockElement d b).coeff g)
  exact MonoidAlgebra.coeff_mapRingHom _ _ _

/-- Coefficient formula for an arbitrary complex block projector. -/
private theorem blockElement_coeff
    (d : PrimeCongruenceBlockData p G) (b : d.I) (g : G) :
    (blockElement d b).coeff g =
      (Nat.card G : ℂ)⁻¹ *
        ∑ i ∈ d.blockOf b,
          d.chi i (ConjClasses.mk (1 : G)) *
            d.chi i (ConjClasses.mk g⁻¹) := by
  classical
  have hcoeff := coeff_eq_inv_card_mul_sum_scalar_degree_character
    d.chi d.complete (blockElement d b)
    (blockElement_comm d b)
    (fun i : d.I => if i ∈ d.blockOf b then 1 else 0)
    (by
      intro i n ρ hρ
      exact blockElement_action d b i ρ hρ)
    g
  rw [hcoeff]
  congr 1
  simp [PrimeCongruenceBlockData.blockOf, Finset.sum_filter]

private theorem blockElement_isIdempotent
    (d : PrimeCongruenceBlockData p G) (b : d.I) :
    IsIdempotentElem (blockElement d b) := by
  classical
  let e := blockElement d b
  have hecenter : e ∈ Set.center (MonoidAlgebra ℂ G) :=
    blockElement_mem_center d b
  have hdiffcenter : e * e - e ∈ Set.center (MonoidAlgebra ℂ G) := by
    rw [sub_eq_add_neg]
    exact Set.add_mem_center (Set.mul_mem_center hecenter hecenter)
      (Set.neg_mem_center hecenter)
  have hdiffcomm : ∀ a : MonoidAlgebra ℂ G,
      a * (e * e - e) = (e * e - e) * a :=
    (Semigroup.mem_center_iff.mp hdiffcenter)
  have haction : ∀ i : d.I, ∀ {n : ℕ}
      (ρ : Representation ℂ G (Fin n → ℂ)),
      d.chi i = (characterClassFunction ρ) →
      ρ.asAlgebraHom (e * e - e) =
        (0 : ℂ) • (1 : Module.End ℂ (Fin n → ℂ)) := by
    intro i n ρ hρ
    rw [map_sub, map_mul]
    change ρ.asAlgebraHom (blockElement d b) *
        ρ.asAlgebraHom (blockElement d b) -
      ρ.asAlgebraHom (blockElement d b) =
        (0 : ℂ) • (1 : Module.End ℂ (Fin n → ℂ))
    rw [blockElement_action d b i ρ hρ]
    by_cases hi : i ∈ d.blockOf b <;> simp [hi]
  have hdiffzero : e * e - e = 0 := by
    ext g
    change (e * e - e).coeff g = 0
    have hcoeff := coeff_eq_inv_card_mul_sum_scalar_degree_character
      d.chi d.complete (e * e - e) hdiffcomm
      (fun _i : d.I => (0 : ℂ)) haction g
    simpa using hcoeff
  change e * e = e
  exact sub_eq_zero.mp hdiffzero

theorem localizedBlockElement_isIdempotent
    (d : PrimeCongruenceBlockData p G) (b : d.I) :
    IsIdempotentElem (localizedBlockElement d b) := by
  change localizedBlockElement d b * localizedBlockElement d b =
    localizedBlockElement d b
  apply localizedGroupAlgebraToComplex_injective d
  rw [map_mul]
  change blockElement d b * blockElement d b =
    blockElement d b
  exact blockElement_isIdempotent d b


/-- The coefficient formula for the localized block projector. -/
theorem localizedBlockElement_coeff
    (d : PrimeCongruenceBlockData p G) (b : d.I) (g : G) :
    localizationToComplex d.primeIdeal ((localizedBlockElement d b).coeff g) =
      (Nat.card G : ℂ)⁻¹ * ∑ i ∈ d.blockOf b,
        d.chi i (ConjClasses.mk 1) * d.chi i (ConjClasses.mk g⁻¹) := by
  rw [← blockElement_coeff_eq_localized, blockElement_coeff]

/-- Every congruence block admits an actual localized central idempotent,
with the ordinary character coefficient formula of Brauer--Tuan (2.3). -/
theorem exists_localizedBlockProjector
    (d : PrimeCongruenceBlockData p G) (b : d.I) :
    ∃ e : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G,
      IsIdempotentElem e ∧ e ∈ Set.center (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) ∧
      ∀ g : G, localizationToComplex d.primeIdeal (e.coeff g) =
        (Nat.card G : ℂ)⁻¹ * ∑ i ∈ d.blockOf b,
          d.chi i (ConjClasses.mk 1) * d.chi i (ConjClasses.mk g⁻¹) :=
  ⟨localizedBlockElement d b, localizedBlockElement_isIdempotent d b,
    localizedBlockElement_mem_center d b, localizedBlockElement_coeff d b⟩

/-- The localized cyclotomic order has characteristic zero. -/
instance localization_charZero (d : PrimeCongruenceBlockData p G) :
    CharZero (Localization.AtPrime d.primeIdeal) where
  cast_injective m n hmn := by
    apply CharZero.cast_injective (R := ℂ)
    have hmap := congrArg (localizationToComplex d.primeIdeal) hmn
    simpa using hmap

/-- The rational prime lies in the chosen prime ideal. -/
theorem prime_mem_primeIdeal (d : PrimeCongruenceBlockData p G) :
    (p : cyclotomicOrder d.eta) ∈ d.primeIdeal := by
  let : d.primeIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) :=
    d.primeIdeal_liesOver
  have h := (Ideal.mem_of_liesOver d.primeIdeal
    (Ideal.span ({(p : ℤ)} : Set ℤ)) (p : ℤ)).mp
    (Ideal.subset_span (Set.mem_singleton _))
  simpa only [map_natCast] using h

/-- A prime below the localization ideal cannot become a unit. -/
theorem prime_not_isUnit (d : PrimeCongruenceBlockData p G) :
    ¬ IsUnit (p : Localization.AtPrime d.primeIdeal) := by
  intro hunit
  have hunit' : IsUnit (algebraMap (cyclotomicOrder d.eta)
      (Localization.AtPrime d.primeIdeal) (p : cyclotomicOrder d.eta)) := by
    simpa only [map_natCast] using hunit
  rw [← IsLocalization.mk'_one (M := d.primeIdeal.primeCompl)
      (Localization.AtPrime d.primeIdeal) (p : cyclotomicOrder d.eta),
    IsLocalization.AtPrime.isUnit_mk'_iff
      (Localization.AtPrime d.primeIdeal) d.primeIdeal] at hunit'
  exact hunit' (prime_mem_primeIdeal d)

/-- The localization contains primitive roots for every divisor of the group order. -/
theorem exists_localization_primitiveRoot (d : PrimeCongruenceBlockData p G)
    (m : ℕ) (hm : m ∣ Nat.card G) :
    ∃ ζ : Localization.AtPrime d.primeIdeal, IsPrimitiveRoot ζ m := by
  let ζ : cyclotomicOrder d.eta :=
    ⟨d.eta ^ (Nat.card G / m), pow_mem_cyclotomicOrder
      (eta_mem_cyclotomicOrder d.eta) _⟩
  refine ⟨algebraMap _ _ ζ, ?_⟩
  apply IsPrimitiveRoot.of_map_of_injective (f := localizationToComplex d.primeIdeal)
    _ (localizationToComplex_injective d)
  rw [localizationToComplex_algebraMap]
  exact d.eta_spec.pow Nat.card_pos (Nat.div_mul_cancel hm).symm

end PrimeSelector
end ModularBlock.PrimeBlockConstruction
