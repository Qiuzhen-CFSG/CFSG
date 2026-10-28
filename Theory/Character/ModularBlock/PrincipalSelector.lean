module

public import Theory.Character.ModularBlock.Congruence
public import Theory.Character.ModularBlock.ClassSumAction
public import Theory.Comparator.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The localized principal-block selector

For a finite group, construct a central element over the cyclotomic order
localized at a prime above two, acting by one on the chosen principal
congruence block and by zero on the other irreducibles.

Distinct congruence blocks have a separating class sum whose central
character difference becomes a unit. Products of normalized separating
factors select one block character against all outside characters; the
complement of the product of their complements selects the whole block.
The chosen conjugacy classes and interpolation products remain private.
The coefficient map is exposed because scalar extension is the public
construction used to transfer idempotence. Injectivity and coefficient
formulas form its boundary for the final principal-element module.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BlockOrthogonality.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.BlockOrthogonality

open BlockPreliminaries PrincipalBlockConstruction

attribute [local instance] Fintype.ofFinite

universe u v w

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

section LocalBlockElement

variable {G : Type u} [Group G] [Finite G]

abbrev cyclotomicOrderAtPrime
    {eta : ℂ} (P : Ideal (cyclotomicOrder eta))
    [P.IsPrime] : Type _ :=
  Localization.AtPrime P

noncomputable def localizationToComplex
    {eta : ℂ} (P : Ideal (cyclotomicOrder eta))
    [P.IsPrime] :
    cyclotomicOrderAtPrime P →+* ℂ := by
  let A := cyclotomicOrder eta
  let f : A →+* ℂ := Subring.subtype A
  exact IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
    (g := f) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      intro hy
      apply y.2
      have hyA : (y.1 : ℂ) = 0 := by
        simpa [f] using hy
      have hyzero : y.1 = 0 := Subtype.ext hyA
      rw [hyzero]
      exact P.zero_mem)

theorem localizationToComplex_algebraMap
    {eta : ℂ} (P : Ideal (cyclotomicOrder eta))
    [P.IsPrime] (a : cyclotomicOrder eta) :
    localizationToComplex P (algebraMap _ _ a) = (a : ℂ) := by
  apply IsLocalization.lift_eq

end LocalBlockElement

section BlockIndicator

variable {G : Type u} [Group G] [Finite G]

instance principalPrimeIdeal_isPrime
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

private theorem exists_separating_class
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
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
    apply (d.mem_block_iff j).2
    exact sameTwoBlock_trans d.eta_spec d.primeIdeal
      (sameTwoBlock_symm d.eta_spec d.primeIdeal
        h)
      ((d.mem_block_iff i).1 hi)
  by_contra hsep
  apply hij
  apply (sameTwoBlock_iff d.eta_spec d.primeIdeal
    (d.chi i) (d.chi j) (d.complete.1 i) (d.complete.1 j)).2
  intro c
  by_contra hc
  exact hsep ⟨c, hc⟩

private noncomputable def separatingClass
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) : ConjClasses G :=
  Classical.choose (exists_separating_class d hi hj)

private theorem separatingClass_spec
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) -
        centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) ∉ d.primeIdeal :=
  Classical.choose_spec (exists_separating_class d hi hj)

private noncomputable def localizedCentralCharacter
    (d : PrincipalCongruenceBlockData G) (i : d.I) (c : ConjClasses G) :
    cyclotomicOrderAtPrime d.primeIdeal :=
  algebraMap _ _ (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
    (d.complete.1 i) c)

private theorem localizationToComplex_localizedCentralCharacter
    (d : PrincipalCongruenceBlockData G) (i : d.I) (c : ConjClasses G) :
    localizationToComplex d.primeIdeal (localizedCentralCharacter d i c) =
      (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
        (d.complete.1 i) c : ℂ) := by
  exact localizationToComplex_algebraMap d.primeIdeal _

private noncomputable def denominatorInverse
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    cyclotomicOrderAtPrime d.primeIdeal := by
  let a := centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
      (d.complete.1 i) (separatingClass d hi hj) -
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
      (d.complete.1 j) (separatingClass d hi hj)
  let hmem : a ∈ d.primeIdeal.primeCompl :=
    show a ∉ d.primeIdeal from separatingClass_spec d hi hj
  exact IsLocalization.mk' (Localization.AtPrime d.primeIdeal) 1 ⟨a, hmem⟩

private theorem denominatorInverse_map
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    localizationToComplex d.primeIdeal
        (denominatorInverse d hi hj) =
      ((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹ := by
  classical
  let A := cyclotomicOrder d.eta
  let a := centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
      (d.complete.1 i) (separatingClass d hi hj) -
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
      (d.complete.1 j) (separatingClass d hi hj)
  let hmem : a ∈ d.primeIdeal.primeCompl :=
    separatingClass_spec d hi hj
  simp only [denominatorInverse]
  rw [show localizationToComplex d.primeIdeal =
      IsLocalization.lift (M := d.primeIdeal.primeCompl)
        (S := Localization.AtPrime d.primeIdeal)
        (g := Subring.subtype (cyclotomicOrder d.eta))
        (by
          intro y
          apply isUnit_iff_ne_zero.mpr
          intro hy
          apply y.2
          have hyA : (y.1 : ℂ) = 0 := hy
          have hyzero : y.1 = 0 := Subtype.ext hyA
          rw [hyzero]
          exact d.primeIdeal.zero_mem) by rfl]
  rw [IsLocalization.lift_mk']
  simp [IsUnit.coe_liftRight]

@[expose] noncomputable def localizedGroupAlgebraToComplex
    (d : PrincipalCongruenceBlockData G) :
    MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G →+*
      MonoidAlgebra ℂ G :=
  MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)

/-- A localized class-sum polynomial which acts as `1` on `i` and as `0`
on `j`. -/
private noncomputable def separatingFactor
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G :=
  MonoidAlgebra.single 1 (denominatorInverse d hi hj) *
    (classSum (cyclotomicOrderAtPrime d.primeIdeal)
        (separatingClass d hi hj) -
      MonoidAlgebra.single 1
        (localizedCentralCharacter d j (separatingClass d hi hj)))

private theorem map_separatingFactor
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    localizedGroupAlgebraToComplex d (separatingFactor d hi hj) =
      (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹) •
        (classSum ℂ (separatingClass d hi hj) -
          (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
            (d.complete.1 j) (separatingClass d hi hj) : ℂ) • 1) := by
  classical
  simp only [separatingFactor, localizedGroupAlgebraToComplex, map_mul,
    map_sub, MonoidAlgebra.mapRingHom_single, mapRingHom_classSum]
  rw [show localizationToComplex d.primeIdeal
      (denominatorInverse d hi hj) =
        ((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
          (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
            (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹ by
      exact denominatorInverse_map d hi hj]
  have hsingle (r : ℂ) :
      (MonoidAlgebra.single 1 r : MonoidAlgebra ℂ G) = r • 1 := by
    simp [MonoidAlgebra.one_def]
  calc
    MonoidAlgebra.single 1
          (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
            (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
              (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
                (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹) *
        (classSum ℂ (separatingClass d hi hj) -
          MonoidAlgebra.single 1
            (localizationToComplex d.primeIdeal
              (localizedCentralCharacter d j (separatingClass d hi hj)))) =
      (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹) •
        (classSum ℂ (separatingClass d hi hj) -
          MonoidAlgebra.single 1
            (localizationToComplex d.primeIdeal
              (localizedCentralCharacter d j (separatingClass d hi hj)))) := by
      exact single_one_mul_eq_smul _ _
    _ = (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹) •
        (classSum ℂ (separatingClass d hi hj) -
          (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
            (d.complete.1 j) (separatingClass d hi hj) : ℂ) • 1) := by
      rw [localizationToComplex_localizedCentralCharacter,
        hsingle]

private theorem separatingFactor_comm
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block)
    (a : MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :
    a * separatingFactor d hi hj = separatingFactor d hi hj * a := by
  classical
  rw [separatingFactor]
  have hdenom :
      a * MonoidAlgebra.single 1 (denominatorInverse d hi hj) =
        MonoidAlgebra.single 1 (denominatorInverse d hi hj) * a := by
    ext x
    simp [mul_comm]
  let x := classSum (cyclotomicOrderAtPrime d.primeIdeal)
      (separatingClass d hi hj) -
    MonoidAlgebra.single 1
      (localizedCentralCharacter d j (separatingClass d hi hj))
  have hx : a * x = x * a := by
    have hclass : classSum (cyclotomicOrderAtPrime d.primeIdeal)
        (separatingClass d hi hj) ∈
        Set.center (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
      (Semigroup.mem_center_iff).2
        (classSum_comm (cyclotomicOrderAtPrime d.primeIdeal)
          (separatingClass d hi hj))
    have hscalar : MonoidAlgebra.single 1
        (localizedCentralCharacter d j (separatingClass d hi hj)) ∈
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
    a * (MonoidAlgebra.single 1 (denominatorInverse d hi hj) * x) =
        (a * MonoidAlgebra.single 1 (denominatorInverse d hi hj)) * x :=
      (mul_assoc _ _ _).symm
    _ = (MonoidAlgebra.single 1 (denominatorInverse d hi hj) * a) * x := by
      rw [hdenom]
    _ = MonoidAlgebra.single 1 (denominatorInverse d hi hj) * (a * x) :=
      mul_assoc _ _ _
    _ = MonoidAlgebra.single 1 (denominatorInverse d hi hj) * (x * a) := by
      rw [hx]
    _ = (MonoidAlgebra.single 1 (denominatorInverse d hi hj) * x) * a :=
      (mul_assoc _ _ _).symm

private theorem separatingDifference_ne_zero
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ) ≠ 0 := by
  intro hzero
  apply separatingClass_spec d hi hj
  have hzero' :
      centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) -
        centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) = 0 := by
    apply Subtype.ext
    exact hzero
  rw [hzero']
  exact d.primeIdeal.zero_mem

private theorem separatingFactor_action
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block)
    (l : d.I) {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (separatingFactor d hi hj)) =
      (((centralCharacterInCyclotomicOrder d.eta_spec (d.chi i)
          (d.complete.1 i) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))⁻¹ *
        ((centralCharacterInCyclotomicOrder d.eta_spec (d.chi l)
          (d.complete.1 l) (separatingClass d hi hj) : ℂ) -
        (centralCharacterInCyclotomicOrder d.eta_spec (d.chi j)
          (d.complete.1 j) (separatingClass d hi hj) : ℂ))) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  have hρirr : Representation.IsIrreducible ρ := by
    apply (irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using (d.complete.1 l).2
  let : Representation.IsIrreducible ρ := hρirr
  let c := separatingClass d hi hj
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
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi i = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (separatingFactor d hi hj)) = 1 := by
  rw [separatingFactor_action d hi hj i ρ hρ]
  rw [inv_mul_cancel₀ (separatingDifference_ne_zero d hi hj)]
  exact one_smul ℂ _

private theorem separatingFactor_action_other
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi j = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (separatingFactor d hi hj)) = 0 := by
  rw [separatingFactor_action d hi hj j ρ hρ]
  simp

private abbrev blockCharacterIndex (d : PrincipalCongruenceBlockData G) :=
  {i : d.I // i ∈ d.block}

private abbrev outsideCharacterIndex (d : PrincipalCongruenceBlockData G) :=
  {j : d.I // j ∉ d.block}

private instance localizedCenterCommRing
    (d : PrincipalCongruenceBlockData G) :
    CommRing (Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) :=
  @Subring.instCommRingSubtypeMemCenter _
    (inferInstance : Ring
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G))

private noncomputable def separatingFactorCenter
    (d : PrincipalCongruenceBlockData G)
    {i j : d.I} (hi : i ∈ d.block) (hj : j ∉ d.block) :
    Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  ⟨separatingFactor d hi hj,
    (Semigroup.mem_center_iff).2 (separatingFactor_comm d hi hj)⟩

/-- A central localized element which acts as `1` on one prescribed block
character and as `0` on every character outside the block. -/
private noncomputable def characterSelector
    (d : PrincipalCongruenceBlockData G) (i : blockCharacterIndex d) :
    Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  ∏ j : outsideCharacterIndex d,
    separatingFactorCenter d i.property j.property

private theorem characterSelector_action_self
    (d : PrincipalCongruenceBlockData G) (i : blockCharacterIndex d)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi i.1 = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (characterSelector d i :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 1 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  change Φ (characterSelector d i) = 1
  have hprod (s : Finset (outsideCharacterIndex d)) :
      Φ (∏ j ∈ s, separatingFactorCenter d i.property j.property) = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj, map_mul, ih, mul_one]
        change ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
          (separatingFactor d i.property j.property)) = 1
        exact separatingFactor_action_self d i.property j.property ρ hρ
  simpa only [characterSelector] using hprod Finset.univ

private theorem characterSelector_action_outside
    (d : PrincipalCongruenceBlockData G) (i : blockCharacterIndex d)
    (l : d.I) (hl : l ∉ d.block)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (characterSelector d i :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 0 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  let j₀ : outsideCharacterIndex d := ⟨l, hl⟩
  change Φ (characterSelector d i) = 0
  rw [characterSelector]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j : outsideCharacterIndex d =>
      separatingFactorCenter d i.property j.property)
    (Finset.mem_univ j₀)]
  rw [map_mul]
  have hzero : Φ (separatingFactorCenter d i.property j₀.property) = 0 := by
    change ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
      (separatingFactor d i.property hl)) = 0
    exact separatingFactor_action_other d i.property hl ρ hρ
  rw [hzero, zero_mul]

/-- The localized central element whose irreducible scalars are the
characteristic function of the principal congruence block. -/
private noncomputable def localizedBlockIndicatorCenter
    (d : PrincipalCongruenceBlockData G) :
    Subring.center
      (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  1 - ∏ i : blockCharacterIndex d, (1 - characterSelector d i)

private theorem localizedBlockIndicator_action_mem
    (d : PrincipalCongruenceBlockData G) (l : d.I) (hl : l ∈ d.block)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (localizedBlockIndicatorCenter d :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 1 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  let i₀ : blockCharacterIndex d := ⟨l, hl⟩
  change Φ (localizedBlockIndicatorCenter d) = 1
  rw [localizedBlockIndicatorCenter, map_sub, map_one]
  have hfactor : Φ (1 - characterSelector d i₀) = 0 := by
    rw [map_sub, map_one]
    change 1 - ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
      (characterSelector d i₀ : A)) = 0
    rw [characterSelector_action_self d i₀ ρ hρ]
    exact sub_self 1
  have hproduct :
      Φ (∏ i : blockCharacterIndex d, (1 - characterSelector d i)) = 0 := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i : blockCharacterIndex d => 1 - characterSelector d i)
      (Finset.mem_univ i₀)]
    rw [map_mul, hfactor, zero_mul]
  rw [hproduct, sub_zero]

private theorem localizedBlockIndicator_action_not_mem
    (d : PrincipalCongruenceBlockData G) (l : d.I) (hl : l ∉ d.block)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
        (localizedBlockIndicatorCenter d :
          MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G)) = 0 := by
  classical
  let A := MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G
  let Φ : Subring.center A →+* Module.End ℂ (Fin n → ℂ) :=
    ρ.asAlgebraHom.toRingHom.comp
      ((localizedGroupAlgebraToComplex d).comp
        (Subring.subtype (Subring.center A)))
  change Φ (localizedBlockIndicatorCenter d) = 0
  rw [localizedBlockIndicatorCenter, map_sub, map_one]
  have hprod (s : Finset (blockCharacterIndex d)) :
      Φ (∏ i ∈ s, (1 - characterSelector d i)) = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, map_mul, ih, mul_one]
        rw [map_sub, map_one]
        change 1 - ρ.asAlgebraHom (localizedGroupAlgebraToComplex d
          (characterSelector d i : A)) = 1
        rw [characterSelector_action_outside d i l hl ρ hρ]
        exact sub_zero 1
  rw [hprod Finset.univ, sub_self]

/-- The integral-localized principal-block element. -/
noncomputable def localizedPrincipalBlockElement
    (d : PrincipalCongruenceBlockData G) :
    MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G :=
  localizedBlockIndicatorCenter d

/-- The complex principal-block central element obtained by extending
coefficients from the localized cyclotomic order. -/
@[expose] noncomputable def principalBlockElement
    (d : PrincipalCongruenceBlockData G) : MonoidAlgebra ℂ G :=
  localizedGroupAlgebraToComplex d (localizedPrincipalBlockElement d)

/-- The complex principal-block element is independent of the presentation of
the canonical localization lift.  This lets downstream arguments use their
own named copy of the localization-to-`ℂ` homomorphism. -/
theorem mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
    (d : PrincipalCongruenceBlockData G)
    (f : cyclotomicOrderAtPrime d.primeIdeal →+* ℂ)
    (hf : ∀ a : cyclotomicOrder d.eta,
      f (algebraMap _ (cyclotomicOrderAtPrime d.primeIdeal) a) = (a : ℂ)) :
    MonoidAlgebra.mapRingHom G f (localizedPrincipalBlockElement d) =
      principalBlockElement d := by
  change MonoidAlgebra.mapRingHom G f (localizedPrincipalBlockElement d) =
    MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)
      (localizedPrincipalBlockElement d)
  have hfg : f = localizationToComplex d.primeIdeal := by
    apply IsLocalization.ringHom_ext d.primeIdeal.primeCompl
    apply RingHom.ext
    intro a
    change f (algebraMap _ (cyclotomicOrderAtPrime d.primeIdeal) a) =
      localizationToComplex d.primeIdeal
        (algebraMap _ (cyclotomicOrderAtPrime d.primeIdeal) a)
    rw [hf, localizationToComplex_algebraMap]
  rw [hfg]

theorem principalBlockElement_action
    (d : PrincipalCongruenceBlockData G) (l : d.I)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi l = (characterClassFunction ρ)) :
    ρ.asAlgebraHom (principalBlockElement d) =
      (if l ∈ d.block then (1 : ℂ) else 0) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  by_cases hl : l ∈ d.block
  · rw [if_pos hl, one_smul]
    exact localizedBlockIndicator_action_mem d l hl ρ hρ
  · rw [if_neg hl, zero_smul]
    exact localizedBlockIndicator_action_not_mem d l hl ρ hρ

private theorem map_localized_center_comm
    (d : PrincipalCongruenceBlockData G)
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

theorem localizedPrincipalBlockElement_mem_center
    (d : PrincipalCongruenceBlockData G) :
    localizedPrincipalBlockElement d ∈
      Set.center
        (MonoidAlgebra (cyclotomicOrderAtPrime d.primeIdeal) G) :=
  (localizedBlockIndicatorCenter d).property

theorem principalBlockElement_comm
    (d : PrincipalCongruenceBlockData G) (a : MonoidAlgebra ℂ G) :
    a * principalBlockElement d = principalBlockElement d * a :=
  map_localized_center_comm d (localizedBlockIndicatorCenter d) a

theorem principalBlockElement_mem_center
    (d : PrincipalCongruenceBlockData G) :
    principalBlockElement d ∈ Set.center (MonoidAlgebra ℂ G) :=
  (Semigroup.mem_center_iff).2 (principalBlockElement_comm d)

theorem localizationToComplex_injective
    (d : PrincipalCongruenceBlockData G) :
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

instance cyclotomicOrderAtPrime_charZero
    (d : PrincipalCongruenceBlockData G) :
    CharZero (cyclotomicOrderAtPrime d.primeIdeal) where
  cast_injective m n hmn := by
    apply CharZero.cast_injective (R := ℂ)
    have hmap := congrArg (localizationToComplex d.primeIdeal) hmn
    simpa using hmap

theorem two_not_isUnit_cyclotomicOrderAtPrime
    (d : PrincipalCongruenceBlockData G) :
    ¬ IsUnit (2 : cyclotomicOrderAtPrime d.primeIdeal) := by
  intro hunit
  have hunit' : IsUnit
      (algebraMap (cyclotomicOrder d.eta)
        (cyclotomicOrderAtPrime d.primeIdeal)
        (2 : cyclotomicOrder d.eta)) := by
    simpa only [map_ofNat] using hunit
  rw [← IsLocalization.mk'_one
    (M := d.primeIdeal.primeCompl)
    (cyclotomicOrderAtPrime d.primeIdeal)
      (2 : cyclotomicOrder d.eta),
    IsLocalization.AtPrime.isUnit_mk'_iff
      (cyclotomicOrderAtPrime d.primeIdeal) d.primeIdeal] at hunit'
  exact hunit' (two_mem_of_liesOver d.primeIdeal
    d.primeIdeal_liesOverTwo)

omit [Finite G] in
theorem card_zpowers_eq_two_of_isInvolution
    (s : G) (hs : IsInvolution s) :
    Nat.card (Subgroup.zpowers s) = 2 :=
  (Nat.card_zpowers s).trans (orderOf_eq_prime hs.2 hs.1)

theorem localizedGroupAlgebraToComplex_injective
    (d : PrincipalCongruenceBlockData G) :
    Function.Injective (localizedGroupAlgebraToComplex d) := by
  intro x y hxy
  ext g
  apply localizationToComplex_injective d
  have hg := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff g) hxy
  simpa [localizedGroupAlgebraToComplex,
    MonoidAlgebra.coeff_mapRingHom] using hg

theorem principalBlockElement_coeff_eq_localized
    (d : PrincipalCongruenceBlockData G) (g : G) :
    (principalBlockElement d).coeff g =
      localizationToComplex d.primeIdeal
        ((localizedPrincipalBlockElement d).coeff g) := by
  change (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)
      (localizedPrincipalBlockElement d)).coeff g =
    localizationToComplex d.primeIdeal
      ((localizedPrincipalBlockElement d).coeff g)
  exact MonoidAlgebra.coeff_mapRingHom _ _ _

end BlockIndicator

end ModularBlock.BlockOrthogonality
