import Submission.ZStar.CyclotomicDVR
import Submission.ZStar.CompatibleBrauerBlock
import Submission.ZStar.CentralScalarCongruence
import Submission.ZStar.CentralLift
import Submission.ZStar.FiniteFieldPrimitivity

/-!
# Primitivity of reduced congruence-block selectors

This file develops the valuation argument used to prove that the reduction of
an ordinary congruence-block selector is centrally primitive.  The first lemma
is the DVR denominator-absorption step: a sufficiently high power of any
nonunit is divisible by a prescribed nonzero denominator, with a nonunit
quotient.
-/

noncomputable section

namespace Submission.ZStar

namespace BlockPrimitivity

/-- In a DVR, a sufficiently high power of a nonunit absorbs any prescribed
nonzero denominator and still leaves a nonunit quotient. -/
theorem exists_pow_eq_mul_nonunit
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a n : R) (ha : ¬ IsUnit a) (hn : n ≠ 0) :
    ∃ N : ℕ, ∃ q : R, 0 < N ∧ a ^ N = n * q ∧ ¬ IsUnit q := by
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible R
  by_cases ha0 : a = 0
  · refine ⟨1, 0, by omega, ?_, ?_⟩
    · simp [ha0]
    · exact not_isUnit_zero
  obtain ⟨t, u, hneq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hpi
  obtain ⟨s, v, haeq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hpi
  have hs : 0 < s := by
    by_contra hs0
    have hs0' : s = 0 := Nat.eq_zero_of_not_pos hs0
    apply ha
    rw [haeq, hs0', pow_zero, mul_one]
    exact v.isUnit
  let N := t + 1
  let k := s * N - t
  let w : Rˣ := u⁻¹ * v ^ N
  refine ⟨N, (w : R) * pi ^ k, by simp [N], ?_, ?_⟩
  · rw [haeq, hneq, mul_pow, ← pow_mul]
    have hle : t ≤ s * N := by
      dsimp only [N]
      nlinarith
    have htk : t + k = s * N := by
      dsimp only [k]
      omega
    have hpipow : pi ^ (s * N) = pi ^ t * pi ^ k := by
      rw [← htk, pow_add]
    rw [hpipow]
    dsimp only [w]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    have hu : (u : R) * (↑(u⁻¹) : R) = 1 := by simp
    calc
      (v : R) ^ N * (pi ^ t * pi ^ k) =
          ((u : R) * (↑(u⁻¹) : R)) *
            ((v : R) ^ N * (pi ^ t * pi ^ k)) := by rw [hu, one_mul]
      _ = ((u : R) * pi ^ t) *
          (((↑(u⁻¹) : R) * (v : R) ^ N) * pi ^ k) := by ring
  · intro hunit
    have hpowunit : IsUnit (pi ^ k) :=
      (IsUnit.mul_iff.mp hunit).2
    have hk0 : k = 0 :=
      (isUnit_pow_iff_of_not_isUnit hpi.not_isUnit).mp hpowunit
    dsimp only [k, N] at hk0
    have hle : t < s * (t + 1) := by
      nlinarith
    omega

/-- The exponent in the preceding lemma can be chosen uniformly for all
nonunits; it depends only on the denominator. -/
theorem exists_uniform_pow_eq_mul_nonunit
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (n : R) (hn : n ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : R, ¬ IsUnit a →
      ∃ q : R, a ^ N = n * q ∧ ¬ IsUnit q := by
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨t, u, hneq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hpi
  let N := t + 1
  refine ⟨N, by simp [N], ?_⟩
  intro a ha
  by_cases ha0 : a = 0
  · refine ⟨0, ?_, not_isUnit_zero⟩
    simp [ha0]
  obtain ⟨s, v, haeq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hpi
  have hs : 0 < s := by
    by_contra hs0
    have hs0' : s = 0 := Nat.eq_zero_of_not_pos hs0
    apply ha
    rw [haeq, hs0', pow_zero, mul_one]
    exact v.isUnit
  let k := s * N - t
  let w : Rˣ := u⁻¹ * v ^ N
  refine ⟨(w : R) * pi ^ k, ?_, ?_⟩
  · rw [haeq, hneq, mul_pow, ← pow_mul]
    have hle : t ≤ s * N := by
      dsimp only [N]
      nlinarith
    have htk : t + k = s * N := by
      dsimp only [k]
      omega
    have hpipow : pi ^ (s * N) = pi ^ t * pi ^ k := by
      rw [← htk, pow_add]
    rw [hpipow]
    dsimp only [w]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    have hu : (u : R) * (↑(u⁻¹) : R) = 1 := by simp
    calc
      (v : R) ^ N * (pi ^ t * pi ^ k) =
          ((u : R) * (↑(u⁻¹) : R)) *
            ((v : R) ^ N * (pi ^ t * pi ^ k)) := by rw [hu, one_mul]
      _ = ((u : R) * pi ^ t) *
          (((↑(u⁻¹) : R) * (v : R) ^ N) * pi ^ k) := by ring
  · intro hunit
    have hpowunit : IsUnit (pi ^ k) :=
      (IsUnit.mul_iff.mp hunit).2
    have hk0 : k = 0 :=
      (isUnit_pow_iff_of_not_isUnit hpi.not_isUnit).mp hpowunit
    dsimp only [k, N] at hk0
    have hle : t < s * (t + 1) := by
      nlinarith
    omega

attribute [local instance] Fintype.ofFinite

private instance principalPrime_isPrime
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

/-- The canonical embedding of the localized cyclotomic order into `ℂ`. -/
private noncomputable def localizationToComplex
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    Localization.AtPrime d.primeIdeal →+* ℂ := by
  let A := Representation.cyclotomicOrder d.eta
  let f : A →+* ℂ := Subring.subtype A
  exact IsLocalization.lift
    (M := d.primeIdeal.primeCompl)
    (S := Localization.AtPrime d.primeIdeal)
    (g := f) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      intro hy
      apply y.2
      have hyA : (y.1 : ℂ) = 0 := by
        simpa [f] using hy
      have hyzero : y.1 = 0 := Subtype.ext hyA
      rw [hyzero]
      exact d.primeIdeal.zero_mem)

private theorem localizationToComplex_algebraMap
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (a : Representation.cyclotomicOrder d.eta) :
    localizationToComplex d
        (algebraMap _ (Localization.AtPrime d.primeIdeal) a) = (a : ℂ) := by
  apply IsLocalization.lift_eq

private theorem localizationToComplex_injective
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    Function.Injective (localizationToComplex d) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    d.primeIdeal.primeCompl (localizationToComplex d)).2
  intro x y
  constructor
  · intro h
    exact congrArg (localizationToComplex d) h
  · intro h
    have hcoe : (x : ℂ) = (y : ℂ) := by
      simpa only [localizationToComplex_algebraMap] using h
    have hxy : x = y := Subtype.ext hcoe
    rw [hxy]

/-! The next private lemmas identify `localizedCentralScalar` with the
actual scalar action on an irreducible complex representation.  Keeping this
identification explicit lets us use multiplicativity of the representation
while retaining the integral scalar supplied by the localized cyclotomic
order. -/

private noncomputable def classSet
    {G : Type*} [Group G] [Finite G] (c : ConjClasses G) : Finset G :=
  letI : DecidableEq (ConjClasses G) := Classical.decEq (ConjClasses G)
  Finset.univ.filter fun g : G => ConjClasses.mk g = c

private theorem mem_classSet_iff
    {G : Type*} [Group G] [Finite G]
    {c : ConjClasses G} {g : G} :
    g ∈ classSet c ↔ ConjClasses.mk g = c := by
  classical
  simp [classSet]

private theorem classSet_card
    {G : Type*} [Group G] [Finite G] (c : ConjClasses G) :
    (classSet c).card = Nat.card c.carrier := by
  classical
  let e : {g : G // g ∈ classSet c} ≃ c.carrier :=
    { toFun := fun x =>
        ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mpr
          (mem_classSet_iff.mp x.2)⟩
      invFun := fun x =>
        ⟨x, mem_classSet_iff.mpr
          (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr e

private noncomputable def classSum
    {G : Type*} [Group G] [Finite G]
    (R : Type*) [CommRing R] (c : ConjClasses G) : MonoidAlgebra R G :=
  ∑ g ∈ classSet c, MonoidAlgebra.single g 1

private theorem classSum_coeff
    {G : Type*} [Group G] [Finite G]
    [DecidableEq (ConjClasses G)]
    (R : Type*) [CommRing R] (c : ConjClasses G) (g : G) :
    (classSum R c).coeff g =
      if ConjClasses.mk g = c then 1 else 0 := by
  classical
  rw [classSum]
  simp only [MonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply']
  change ∑ x ∈ classSet c, (Finsupp.single x (1 : R)) g = _
  by_cases hgc : ConjClasses.mk g = c
  · rw [if_pos hgc]
    have hgmem : g ∈ classSet c := mem_classSet_iff.mpr hgc
    rw [Finset.sum_eq_single g]
    · simp
    · intro x _hx hxg
      simp [hxg]
    · intro hgnot
      exact (hgnot hgmem).elim
  · rw [if_neg hgc]
    apply Finset.sum_eq_zero
    intro x hx
    have hxg : x ≠ g := by
      intro hxg
      apply hgc
      simpa [hxg] using (mem_classSet_iff.mp hx)
    simp [hxg]

private theorem classSum_apply
    {G : Type*} [Group G] [Finite G]
    [DecidableEq (ConjClasses G)]
    (R : Type*) [CommRing R] (c : ConjClasses G) (g : G) :
    classSum R c g = if ConjClasses.mk g = c then 1 else 0 :=
  classSum_coeff R c g

private theorem classSum_comm
    {G : Type*} [Group G] [Finite G]
    (R : Type*) [CommRing R] (c : ConjClasses G)
    (a : MonoidAlgebra R G) :
    a * classSum R c = classSum R c * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      ext x
      have hconj :
          ConjClasses.mk (g⁻¹ * x) = ConjClasses.mk (x * g⁻¹) := by
        rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
        exact ⟨g, by group⟩
      simp only [MonoidAlgebra.single_mul_apply,
        MonoidAlgebra.mul_single_apply, classSum_apply]
      rw [hconj, mul_comm]

private theorem mapRingHom_classSum
    {G : Type*} [Group G] [Finite G]
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : ConjClasses G) :
    MonoidAlgebra.mapRingHom G f (classSum R c) = classSum S c := by
  classical
  simp [classSum]

private theorem mapRingHom_smul
    {G : Type*} [Group G]
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (a : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G f (r • a) =
      f r • MonoidAlgebra.mapRingHom G f a := by
  ext g
  simp [MonoidAlgebra.mapRingHom_apply]

private noncomputable def centralIntertwiner
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    Representation.IntertwiningMap ρ ρ where
  toLinearMap := ρ.asAlgebraHom z
  isIntertwining' g := by
    rw [← Representation.asAlgebraHom_single_one (ρ := ρ) g]
    change ρ.asAlgebraHom z *
        ρ.asAlgebraHom (MonoidAlgebra.single g (1 : ℂ)) =
      ρ.asAlgebraHom (MonoidAlgebra.single g (1 : ℂ)) *
        ρ.asAlgebraHom z
    rw [← map_mul, ← map_mul]
    exact congrArg ρ.asAlgebraHom
      (hz (MonoidAlgebra.single g (1 : ℂ))).symm

private theorem centralIntertwiner_eq_scalar
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    ∃ a : ℂ, ρ.asAlgebraHom z = a • (1 : Module.End ℂ V) := by
  classical
  have hfin :
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) = 1 :=
    (Representation.irreducible_iff_end_dimension_one (ρ := ρ)).1 inferInstance
  haveI : Nontrivial V := Representation.irreducible_nontrivial (ρ := ρ)
  have hone_ne_zero :
      (1 : Representation.IntertwiningMap ρ ρ) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvzero : v = 0 := by
      simpa using congrArg
        (fun f : Representation.IntertwiningMap ρ ρ => f v) h
    exact hv hvzero
  obtain ⟨a, ha⟩ :
      ∃ a : ℂ, a • (1 : Representation.IntertwiningMap ρ ρ) =
        centralIntertwiner ρ z hz :=
    (finrank_eq_one_iff_of_nonzero'
      (K := ℂ) (V := Representation.IntertwiningMap ρ ρ)
      (1 : Representation.IntertwiningMap ρ ρ) hone_ne_zero).mp hfin
      (centralIntertwiner ρ z hz)
  refine ⟨a, ?_⟩
  ext v
  simpa [centralIntertwiner] using
    (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) ha).symm

private theorem classSum_trace
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (c : ConjClasses G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
      ∑ g ∈ classSet c, ρ.character g := by
  classical
  simp [classSum, Representation.character, map_sum]

private theorem classSum_action_eq_centralCharacter
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) :
    ρ.asAlgebraHom (classSum ℂ c) =
      BlockPreliminaries.ordinaryCentralCharacterValue
          ρ.characterClassFunction c •
        (1 : Module.End ℂ V) := by
  classical
  letI : Nontrivial V := Representation.irreducible_nontrivial (ρ := ρ)
  obtain ⟨a, ha⟩ := centralIntertwiner_eq_scalar ρ (classSum ℂ c)
    (classSum_comm ℂ c)
  have htrace₁ :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
        ∑ g ∈ classSet c, ρ.character g := classSum_trace ρ c
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep c
  have hconst : ∀ g ∈ classSet c, ρ.character g = ρ.character x := by
    intro g hg
    change ρ.characterClassFunction (ConjClasses.mk g) =
      ρ.characterClassFunction (ConjClasses.mk x)
    rw [mem_classSet_iff.mp hg, hx]
  have htrace₁' :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
        (Nat.card c.carrier : ℂ) * ρ.character x := by
    rw [htrace₁]
    calc
      (∑ g ∈ classSet c, ρ.character g) =
          ∑ _g ∈ classSet c, ρ.character x := by
            apply Finset.sum_congr rfl
            intro g hg
            exact hconst g hg
      _ = (Nat.card c.carrier : ℂ) * ρ.character x := by
            rw [Finset.sum_const, classSet_card]
            simp [nsmul_eq_mul]
  have htrace₂ :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
        a * (Module.finrank ℂ V : ℂ) := by
    rw [ha, map_smul]
    simp
  have hdegree : ρ.character 1 = (Module.finrank ℂ V : ℂ) := by
    simp [Representation.character]
  have hdim_ne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    have hpos : 0 < Module.finrank ℂ V :=
      (Module.finrank_pos_iff (R := ℂ) (M := V)).2 inferInstance
    exact_mod_cast hpos.ne'
  rw [ha]
  congr 1
  rw [BlockPreliminaries.ordinaryCentralCharacterValue]
  have hχc : ρ.characterClassFunction c = ρ.character x := by
    rw [← hx]
    rfl
  have hχone :
      ρ.characterClassFunction (ConjClasses.mk (1 : G)) =
        ρ.character 1 := rfl
  rw [hχc, hχone, hdegree]
  have hscalar :
      a * (Module.finrank ℂ V : ℂ) =
        (Nat.card c.carrier : ℂ) * ρ.character x :=
    htrace₂.symm.trans htrace₁'
  field_simp [hdim_ne]
  simpa [mul_comm] using hscalar

private theorem center_eq_sum_classCoefficient_smul_classSum
    {R G : Type*} [CommRing R] [Group G] [Finite G]
    (z : Subring.center (MonoidAlgebra R G)) :
    (z : MonoidAlgebra R G) =
      ∑ c : ConjClasses G,
        CentralScalarCongruence.centralClassCoefficient z c • classSum R c := by
  classical
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  apply Finsupp.ext
  intro g
  change (z : MonoidAlgebra R G).coeff g =
    (∑ c : ConjClasses G,
      CentralScalarCongruence.centralClassCoefficient z c • classSum R c).coeff g
  simp only [MonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply']
  change (z : MonoidAlgebra R G) g = ∑ c : ConjClasses G,
    CentralScalarCongruence.centralClassCoefficient z c * classSum R c g
  simp only [classSum_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (ConjClasses.mk g)]
  · simpa using (CentralScalarCongruence.centralClassCoefficient_eq
      z (ConjClasses.mk g) g rfl).symm
  · intro c _hc hc
    rw [if_neg (Ne.symm hc)]
  · simp

private theorem localizedCentralScalar_action
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I) {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρ : d.chi i = ρ.characterClassFunction)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (localizationToComplex d)
          (z : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)) =
      localizationToComplex d
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  have hρirr : Representation.IsIrreducible ρ := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using (d.complete.1 i).2
  letI : Representation.IsIrreducible ρ := hρirr
  letI : Nontrivial (Fin n → ℂ) :=
    Representation.irreducible_nontrivial (ρ := ρ)
  rw [center_eq_sum_classCoefficient_smul_classSum z]
  calc
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (localizationToComplex d)
          (∑ c : ConjClasses G,
            CentralScalarCongruence.centralClassCoefficient z c •
              classSum (Localization.AtPrime d.primeIdeal) c)) =
        ∑ c : ConjClasses G,
          localizationToComplex d
              (CentralScalarCongruence.centralClassCoefficient z c) •
            ρ.asAlgebraHom (classSum ℂ c) := by
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro c _hc
          rw [mapRingHom_smul, mapRingHom_classSum, map_smul]
    _ = ∑ c : ConjClasses G,
          localizationToComplex d
              (CentralScalarCongruence.centralClassCoefficient z c) •
            (BlockPreliminaries.ordinaryCentralCharacterValue
                (d.chi i) c • (1 : Module.End ℂ (Fin n → ℂ))) := by
          apply Finset.sum_congr rfl
          intro c _hc
          rw [classSum_action_eq_centralCharacter ρ, ← hρ]
    _ = localizationToComplex d
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
          unfold CentralScalarCongruence.localizedCentralScalar
          rw [map_sum, Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro c _hc
          simp only [CentralScalarCongruence.localizedCentralScalar,
            map_mul, localizationToComplex_algebraMap, smul_smul]
          rfl

private theorem smul_one_injective
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V] :
    Function.Injective
      (fun a : ℂ => a • (1 : Module.End ℂ V)) := by
  intro a b hab
  apply FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ V)
  simpa [Algebra.algebraMap_eq_smul_one] using hab

private theorem localizedCentralScalar_one
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I) :
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
        d.primeIdeal (d.chi i) (d.complete.1 i)
        (1 : Subring.center
          (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)) = 1 := by
  rcases (d.complete.1 i).1 with ⟨n, ρ, hρ⟩
  have hρirr : Representation.IsIrreducible ρ := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using (d.complete.1 i).2
  letI : Representation.IsIrreducible ρ := hρirr
  letI : Nontrivial (Fin n → ℂ) :=
    Representation.irreducible_nontrivial (ρ := ρ)
  have haction := localizedCentralScalar_action d i ρ hρ
    (1 : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
  have hscalar :
      localizationToComplex d
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i)
            (1 : Subring.center
              (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))) = 1 := by
    apply smul_one_injective
      (V := Fin n → ℂ)
    simpa using haction.symm
  apply localizationToComplex_injective d
  simpa using hscalar

private theorem localizedCentralScalar_mul
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
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
    apply (Representation.irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using (d.complete.1 i).2
  letI : Representation.IsIrreducible ρ := hρirr
  letI : Nontrivial (Fin n → ℂ) :=
    Representation.irreducible_nontrivial (ρ := ρ)
  have hz := localizedCentralScalar_action d i ρ hρ z
  have hw := localizedCentralScalar_action d i ρ hρ w
  have hzw := localizedCentralScalar_action d i ρ hρ (z * w)
  have hscalar :
      localizationToComplex d
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) (z * w)) =
        localizationToComplex d
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) z) *
          localizationToComplex d
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) w) := by
    apply smul_one_injective
      (V := Fin n → ℂ)
    change
      localizationToComplex d
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) (z * w)) •
          (1 : Module.End ℂ (Fin n → ℂ)) =
        (localizationToComplex d
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) z) *
          localizationToComplex d
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) w)) •
          (1 : Module.End ℂ (Fin n → ℂ))
    calc
      _ = ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (localizationToComplex d) (z * w)) :=
        hzw.symm
      _ = ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (localizationToComplex d) z) *
          ρ.asAlgebraHom
            (MonoidAlgebra.mapRingHom G (localizationToComplex d) w) := by
        rw [map_mul, map_mul]
      _ = _ := by rw [hz, hw]; simp [Algebra.smul_def]
  apply localizationToComplex_injective d
  simpa using hscalar

/-- An irreducible character value, regarded as an element of the chosen
cyclotomic order. -/
private noncomputable def characterValueInCyclotomicOrder
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I) (g : G) : Representation.cyclotomicOrder d.eta := by
  refine ⟨d.chi i (ConjClasses.mk g), ?_⟩
  rcases (d.complete.1 i).1 with ⟨n, rho, hrho⟩
  rw [hrho]
  exact Representation.representation_character_mem_cyclotomicOrder
    d.eta_spec rho g

@[simp] private theorem localizationToComplex_characterValue
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I) (g : G) :
    localizationToComplex d
        (algebraMap (Representation.cyclotomicOrder d.eta)
          (Localization.AtPrime d.primeIdeal)
          (characterValueInCyclotomicOrder d i g)) =
      d.chi i (ConjClasses.mk g) := by
  exact localizationToComplex_algebraMap d _

private theorem mapRingHom_mem_center
    {R S G : Type*} [CommRing R] [CommRing S] [Group G]
    (f : R →+* S) (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    MonoidAlgebra.mapRingHom G f e ∈
      Set.center (MonoidAlgebra S G) := by
  apply (Semigroup.mem_center_iff).2
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      have hcomm := Semigroup.mem_center_iff.mp he
        (MonoidAlgebra.single g (1 : R))
      have hmap := congrArg (MonoidAlgebra.mapRingHom G f) hcomm
      have hcommOne :
          (MonoidAlgebra.single g (1 : S)) *
              MonoidAlgebra.mapRingHom G f e =
            MonoidAlgebra.mapRingHom G f e *
              MonoidAlgebra.single g (1 : S) := by
        simpa using hmap
      rw [show (MonoidAlgebra.single g r : MonoidAlgebra S G) =
          r • MonoidAlgebra.single g 1 by simp]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      exact congrArg (fun x : MonoidAlgebra S G => r • x) hcommOne

private theorem pow_mem_center
    {A : Type*} [Monoid A] (e : A) (he : e ∈ Set.center A) (N : ℕ) :
    e ^ N ∈ Set.center A := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ]
      exact Set.mul_mem_center ih he

private theorem localizedCentralScalar_sub
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
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
    (z.1 (CentralScalarCongruence.classRepresentative c) -
        w.1 (CentralScalarCongruence.classRepresentative c)) * _ =
      z.1 (CentralScalarCongruence.classRepresentative c) * _ -
        w.1 (CentralScalarCongruence.classRepresentative c) * _
  exact sub_mul _ _ _

private theorem localizedCentralScalar_pow_of_pos
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
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

private theorem card_mul_coeff_eq_sum_localizedCentralScalar
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (g : G) :
    (Nat.card G : Localization.AtPrime d.primeIdeal) * z.1 g =
      ∑ i : d.I,
        CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z *
          algebraMap (Representation.cyclotomicOrder d.eta)
            (Localization.AtPrime d.primeIdeal)
            (characterValueInCyclotomicOrder d i 1) *
          algebraMap (Representation.cyclotomicOrder d.eta)
            (Localization.AtPrime d.primeIdeal)
            (characterValueInCyclotomicOrder d i g⁻¹) := by
  classical
  apply localizationToComplex_injective d
  simp only [map_mul, map_sum, map_natCast,
    localizationToComplex_characterValue]
  change (Nat.card G : ℂ) *
      (MonoidAlgebra.mapRingHom G (localizationToComplex d) z.1) g =
    ∑ i : d.I,
      localizationToComplex d
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z) *
        d.chi i (ConjClasses.mk (1 : G)) *
        d.chi i (ConjClasses.mk g⁻¹)
  let zC := MonoidAlgebra.mapRingHom G (localizationToComplex d) z.1
  have hzC : zC ∈ Set.center (MonoidAlgebra ℂ G) :=
    mapRingHom_mem_center (localizationToComplex d) z.1 z.property
  have hcoeff :=
    BlockOrthogonality.coeff_eq_inv_card_mul_sum_scalar_degree_character
      d.chi d.complete zC (Semigroup.mem_center_iff.mp hzC)
      (fun i => localizationToComplex d
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z))
      (by
        intro i n rho hrho
        exact localizedCentralScalar_action d i rho hrho z) g
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  change zC g = _ at hcoeff
  change (Nat.card G : ℂ) * zC g = _
  rw [hcoeff]
  field_simp [hcard]

private theorem localizedCentralScalar_localizedPrincipalBlockElement
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I) :
    let e : Subring.center
        (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) :=
      ⟨BlockOrthogonality.localizedPrincipalBlockElement d,
        BlockOrthogonality.localizedPrincipalBlockElement_mem_center d⟩
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
        d.primeIdeal (d.chi i) (d.complete.1 i) e =
      if i ∈ d.block then 1 else 0 := by
  dsimp only
  let e : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) :=
    ⟨BlockOrthogonality.localizedPrincipalBlockElement d,
      BlockOrthogonality.localizedPrincipalBlockElement_mem_center d⟩
  rcases (d.complete.1 i).1 with ⟨n, rho, hrho⟩
  have hrhoIrr : Representation.IsIrreducible rho := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := rho)).2
    simpa [hrho] using (d.complete.1 i).2
  letI : Representation.IsIrreducible rho := hrhoIrr
  letI : Nontrivial (Fin n → ℂ) :=
    Representation.irreducible_nontrivial (ρ := rho)
  apply localizationToComplex_injective d
  apply smul_one_injective (V := Fin n → ℂ)
  have hscalar := localizedCentralScalar_action d i rho hrho e
  have hindicator :=
    BlockOrthogonality.principalBlockElement_action d i rho hrho
  have hmap :=
    BlockOrthogonality.mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
      d (localizationToComplex d) (localizationToComplex_algebraMap d)
  calc
    localizationToComplex d
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) e) •
        (1 : Module.End ℂ (Fin n → ℂ)) =
      rho.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (localizationToComplex d)
          (BlockOrthogonality.localizedPrincipalBlockElement d)) := by
        simpa [e] using hscalar.symm
    _ = rho.asAlgebraHom (BlockOrthogonality.principalBlockElement d) := by
      rw [hmap]
    _ = (if i ∈ d.block then (1 : ℂ) else 0) •
        (1 : Module.End ℂ (Fin n → ℂ)) := hindicator
    _ = localizationToComplex d
          (if i ∈ d.block then (1 : Localization.AtPrime d.primeIdeal)
            else 0) • (1 : Module.End ℂ (Fin n → ℂ)) := by
        split <;> simp

private theorem localizationToResidue_localizedCentralScalar_eq_zero_of_map_eq_zero
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (hz : MonoidAlgebra.mapRingHom G
        (BrauerBlockReduction.localizationToResidue d) z.1 = 0) :
    BrauerBlockReduction.localizationToResidue d
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z) = 0 := by
  classical
  rw [CentralScalarCongruence.localizedCentralScalar, map_sum]
  apply Finset.sum_eq_zero
  intro c _hc
  rw [map_mul]
  have hc := congrArg
    (fun a : MonoidAlgebra
        (BrauerBlockReduction.principalResidueField d) G =>
      a (CentralScalarCongruence.classRepresentative c)) hz
  change BrauerBlockReduction.localizationToResidue d
      (z.1 (CentralScalarCongruence.classRepresentative c)) = 0 at hc
  have hcoeff : BrauerBlockReduction.localizationToResidue d
      (CentralScalarCongruence.centralClassCoefficient z c) = 0 := by
    exact hc
  rw [hcoeff, zero_mul]

private theorem localizationToResidue_eq_zero_iff_not_isUnit_aux
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (a : Localization.AtPrime d.primeIdeal) :
    BrauerBlockReduction.localizationToResidue d a = 0 ↔ ¬ IsUnit a := by
  letI : d.primeIdeal.IsMaximal := d.primeIdeal_maximal
  letI : Field (BrauerBlockReduction.principalResidueField d) :=
    Ideal.Quotient.field d.primeIdeal
  have hsurjective : Function.Surjective
      (BrauerBlockReduction.localizationToResidue d) := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap (Representation.cyclotomicOrder d.eta)
      (Localization.AtPrime d.primeIdeal) b, ?_⟩
    exact BrauerBlockReduction.localizationToResidue_algebraMap d b
  have hkerMaximal :
      (RingHom.ker (BrauerBlockReduction.localizationToResidue d)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective
      (BrauerBlockReduction.localizationToResidue d) hsurjective
  have hker : RingHom.ker (BrauerBlockReduction.localizationToResidue d) =
      IsLocalRing.maximalIdeal (Localization.AtPrime d.primeIdeal) :=
    IsLocalRing.eq_maximalIdeal hkerMaximal
  rw [← RingHom.mem_ker, hker, IsLocalRing.mem_maximalIdeal]
  rfl

/-- If every ordinary scalar of a central localized element is a nonunit,
then one positive power of that element vanishes after reduction.  The
uniform DVR exponent absorbs the single denominator `|G|` in the central
coefficient formula. -/
theorem exists_pow_reduce_eq_zero_of_all_localizedCentralScalar_nonunit
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (hscalar : ∀ i : d.I,
      ¬ IsUnit
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z)) :
    ∃ N : ℕ, 0 < N ∧
      MonoidAlgebra.mapRingHom G
          (BrauerBlockReduction.localizationToResidue d)
          ((z ^ N : Subring.center
            (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)).1) = 0 := by
  classical
  let R := Localization.AtPrime d.primeIdeal
  letI : IsDiscreteValuationRing R :=
    CyclotomicDVR.cyclotomicOrderAtPrime_isDiscreteValuationRing d
  have hcard : (Nat.card G : R) ≠ 0 := by
    intro hzero
    have hmap := congrArg (localizationToComplex d) hzero
    have hcardC : (Nat.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := G)).ne'
    exact hcardC (by simpa [R] using hmap)
  obtain ⟨N, hN, huniform⟩ :=
    exists_uniform_pow_eq_mul_nonunit (R := R)
      (Nat.card G : R) hcard
  have hquot : ∀ i : d.I, ∃ q : R,
      CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z ^ N =
          (Nat.card G : R) * q ∧
        ¬ IsUnit q := by
    intro i
    exact huniform _ (hscalar i)
  choose q hq hq_nonunit using hquot
  refine ⟨N, hN, ?_⟩
  ext g
  rw [MonoidAlgebra.mapRingHom_apply]
  apply (localizationToResidue_eq_zero_iff_not_isUnit_aux d _).2
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  have hreconstruct :=
    card_mul_coeff_eq_sum_localizedCentralScalar d (z ^ N) g
  simp_rw [localizedCentralScalar_pow_of_pos d _ z N hN] at hreconstruct
  have hcoeff :
      ((z ^ N : Subring.center
          (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)).1 g) =
        ∑ i : d.I,
          q i *
            algebraMap (Representation.cyclotomicOrder d.eta) R
              (characterValueInCyclotomicOrder d i 1) *
            algebraMap (Representation.cyclotomicOrder d.eta) R
              (characterValueInCyclotomicOrder d i g⁻¹) := by
    apply mul_left_cancel₀ hcard
    calc
      (Nat.card G : R) *
          ((z ^ N : Subring.center
            (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)).1 g) =
        ∑ i : d.I,
          CentralScalarCongruence.localizedCentralScalar d.eta_spec
                d.primeIdeal (d.chi i) (d.complete.1 i) z ^ N *
              algebraMap (Representation.cyclotomicOrder d.eta) R
                (characterValueInCyclotomicOrder d i 1) *
            algebraMap (Representation.cyclotomicOrder d.eta) R
              (characterValueInCyclotomicOrder d i g⁻¹) :=
        hreconstruct
      _ = ∑ i : d.I,
          ((Nat.card G : R) * q i) *
              algebraMap (Representation.cyclotomicOrder d.eta) R
                (characterValueInCyclotomicOrder d i 1) *
            algebraMap (Representation.cyclotomicOrder d.eta) R
              (characterValueInCyclotomicOrder d i g⁻¹) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hq i]
      _ = (Nat.card G : R) *
          ∑ i : d.I,
            q i *
                algebraMap (Representation.cyclotomicOrder d.eta) R
                  (characterValueInCyclotomicOrder d i 1) *
              algebraMap (Representation.cyclotomicOrder d.eta) R
                (characterValueInCyclotomicOrder d i g⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  rw [hcoeff]
  apply Ideal.sum_mem
  intro i _hi
  apply (IsLocalRing.maximalIdeal R).mul_mem_right
  apply (IsLocalRing.maximalIdeal R).mul_mem_right
  rw [IsLocalRing.mem_maximalIdeal]
  exact hq_nonunit i

/-- Reduction from the localized cyclotomic order kills exactly its
nonunits, equivalently its maximal ideal. -/
theorem localizationToResidue_eq_zero_iff_not_isUnit
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (a : Localization.AtPrime d.primeIdeal) :
    BrauerBlockReduction.localizationToResidue d a = 0 ↔ ¬ IsUnit a :=
  localizationToResidue_eq_zero_iff_not_isUnit_aux d a

private theorem localizationToResidue_surjective
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    Function.Surjective (BrauerBlockReduction.localizationToResidue d) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨algebraMap (Representation.cyclotomicOrder d.eta)
    (Localization.AtPrime d.primeIdeal) b, ?_⟩
  exact BrauerBlockReduction.localizationToResidue_algebraMap d b

private theorem principal_localizedCentralScalar_isUnit_of_nonzero_factor
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (f : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G)
    (hfcenter : f ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G))
    (hfidem : IsIdempotentElem f)
    (hfactor : f * BrauerBlockReduction.reducedPrincipalBlockElement d = f)
    (hfne : f ≠ 0)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (hzreduce : MonoidAlgebra.mapRingHom G
        (BrauerBlockReduction.localizationToResidue d) z.1 = f) :
    IsUnit
      (CentralScalarCongruence.localizedCentralScalar d.eta_spec
        d.primeIdeal (d.chi d.principal) (d.complete.1 d.principal) z) := by
  let e : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) :=
    ⟨BlockOrthogonality.localizedPrincipalBlockElement d,
      BlockOrthogonality.localizedPrincipalBlockElement_mem_center d⟩
  let error := z * e - z
  have herrorReduce : MonoidAlgebra.mapRingHom G
      (BrauerBlockReduction.localizationToResidue d) error.1 = 0 := by
    change MonoidAlgebra.mapRingHom G
        (BrauerBlockReduction.localizationToResidue d)
        (z.1 * e.1 - z.1) = 0
    rw [map_sub, map_mul, hzreduce]
    change f * BrauerBlockReduction.reducedPrincipalBlockElement d - f = 0
    rw [hfactor, sub_self]
  by_contra hprincipal
  have hall : ∀ i : d.I,
      ¬ IsUnit
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z) := by
    intro i
    by_cases hi : i ∈ d.block
    · have hsame := (d.mem_block_iff i).mp hi
      have hdiff :=
        CentralScalarCongruence.localizedCentralScalar_sub_mem_maximalIdeal
          d.eta_spec d.primeIdeal (d.chi i) (d.chi d.principal)
          (d.complete.1 i) (d.complete.1 d.principal) hsame z
      have hp :
          CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi d.principal)
                (d.complete.1 d.principal) z ∈
            IsLocalRing.maximalIdeal
              (Localization.AtPrime d.primeIdeal) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact hprincipal
      have hiMem :
          CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) z ∈
            IsLocalRing.maximalIdeal
              (Localization.AtPrime d.primeIdeal) := by
        have hadd := (IsLocalRing.maximalIdeal
          (Localization.AtPrime d.primeIdeal)).add_mem hdiff hp
        convert hadd using 1 <;> ring
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hiMem
      exact hiMem
    · have hzero :=
        localizationToResidue_localizedCentralScalar_eq_zero_of_map_eq_zero
          d i error herrorReduce
      have heScalar :=
        localizedCentralScalar_localizedPrincipalBlockElement d i
      have hzero' : BrauerBlockReduction.localizationToResidue d
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) z) = 0 := by
        rw [localizedCentralScalar_sub, localizedCentralScalar_mul,
          heScalar, if_neg hi] at hzero
        simpa using hzero
      exact (localizationToResidue_eq_zero_iff_not_isUnit d _).mp hzero'
  obtain ⟨N, hN, hpowzero⟩ :=
    exists_pow_reduce_eq_zero_of_all_localizedCentralScalar_nonunit
      d z hall
  have hpowzero' : f ^ N = 0 := by
    change MonoidAlgebra.mapRingHom G
        (BrauerBlockReduction.localizationToResidue d) (z.1 ^ N) = 0 at hpowzero
    rwa [map_pow, hzreduce] at hpowzero
  apply hfne
  rw [← hfidem.pow_eq hN.ne']
  exact hpowzero'

/-- A nonzero central idempotent is centrally primitive when it has no
proper nonzero central-idempotent factor. -/
def IsCentrallyPrimitive
    {A : Type*} [Ring A] (e : A) : Prop :=
  e ∈ Set.center A ∧ IsIdempotentElem e ∧ e ≠ 0 ∧
    ∀ f : A, f ∈ Set.center A → IsIdempotentElem f →
      f * e = f → f ≠ 0 → f = e

/-- The reduced principal congruence selector is centrally primitive.  A
central idempotent factor is lifted coefficientwise to the localization.  Its
ordinary central scalars are then reconstructed from the character family;
the uniform DVR power lemma turns vanishing scalar residues into nilpotence,
which is impossible for a nonzero idempotent. -/
theorem reducedPrincipalBlockElement_isCentrallyPrimitive
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    IsCentrallyPrimitive
      (BrauerBlockReduction.reducedPrincipalBlockElement d) := by
  classical
  letI : d.primeIdeal.IsMaximal := d.primeIdeal_maximal
  letI : Field (BrauerBlockReduction.principalResidueField d) :=
    Ideal.Quotient.field d.primeIdeal
  let R := Localization.AtPrime d.primeIdeal
  let q := BrauerBlockReduction.localizationToResidue d
  let eR : Subring.center (MonoidAlgebra R G) :=
    ⟨BlockOrthogonality.localizedPrincipalBlockElement d,
      BlockOrthogonality.localizedPrincipalBlockElement_mem_center d⟩
  let eK := BrauerBlockReduction.reducedPrincipalBlockElement d
  have hemap : MonoidAlgebra.mapRingHom G q eR.1 = eK := rfl
  have hecenter : eK ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) :=
    BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d
  have heidem : IsIdempotentElem eK :=
    BrauerBlockReduction.reducedPrincipalBlockElement_isIdempotent d
  have hene : eK ≠ 0 := by
    intro hzero
    change BrauerBlockReduction.reducedPrincipalBlockElement d = 0 at hzero
    have haug :=
      AugmentationScratch.reducedPrincipalBlockElement_augmentation_eq_one d
    rw [hzero] at haug
    simpa using haug
  refine ⟨hecenter, heidem, hene, ?_⟩
  intro f hf hfid hfactor hfne
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap (Representation.cyclotomicOrder d.eta) R a, ?_⟩
    exact BrauerBlockReduction.localizationToResidue_algebraMap d a
  obtain ⟨x, hxcenter, hxmap⟩ :=
    CentralLift.exists_monoidAlgebra_lift_mem_center q hqsurj f hf
  let xz : Subring.center (MonoidAlgebra R G) := ⟨x, hxcenter⟩
  have hfactorzero :
      MonoidAlgebra.mapRingHom G q ((xz * eR - xz).1) = 0 := by
    change MonoidAlgebra.mapRingHom G q (x *
        BlockOrthogonality.localizedPrincipalBlockElement d - x) = 0
    rw [map_sub, map_mul, hxmap]
    change f * eK - f = 0
    rw [hfactor, sub_self]
  have hidemzero :
      MonoidAlgebra.mapRingHom G q ((xz * xz - xz).1) = 0 := by
    change MonoidAlgebra.mapRingHom G q (x * x - x) = 0
    rw [map_sub, map_mul, hxmap, hfid, sub_self]
  let scalar : d.I → R := fun i =>
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
      d.primeIdeal (d.chi i) (d.complete.1 i) xz
  have houtside : ∀ i : d.I, i ∉ d.block → q (scalar i) = 0 := by
    intro i hi
    have hy :=
      localizationToResidue_localizedCentralScalar_eq_zero_of_map_eq_zero
        d i (xz * eR - xz) hfactorzero
    rw [localizedCentralScalar_sub, localizedCentralScalar_mul,
      localizedCentralScalar_localizedPrincipalBlockElement] at hy
    simpa [scalar, hi] using hy
  have hidemScalar : ∀ i : d.I,
      q (scalar i) * q (scalar i) = q (scalar i) := by
    intro i
    have hy :=
      localizationToResidue_localizedCentralScalar_eq_zero_of_map_eq_zero
        d i (xz * xz - xz) hidemzero
    rw [localizedCentralScalar_sub, localizedCentralScalar_mul] at hy
    simpa [scalar, map_sub, map_mul, sub_eq_zero] using hy
  have hexScalar : ∃ i : d.I, q (scalar i) ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    have hnonunit : ∀ i : d.I, ¬ IsUnit (scalar i) := by
      intro i
      exact (localizationToResidue_eq_zero_iff_not_isUnit d _).mp
        (hnone i)
    obtain ⟨N, hN, hpow⟩ :=
      exists_pow_reduce_eq_zero_of_all_localizedCentralScalar_nonunit
        d xz hnonunit
    have hfzero : f = 0 := by
      calc
        f = f ^ N := (hfid.pow_eq (Nat.ne_of_gt hN)).symm
        _ = (MonoidAlgebra.mapRingHom G q x) ^ N := by rw [hxmap]
        _ = MonoidAlgebra.mapRingHom G q (x ^ N) := by rw [map_pow]
        _ = MonoidAlgebra.mapRingHom G q (xz.1 ^ N) := rfl
        _ = 0 := by simpa using hpow
    exact hfne hfzero
  obtain ⟨i₀, hi₀ne⟩ := hexScalar
  have hi₀block : i₀ ∈ d.block := by
    by_contra hi
    exact hi₀ne (houtside i₀ hi)
  have hqScalar₀ : q (scalar i₀) = 1 := by
    have hpoly := hidemScalar i₀
    have hprod : q (scalar i₀) * (q (scalar i₀) - 1) = 0 := by
      rw [mul_sub, mul_one, hpoly, sub_self]
    rcases mul_eq_zero.mp hprod with hzero | hone
    · exact (hi₀ne hzero).elim
    · exact sub_eq_zero.mp hone
  have hscalar_eq (i : d.I) (hi : i ∈ d.block) :
      q (scalar i) = q (scalar i₀) := by
    have hsame : BlockPreliminaries.SameTwoBlock d.eta_spec d.primeIdeal
        (d.chi i) (d.chi i₀) (d.complete.1 i) (d.complete.1 i₀) := by
      exact BlockPreliminaries.sameTwoBlock_trans d.eta_spec d.primeIdeal
        ((d.mem_block_iff i).mp hi)
        (BlockPreliminaries.sameTwoBlock_symm d.eta_spec d.primeIdeal
          ((d.mem_block_iff i₀).mp hi₀block))
    have hdiff :=
      CentralScalarCongruence.localizedCentralScalar_sub_mem_maximalIdeal
        d.eta_spec d.primeIdeal (d.chi i) (d.chi i₀)
        (d.complete.1 i) (d.complete.1 i₀) hsame xz
    have hnonunit : ¬ IsUnit (scalar i - scalar i₀) := by
      apply mem_nonunits_iff.mp
      exact (IsLocalRing.mem_maximalIdeal _).mp hdiff
    have hzero :=
      (localizationToResidue_eq_zero_iff_not_isUnit d _).2 hnonunit
    have hzero' : q (scalar i) - q (scalar i₀) = 0 := by
      simpa [scalar, map_sub] using hzero
    exact sub_eq_zero.mp hzero'
  have hinside : ∀ i : d.I, i ∈ d.block → q (scalar i) = 1 := by
    intro i hi
    rw [hscalar_eq i hi, hqScalar₀]
  let dz : Subring.center (MonoidAlgebra R G) := eR - xz
  have hdzzero : MonoidAlgebra.mapRingHom G q dz.1 = eK - f := by
    change MonoidAlgebra.mapRingHom G q (eR.1 - x) = _
    rw [map_sub, hemap, hxmap]
  have hdzNonunit : ∀ i : d.I,
      ¬ IsUnit
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) dz) := by
    intro i
    apply (localizationToResidue_eq_zero_iff_not_isUnit d _).mp
    rw [localizedCentralScalar_sub,
      localizedCentralScalar_localizedPrincipalBlockElement]
    change q ((if i ∈ d.block then (1 : R) else 0) - scalar i) = 0
    rw [map_sub]
    by_cases hi : i ∈ d.block
    · rw [if_pos hi, map_one, hinside i hi, sub_self]
    · rw [if_neg hi, map_zero, houtside i hi, sub_zero]
  obtain ⟨N, hN, hpow⟩ :=
    exists_pow_reduce_eq_zero_of_all_localizedCentralScalar_nonunit
      d dz hdzNonunit
  have hefactor : eK * f = f := by
    calc
      eK * f = f * eK := (Semigroup.mem_center_iff.mp hecenter f).symm
      _ = f := hfactor
  have hsubidem : IsIdempotentElem (eK - f) :=
    IsIdempotentElem.sub hfid heidem hfactor hefactor
  have hsubpow : (eK - f) ^ N = eK - f :=
    hsubidem.pow_eq (Nat.ne_of_gt hN)
  have hsubzero : eK - f = 0 := by
    have hpow' : (eK - f) ^ N = 0 := by
      calc
        (eK - f) ^ N =
            MonoidAlgebra.mapRingHom G q (dz.1 ^ N) := by
              rw [map_pow, hdzzero]
        _ = 0 := by simpa using hpow
    exact hsubpow.symm.trans hpow'
  exact (sub_eq_zero.mp hsubzero).symm

/-! ## Primitivity after passing to the compatible ambient residue field

The residue-field inclusion attached to a compatible subgroup can be proper,
so central primitivity cannot simply be transported along it.  Instead we
repeat the scalar argument over the ambient localization.  Ordinary central
character values for the subgroup first lie in the compatible local
localization and are then mapped into the ambient DVR. -/

private theorem localizationToComplex_cyclotomicOrderInclusion
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    {xi : ℂ} (hxi : xi ∈ Representation.cyclotomicOrder d.eta)
    (a : Representation.cyclotomicOrder xi) :
    localizationToComplex d
        (algebraMap (Representation.cyclotomicOrder d.eta)
          (Localization.AtPrime d.primeIdeal)
          (CompatibleLocalBlock.cyclotomicOrderInclusion hxi a)) =
      (a : ℂ) := by
  calc
    _ = ((CompatibleLocalBlock.cyclotomicOrderInclusion hxi a :
          Representation.cyclotomicOrder d.eta) : ℂ) :=
      localizationToComplex_algebraMap d _
    _ = (a : ℂ) := Subring.coe_inclusion _ a

private noncomputable def localCentralCharacterValueInAmbientLocalization
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I)
    (c : ConjClasses H) : Localization.AtPrime d.primeIdeal :=
  algebraMap (Representation.cyclotomicOrder d.eta)
    (Localization.AtPrime d.primeIdeal)
    (CompatibleLocalBlock.cyclotomicOrderInclusion
      (CompatibleLocalBlock.subgroupRoot_mem d H)
      (BlockPreliminaries.centralCharacterInCyclotomicOrder
        (CompatibleBrauerBlock.localData d H).eta_spec
        ((CompatibleBrauerBlock.localData d H).chi i)
        ((CompatibleBrauerBlock.localData d H).complete.1 i) c))

private theorem localizationToComplex_localCentralCharacterValueInAmbientLocalization
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I)
    (c : ConjClasses H) :
    localizationToComplex d
        (localCentralCharacterValueInAmbientLocalization d H i c) =
      BlockPreliminaries.ordinaryCentralCharacterValue
        ((CompatibleBrauerBlock.localData d H).chi i) c := by
  exact localizationToComplex_cyclotomicOrderInclusion d
    (CompatibleLocalBlock.subgroupRoot_mem d H) _

/-- The ordinary central scalar of a central subgroup-algebra element with
coefficients in the ambient localization. -/
private noncomputable def ambientLocalizedCentralScalar
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H)) :
    Localization.AtPrime d.primeIdeal :=
  ∑ c : ConjClasses H,
    CentralScalarCongruence.centralClassCoefficient z c *
      localCentralCharacterValueInAmbientLocalization d H i c

private theorem ambientLocalizedCentralScalar_action
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I)
    {n : ℕ} (rho : Representation ℂ H (Fin n → ℂ))
    (hrho : (CompatibleBrauerBlock.localData d H).chi i =
      rho.characterClassFunction)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H)) :
    rho.asAlgebraHom
        (MonoidAlgebra.mapRingHom H (localizationToComplex d) z.1) =
      localizationToComplex d (ambientLocalizedCentralScalar d H i z) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  letI : Fintype (ConjClasses H) := Fintype.ofFinite (ConjClasses H)
  have hrhoIrr : Representation.IsIrreducible rho := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := rho)).2
    simpa [hrho] using
      ((CompatibleBrauerBlock.localData d H).complete.1 i).2
  letI : Representation.IsIrreducible rho := hrhoIrr
  letI : Nontrivial (Fin n → ℂ) :=
    Representation.irreducible_nontrivial (ρ := rho)
  rw [center_eq_sum_classCoefficient_smul_classSum z]
  calc
    rho.asAlgebraHom
        (MonoidAlgebra.mapRingHom H (localizationToComplex d)
          (∑ c : ConjClasses H,
            CentralScalarCongruence.centralClassCoefficient z c •
              classSum (Localization.AtPrime d.primeIdeal) c)) =
        ∑ c : ConjClasses H,
          localizationToComplex d
              (CentralScalarCongruence.centralClassCoefficient z c) •
            rho.asAlgebraHom (classSum ℂ c) := by
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro c _hc
          rw [mapRingHom_smul, mapRingHom_classSum, map_smul]
    _ = ∑ c : ConjClasses H,
          localizationToComplex d
              (CentralScalarCongruence.centralClassCoefficient z c) •
            (BlockPreliminaries.ordinaryCentralCharacterValue
                ((CompatibleBrauerBlock.localData d H).chi i) c •
              (1 : Module.End ℂ (Fin n → ℂ))) := by
          apply Finset.sum_congr rfl
          intro c _hc
          rw [classSum_action_eq_centralCharacter rho, ← hrho]
    _ = localizationToComplex d (ambientLocalizedCentralScalar d H i z) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
          rw [ambientLocalizedCentralScalar, map_sum, Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro c _hc
          simp only [map_mul, smul_smul,
            localizationToComplex_localCentralCharacterValueInAmbientLocalization]

private theorem ambientLocalizedCentralScalar_mul
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I)
    (z w : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H)) :
    ambientLocalizedCentralScalar d H i (z * w) =
      ambientLocalizedCentralScalar d H i z *
        ambientLocalizedCentralScalar d H i w := by
  rcases ((CompatibleBrauerBlock.localData d H).complete.1 i).1 with
    ⟨n, rho, hrho⟩
  have hrhoIrr : Representation.IsIrreducible rho := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := rho)).2
    simpa [hrho] using
      ((CompatibleBrauerBlock.localData d H).complete.1 i).2
  letI : Representation.IsIrreducible rho := hrhoIrr
  letI : Nontrivial (Fin n → ℂ) :=
    Representation.irreducible_nontrivial (ρ := rho)
  have hz := ambientLocalizedCentralScalar_action d H i rho hrho z
  have hw := ambientLocalizedCentralScalar_action d H i rho hrho w
  have hzw := ambientLocalizedCentralScalar_action d H i rho hrho (z * w)
  apply localizationToComplex_injective d
  apply smul_one_injective (V := Fin n → ℂ)
  calc
    localizationToComplex d (ambientLocalizedCentralScalar d H i (z * w)) •
        (1 : Module.End ℂ (Fin n → ℂ)) =
      rho.asAlgebraHom
        (MonoidAlgebra.mapRingHom H (localizationToComplex d) (z * w)) :=
      hzw.symm
    _ = rho.asAlgebraHom
          (MonoidAlgebra.mapRingHom H (localizationToComplex d) z) *
        rho.asAlgebraHom
          (MonoidAlgebra.mapRingHom H (localizationToComplex d) w) := by
      rw [map_mul, map_mul]
    _ = localizationToComplex d
          (ambientLocalizedCentralScalar d H i z *
            ambientLocalizedCentralScalar d H i w) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
      rw [hz, hw, map_mul]
      simp [Algebra.smul_def]

private theorem ambientLocalizedCentralScalar_sub
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I)
    (z w : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H)) :
    ambientLocalizedCentralScalar d H i (z - w) =
      ambientLocalizedCentralScalar d H i z -
        ambientLocalizedCentralScalar d H i w := by
  classical
  rw [ambientLocalizedCentralScalar, ambientLocalizedCentralScalar,
    ambientLocalizedCentralScalar, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  change
    (z.1 (CentralScalarCongruence.classRepresentative c) -
        w.1 (CentralScalarCongruence.classRepresentative c)) * _ =
      z.1 (CentralScalarCongruence.classRepresentative c) * _ -
        w.1 (CentralScalarCongruence.classRepresentative c) * _
  exact sub_mul _ _ _

private theorem ambientLocalizedCentralScalar_pow_of_pos
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H))
    (N : ℕ) (hN : 0 < N) :
    ambientLocalizedCentralScalar d H i (z ^ N) =
      ambientLocalizedCentralScalar d H i z ^ N := by
  induction N using Nat.case_strong_induction_on with
  | hz => omega
  | hi N ih =>
      by_cases hNzero : N = 0
      · subst N
        simp
      · rw [pow_succ, pow_succ, ambientLocalizedCentralScalar_mul]
        rw [ih N (by omega) (Nat.pos_of_ne_zero hNzero)]

private def CompatibleLocalCentralCharactersCongruent
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i j : (CompatibleBrauerBlock.localData d H).I) : Prop :=
  ∀ c : ConjClasses H,
    BlockPreliminaries.centralCharacterInCyclotomicOrder
          (CompatibleBrauerBlock.localData d H).eta_spec
          ((CompatibleBrauerBlock.localData d H).chi i)
          ((CompatibleBrauerBlock.localData d H).complete.1 i) c -
        BlockPreliminaries.centralCharacterInCyclotomicOrder
          (CompatibleBrauerBlock.localData d H).eta_spec
          ((CompatibleBrauerBlock.localData d H).chi j)
          ((CompatibleBrauerBlock.localData d H).complete.1 j) c ∈
      (CompatibleBrauerBlock.localData d H).primeIdeal

private theorem ambientLocalizedCentralScalar_sub_mem_maximalIdeal
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i j : (CompatibleBrauerBlock.localData d H).I)
    (hchar : CompatibleLocalCentralCharactersCongruent d H i j)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H)) :
    ambientLocalizedCentralScalar d H i z -
        ambientLocalizedCentralScalar d H j z ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime d.primeIdeal) := by
  classical
  unfold CompatibleLocalCentralCharactersCongruent at hchar
  rw [ambientLocalizedCentralScalar, ambientLocalizedCentralScalar,
    ← Finset.sum_sub_distrib]
  apply Ideal.sum_mem
  intro c _hc
  rw [← mul_sub]
  apply Ideal.mul_mem_left
  unfold localCentralCharacterValueInAmbientLocalization
  rw [← map_sub, ← map_sub]
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime d.primeIdeal) d.primeIdeal _).2
  have hc := hchar c
  rw [CompatibleLocalBlock.compatibleSubgroupPrincipalCongruenceBlockData_primeIdeal]
    at hc
  exact Ideal.mem_comap.mp hc

private theorem ambientLocalizedCentralScalar_localPrincipalBlockElement
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I) :
    let e : Subring.center
        (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H) :=
      ⟨CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization
          d H,
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_mem_center
          d H⟩
    ambientLocalizedCentralScalar d H i e =
      if i ∈ (CompatibleBrauerBlock.localData d H).block then 1 else 0 := by
  dsimp only
  let l := CompatibleBrauerBlock.localData d H
  let e : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H) :=
    ⟨CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d H,
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_mem_center
        d H⟩
  rcases (l.complete.1 i).1 with ⟨n, rho, hrho⟩
  have hrhoIrr : Representation.IsIrreducible rho := by
    apply (Representation.irreducible_iff_character_norm_one (ρ := rho)).2
    simpa [l, hrho] using (l.complete.1 i).2
  letI : Representation.IsIrreducible rho := hrhoIrr
  letI : Nontrivial (Fin n → ℂ) :=
    Representation.irreducible_nontrivial (ρ := rho)
  have hmap :
      MonoidAlgebra.mapRingHom H (localizationToComplex d) e.1 =
        BlockOrthogonality.principalBlockElement l := by
    have hbase :=
      BlockOrthogonality.mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
        l ((localizationToComplex d).comp
          (CompatibleLocalBlock.compatibleSubgroupLocalizationInclusion d H))
        (by
          intro a
          rw [RingHom.coe_comp, Function.comp_apply,
            CompatibleLocalBlock.compatibleSubgroupLocalizationInclusion_algebraMap]
          exact localizationToComplex_cyclotomicOrderInclusion d
            (CompatibleLocalBlock.subgroupRoot_mem d H) a)
    have hcomp := congrArg
      (fun F => F (BlockOrthogonality.localizedPrincipalBlockElement l))
      (MonoidAlgebra.mapRingHom_comp (M := H) (localizationToComplex d)
        (CompatibleLocalBlock.compatibleSubgroupLocalizationInclusion d H))
    have hcomp' :
        MonoidAlgebra.mapRingHom H (localizationToComplex d)
            (MonoidAlgebra.mapRingHom H
              (CompatibleLocalBlock.compatibleSubgroupLocalizationInclusion d H)
              (BlockOrthogonality.localizedPrincipalBlockElement l)) =
          MonoidAlgebra.mapRingHom H
            ((localizationToComplex d).comp
              (CompatibleLocalBlock.compatibleSubgroupLocalizationInclusion d H))
            (BlockOrthogonality.localizedPrincipalBlockElement l) := by
      simpa only [RingHom.coe_comp, Function.comp_apply] using hcomp.symm
    exact hcomp'.trans hbase
  have haction := ambientLocalizedCentralScalar_action d H i rho hrho e
  have hindicator := BlockOrthogonality.principalBlockElement_action
    l i rho hrho
  apply localizationToComplex_injective d
  apply smul_one_injective (V := Fin n → ℂ)
  calc
    localizationToComplex d (ambientLocalizedCentralScalar d H i e) •
        (1 : Module.End ℂ (Fin n → ℂ)) =
      rho.asAlgebraHom
        (MonoidAlgebra.mapRingHom H (localizationToComplex d) e.1) :=
          haction.symm
    _ = rho.asAlgebraHom (BlockOrthogonality.principalBlockElement l) := by
      rw [hmap]
    _ = (if i ∈ l.block then (1 : ℂ) else 0) •
        (1 : Module.End ℂ (Fin n → ℂ)) := hindicator
    _ = localizationToComplex d
          (if i ∈ l.block then
            (1 : Localization.AtPrime d.primeIdeal) else 0) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
      split <;> simp

private noncomputable def localCharacterValueInAmbientLocalization
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I) (g : H) :
    Localization.AtPrime d.primeIdeal :=
  algebraMap (Representation.cyclotomicOrder d.eta)
    (Localization.AtPrime d.primeIdeal)
    (CompatibleLocalBlock.cyclotomicOrderInclusion
      (CompatibleLocalBlock.subgroupRoot_mem d H)
      (characterValueInCyclotomicOrder
        (CompatibleBrauerBlock.localData d H) i g))

@[simp] private theorem localizationToComplex_localCharacterValueInAmbientLocalization
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I) (g : H) :
    localizationToComplex d (localCharacterValueInAmbientLocalization d H i g) =
      (CompatibleBrauerBlock.localData d H).chi i (ConjClasses.mk g) := by
  exact localizationToComplex_cyclotomicOrderInclusion d
    (CompatibleLocalBlock.subgroupRoot_mem d H) _

private theorem card_mul_coeff_eq_sum_ambientLocalizedCentralScalar
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H))
    (g : H) :
    (Nat.card H : Localization.AtPrime d.primeIdeal) * z.1 g =
      ∑ i : (CompatibleBrauerBlock.localData d H).I,
        ambientLocalizedCentralScalar d H i z *
          localCharacterValueInAmbientLocalization d H i 1 *
          localCharacterValueInAmbientLocalization d H i g⁻¹ := by
  classical
  let l := CompatibleBrauerBlock.localData d H
  apply localizationToComplex_injective d
  simp only [map_mul, map_sum, map_natCast,
    localizationToComplex_localCharacterValueInAmbientLocalization]
  change (Nat.card H : ℂ) *
      (MonoidAlgebra.mapRingHom H (localizationToComplex d) z.1) g =
    ∑ i : l.I,
      localizationToComplex d (ambientLocalizedCentralScalar d H i z) *
        l.chi i (ConjClasses.mk (1 : H)) *
        l.chi i (ConjClasses.mk g⁻¹)
  let zC := MonoidAlgebra.mapRingHom H (localizationToComplex d) z.1
  have hzC : zC ∈ Set.center (MonoidAlgebra ℂ H) :=
    mapRingHom_mem_center (localizationToComplex d) z.1 z.property
  have hcoeff :=
    BlockOrthogonality.coeff_eq_inv_card_mul_sum_scalar_degree_character
      l.chi l.complete zC (Semigroup.mem_center_iff.mp hzC)
      (fun i => localizationToComplex d
        (ambientLocalizedCentralScalar d H i z))
      (by
        intro i n rho hrho
        exact ambientLocalizedCentralScalar_action d H i rho hrho z) g
  have hcard : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  change zC g = _ at hcoeff
  change (Nat.card H : ℂ) * zC g = _
  rw [hcoeff]
  field_simp [hcard]

private theorem localizationToResidue_ambientLocalizedCentralScalar_eq_zero_of_map_eq_zero
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (i : (CompatibleBrauerBlock.localData d H).I)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H))
    (hz : MonoidAlgebra.mapRingHom H
        (BrauerBlockReduction.localizationToResidue d) z.1 = 0) :
    BrauerBlockReduction.localizationToResidue d
        (ambientLocalizedCentralScalar d H i z) = 0 := by
  classical
  unfold ambientLocalizedCentralScalar
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro c _hc
  rw [map_mul]
  have hc := congrArg
    (fun a : MonoidAlgebra
        (BrauerBlockReduction.principalResidueField d) H =>
      a (CentralScalarCongruence.classRepresentative c)) hz
  change BrauerBlockReduction.localizationToResidue d
      (z.1 (CentralScalarCongruence.classRepresentative c)) = 0 at hc
  have hcoeff : BrauerBlockReduction.localizationToResidue d
      (CentralScalarCongruence.centralClassCoefficient z c) = 0 := by
    simpa only [CentralScalarCongruence.centralClassCoefficient] using hc
  rw [hcoeff, zero_mul]

private theorem exists_pow_reduce_eq_zero_of_all_ambientLocalizedCentralScalar_nonunit
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H))
    (hscalar : ∀ i : (CompatibleBrauerBlock.localData d H).I,
      ¬ IsUnit (ambientLocalizedCentralScalar d H i z)) :
    ∃ N : ℕ, 0 < N ∧
      MonoidAlgebra.mapRingHom H
          (BrauerBlockReduction.localizationToResidue d)
          ((z ^ N : Subring.center
            (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H)).1) = 0 := by
  classical
  let R := Localization.AtPrime d.primeIdeal
  let l := CompatibleBrauerBlock.localData d H
  letI : IsDiscreteValuationRing R :=
    CyclotomicDVR.cyclotomicOrderAtPrime_isDiscreteValuationRing d
  have hcard : (Nat.card H : R) ≠ 0 := by
    intro hzero
    have hmap := congrArg (localizationToComplex d) hzero
    have hcardC : (Nat.card H : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := H)).ne'
    exact hcardC (by simpa [R] using hmap)
  obtain ⟨N, hN, huniform⟩ :=
    exists_uniform_pow_eq_mul_nonunit (R := R)
      (Nat.card H : R) hcard
  have hquot : ∀ i : l.I, ∃ q : R,
      ambientLocalizedCentralScalar d H i z ^ N =
        (Nat.card H : R) * q ∧ ¬ IsUnit q := by
    intro i
    exact huniform _ (hscalar i)
  choose q hq hq_nonunit using hquot
  refine ⟨N, hN, ?_⟩
  ext g
  rw [MonoidAlgebra.mapRingHom_apply]
  apply (localizationToResidue_eq_zero_iff_not_isUnit d _).2
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  have hreconstruct :=
    card_mul_coeff_eq_sum_ambientLocalizedCentralScalar d H (z ^ N) g
  simp_rw [ambientLocalizedCentralScalar_pow_of_pos d H _ z N hN] at hreconstruct
  have hcoeff :
      ((z ^ N : Subring.center
          (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H)).1 g) =
        ∑ i : l.I,
          q i * localCharacterValueInAmbientLocalization d H i 1 *
            localCharacterValueInAmbientLocalization d H i g⁻¹ := by
    apply mul_left_cancel₀ hcard
    calc
      (Nat.card H : R) *
          ((z ^ N : Subring.center
            (MonoidAlgebra (Localization.AtPrime d.primeIdeal) H)).1 g) =
        ∑ i : l.I,
          ambientLocalizedCentralScalar d H i z ^ N *
            localCharacterValueInAmbientLocalization d H i 1 *
            localCharacterValueInAmbientLocalization d H i g⁻¹ :=
        hreconstruct
      _ = ∑ i : l.I,
          ((Nat.card H : R) * q i) *
            localCharacterValueInAmbientLocalization d H i 1 *
            localCharacterValueInAmbientLocalization d H i g⁻¹ := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hq i]
      _ = (Nat.card H : R) *
          ∑ i : l.I,
            q i * localCharacterValueInAmbientLocalization d H i 1 *
              localCharacterValueInAmbientLocalization d H i g⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  rw [hcoeff]
  apply Ideal.sum_mem
  intro i _hi
  apply (IsLocalRing.maximalIdeal R).mul_mem_right
  apply (IsLocalRing.maximalIdeal R).mul_mem_right
  rw [IsLocalRing.mem_maximalIdeal]
  exact hq_nonunit i

/-- The compatible local principal selector remains centrally primitive after
extension from its finite residue field to the ambient finite residue field. -/
theorem localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (H : Subgroup G) :
    IsCentrallyPrimitive
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d H) := by
  have hsource : FiniteFieldPrimitivity.IsCentrallyPrimitive
      (BrauerBlockReduction.reducedPrincipalBlockElement
        (CompatibleBrauerBlock.localData d H)) := by
    simpa only [FiniteFieldPrimitivity.IsCentrallyPrimitive,
      IsCentrallyPrimitive] using
      reducedPrincipalBlockElement_isCentrallyPrimitive
        (CompatibleBrauerBlock.localData d H)
  have hambient :=
    FiniteFieldPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive_of_source
      d H hsource
  simpa only [FiniteFieldPrimitivity.IsCentrallyPrimitive,
    IsCentrallyPrimitive] using hambient

/-- Central primitivity of the reduced compatible local principal selector
upgrades its known nonzero intersection with the ambient Brauer selector to
the exact factor identity.  This is the conclusion supplied by primitivity;
it does not assert that the Brauer selector has no other local factors. -/
theorem localPrincipalBlockElement_mul_involutionBrauer_eq_self_of_primitive
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1)
    (hprimitive : IsCentrallyPrimitive
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer ({z} : Set G)))) :
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer ({z} : Set G)) := by
  let eLocal :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer ({z} : Set G))
  let eBrauer := BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  obtain ⟨hcenter, hidem, hne⟩ :=
    CompatibleBrauerBlock.localPrincipalBlockElement_mul_involutionBrauer_isCentralIdempotent
      d z hz
  have hfactor : (eLocal * eBrauer) * eLocal = eLocal * eBrauer := by
    have heLocal := hprimitive.2.1
    have heLocalCenter := hprimitive.1
    have heBrauerCenter :=
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z
    have hcomm : eBrauer * eLocal = eLocal * eBrauer :=
      (Semigroup.mem_center_iff.mp heBrauerCenter eLocal).symm
    calc
      (eLocal * eBrauer) * eLocal = eLocal * (eBrauer * eLocal) :=
        mul_assoc _ _ _
      _ = eLocal * (eLocal * eBrauer) := by rw [hcomm]
      _ = (eLocal * eLocal) * eBrauer := (mul_assoc _ _ _).symm
      _ = eLocal * eBrauer := by rw [heLocal.eq]
  exact hprimitive.2.2.2 (eLocal * eBrauer) hcenter hidem hfactor hne

/-- The compatible local principal selector is a factor of the involution
Brauer image of the ambient principal selector. -/
theorem localPrincipalBlockElement_mul_involutionBrauer_eq_self
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1) :
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) *
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer ({z} : Set G)) := by
  exact localPrincipalBlockElement_mul_involutionBrauer_eq_self_of_primitive
    d z hz
    (localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive d
      (Subgroup.centralizer ({z} : Set G)))

end BlockPrimitivity

end Submission.ZStar
