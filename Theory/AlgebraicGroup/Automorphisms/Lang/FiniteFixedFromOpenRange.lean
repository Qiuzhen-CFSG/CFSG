module

public import Mathlib.RingTheory.ZariskisMainTheorem
public import Theory.AlgebraicGroup.Automorphisms.Lang.FiniteFiberDominance
public import Theory.AlgebraicGroup.Dimension.Finite

universe u

/-!
# Finite fixed points from an open Lang range

For a connected algebraic group, a nonempty open subset in the range of the
regular Lang morphism forces its pullback on the coordinate ring to be
injective: a regular function vanishing on that range vanishes on a dense open
set and hence everywhere.  Equal source and target dimensions make the generic
coordinate-ring extension algebraic, hence quasi-finite.  Zariski's Main
Theorem spreads this to a principal open meeting the inverse image of the
prescribed open range.

At the resulting point, quasi-finiteness isolates that point in its Lang
fiber.  The fiber is a torsor under the fixed points: regular right translation
by `a⁻¹b` carries the isolated point `a` to any other fiber point `b` and
preserves the fiber.  Thus the fiber is discrete; it is compact because the
variety point space is Noetherian, so it is finite.  Translation by `a` then
embeds the fixed-point subtype into this fiber.  This is the converse geometric
implication in Steinberg 10.2; no Lang--Steinberg surjectivity or
solvable/invariant-Borel reduction is used.
-/

namespace Theory.AlgebraicGroup

open Topology
open scoped nonZeroDivisors
open Cardinal

variable {k : Type u} [Field k]

/-- Right translation is a homeomorphism because it and translation by the
inverse are regular morphisms. -/
private noncomputable def rightTranslationHomeomorph
    {K : Variety k} [AlgebraicGroup K] (c : Variety.Point K) :
    Variety.Point K ≃ₜ Variety.Point K where
  toEquiv := Equiv.mulRight c
  continuous_toFun := by
    change Continuous (fun x : Variety.Point K => x * c)
    have hfun : (fun x : Variety.Point K => x * c) =
        (rightMulMorphism K c).toFun := by
      funext x
      exact (rightMulMorphism_apply K c x).symm
    rw [hfun]
    exact (rightMulMorphism K c).continuous
  continuous_invFun := by
    change Continuous (fun x : Variety.Point K => x * c⁻¹)
    have hfun : (fun x : Variety.Point K => x * c⁻¹) =
        (rightMulMorphism K c⁻¹).toFun := by
      funext x
      exact (rightMulMorphism_apply K c⁻¹ x).symm
    rw [hfun]
    exact (rightMulMorphism K c⁻¹).continuous

/-- An algebraic finite-type extension of domains is quasi-finite at its
generic point.  The proof passes to fraction fields, where algebraic finite
type extensions are finite, and transports back to the generic localization. -/
private lemma quasiFiniteAt_bot_of_isAlgebraic
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsDomain R] [IsDomain A] [FaithfulSMul R A]
    [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A] :
    Algebra.QuasiFiniteAt R (⊥ : Ideal A) := by
  unfold Algebra.QuasiFiniteAt
  let hTarget : Algebra R (Localization.AtPrime (⊥ : Ideal A)) :=
    OreLocalization.instAlgebra
  let L := Localization.AtPrime (⊥ : Ideal A)
  let K := FractionRing R
  let F := FractionRing A
  have hL : IsFractionRing A L := by
    simpa [Ideal.primeCompl_bot] using
      Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)
  let : IsFractionRing A L := hL
  let : Algebra R L := hTarget
  let : Algebra R K := inferInstance
  let : Algebra K F := FractionRing.liftAlgebra R F
  let : IsScalarTower R K F := FractionRing.isScalarTower_liftAlgebra R F
  let : Algebra.IsAlgebraic R F :=
    (IsFractionRing.isAlgebraic_iff' R A F).mp inferInstance
  let : Algebra.IsAlgebraic K F :=
    Algebra.IsAlgebraic.extendScalars
      (FaithfulSMul.algebraMap_injective R K)
  let : Algebra.EssFiniteType R F :=
    Algebra.EssFiniteType.comp R A F
  let : Algebra.EssFiniteType K F :=
    Algebra.EssFiniteType.of_comp R K F
  let : Module.Finite K F :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  let : Algebra.QuasiFinite R K := inferInstance
  let : Algebra.QuasiFinite K F := inferInstance
  have hF : Algebra.QuasiFinite R F := Algebra.QuasiFinite.trans R K F
  let eA : F ≃ₐ[A] L :=
    IsLocalization.algEquiv (nonZeroDivisors A) F L
  let f : F →ₐ[R] L :=
    { eA.toRingHom with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply R A F,
          IsScalarTower.algebraMap_apply R A L]
        exact eA.commutes (algebraMap R A r) }
  let : Algebra.QuasiFinite R F := hF
  change @Algebra.QuasiFinite R L _ _ hTarget
  exact Algebra.QuasiFinite.of_surjective_algHom f eA.surjective

/-- The principal open furnished by Zariski's Main Theorem consists of
quasi-finite points. -/
private lemma quasiFiniteAt_of_fg_and_awayMap_bijective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (S' : Subalgebra R S) (hS' : S'.toSubmodule.FG) (r : S')
    {p : Ideal S} [p.IsPrime] (hrp : r.1 ∉ p)
    (H : Function.Bijective (Localization.awayMap S'.val.toRingHom r)) :
    Algebra.QuasiFiniteAt R p := by
  have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : Algebra.QuasiFinite R (Localization.Away r) :=
    .trans R S' _
  have : Algebra.QuasiFinite R (Localization.Away r.1) :=
    .of_surjective_algHom (Localization.awayMapₐ S'.val r) H.2
  let f : Localization.Away r.1 →ₐ[S] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom r.1 (f := Algebra.ofId _ _) <|
      IsLocalization.map_units (M := p.primeCompl)
        (Localization.AtPrime p) ⟨r, hrp⟩
  refine .of_forall_exists_mul_mem_range (f.restrictScalars R) fun x ↦ ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  exact ⟨algebraMap _ _ s,
    by simpa using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp⟩

private lemma pullback_injective_of_open_range
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hK : Variety.IsConnected K)
    (U : Set (Variety.Point K)) (hUopen : IsOpen U)
    (hUne : U.Nonempty)
    (hUrange : U ⊆ Set.range (langMorphism σ).toFun) :
    Function.Injective (langMorphism σ).pullbackAlgHom := by
  let hKi := connectedAlgebraicGroup_irreducible K hK
  let : PreirreducibleSpace (Variety.Point K) := ⟨hKi.2⟩
  have hUdense : Dense U := hUopen.dense hUne
  have hzero : ∀ p : Variety.PolynomialFunction K,
      (langMorphism σ).pullbackAlgHom p = 0 → p = 0 := by
    intro p hp
    obtain ⟨q, hq⟩ := p.representedBy
    let Z : Set (Variety.Point K) := {x | evalPolynomial x.val q = 0}
    have hZ : IsZariskiClosed K Z := by
      exact ⟨{q}, by ext x; simp [Z]⟩
    have hUZ : U ⊆ Z := by
      intro x hx
      obtain ⟨g, rfl⟩ := hUrange hx
      have hp' := congrArg (fun z : Variety.PolynomialFunction K => z g) hp
      change p ((langMorphism σ).toFun g) = 0 at hp'
      rw [hq] at hp'
      exact hp'
    have hcl : closure U ⊆ Z :=
      closure_minimal hUZ (Variety.isClosed_iff_isZariskiClosed.mpr hZ)
    apply Variety.PolynomialFunction.ext
    intro x
    have hxZ : x ∈ Z := by
      rw [hUdense.closure_eq] at hcl
      exact hcl (by simp)
    rw [hq]
    exact hxZ
  intro p r hpr
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, sub_eq_zero.mpr hpr]

private lemma trdeg_zero_of_equal_base_trdeg
    {A B : Type u} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [Algebra k A] [Algebra k B] [Algebra B A]
    [IsScalarTower k B A] [FaithfulSMul B A]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    [Algebra.FiniteType B A]
    (hEq : Algebra.trdeg k A = Algebra.trdeg k B) :
    Algebra.trdeg B A = 0 := by
  have hBfin : Algebra.trdeg k B < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have hrelfin : Algebra.trdeg B A < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have htower : Algebra.trdeg k A =
      Algebra.trdeg k B + Algebra.trdeg B A :=
    (trdeg_add_eq (R := k) (S := B) (A := A)).symm
  have htowerNat : Cardinal.toNat (Algebra.trdeg k A) =
      Cardinal.toNat (Algebra.trdeg k B) +
        Cardinal.toNat (Algebra.trdeg B A) := by
    rw [htower, Cardinal.toNat_add hBfin hrelfin]
  rw [hEq] at htowerNat
  have hzeroNat : Cardinal.toNat (Algebra.trdeg B A) = 0 := by
    have hsum : Cardinal.toNat (Algebra.trdeg k B) +
        Cardinal.toNat (Algebra.trdeg B A) =
        Cardinal.toNat (Algebra.trdeg k B) + 0 := by
      simpa using htowerNat.symm
    exact Nat.add_left_cancel hsum
  exact (Cardinal.toNat_eq_zero.mp hzeroNat).resolve_right (not_le_of_gt hrelfin)

private lemma exists_finite_lang_fiber_in_open_range
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hK : Variety.IsConnected K)
    (U : Set (Variety.Point K)) (hUopen : IsOpen U)
    (hUne : U.Nonempty)
    (hUrange : U ⊆ Set.range (langMorphism σ).toFun) :
    ∃ a : Variety.Point K,
      (langMorphism σ).toFun a ∈ U ∧
        Set.Finite {g : Variety.Point K |
          (langMorphism σ).toFun g = (langMorphism σ).toFun a} := by
  let f := langMorphism σ
  let P := Variety.PolynomialFunction K
  let hKi := connectedAlgebraicGroup_irreducible K hK
  let : PreirreducibleSpace (Variety.Point K) := ⟨hKi.2⟩
  let : IsDomain (coordinateRing K) :=
    isDomain_coordinateRing_of_isIrreducible K hKi
  let : IsDomain P :=
    (coordinateRingAlgEquivPolynomialFunction K).toRingEquiv.isDomain_iff.mp
      inferInstance
  let : Algebra P P := f.pullbackAlgHom.toRingHom.toAlgebra
  let : SMul P P := Algebra.toSMul
  let : Module P P := Algebra.toModule
  have hscalar : algebraMap k P =
      (algebraMap P P).comp (algebraMap k P) := by
    apply RingHom.ext
    intro r
    exact (f.pullbackAlgHom.commutes r).symm
  let : IsScalarTower k P P := IsScalarTower.of_algebraMap_eq' hscalar
  let : FaithfulSMul P P :=
    (faithfulSMul_iff_algebraMap_injective P P).mpr
      (pullback_injective_of_open_range σ hK U hUopen hUne hUrange)
  let : Algebra.FiniteType k P := polynomialFunction_finiteType K
  let : Algebra.FiniteType P P :=
    Algebra.FiniteType.of_restrictScalars_finiteType k P P
  have htr : Algebra.trdeg P P = 0 :=
    trdeg_zero_of_equal_base_trdeg (k := k) (A := P) (B := P) rfl
  let : Algebra.IsAlgebraic P P :=
    (trdeg_eq_zero_iff (R := P) (A := P)).mp htr
  have hqf0 : Algebra.QuasiFiniteAt P (⊥ : Ideal P) :=
    quasiFiniteAt_bot_of_isAlgebraic
  let : Algebra.QuasiFiniteAt P (⊥ : Ideal P) := hqf0
  have hzm : Algebra.ZariskisMainProperty P (⊥ : Ideal P) :=
    Algebra.ZariskisMainProperty.of_finiteType (R := P) (S := P)
      (⊥ : Ideal P)
  obtain ⟨S', hS', r, hr0, hrbij⟩ :=
    hzm.exists_fg_and_exists_notMem_and_awayMap_bijective (⊥ : Ideal P)
  let D : Set (Variety.Point K) :=
    K.pointPrime ⁻¹' PrimeSpectrum.basicOpen r.1
  have hDopen : IsOpen D :=
    PrimeSpectrum.isOpen_basicOpen.preimage K.continuous_pointPrime
  have hDne : D.Nonempty := by
    by_contra hD
    have hrzero : r.1 = 0 := by
      apply Variety.PolynomialFunction.ext
      intro x
      have hxnot : x ∉ D := by
        simp [Set.not_nonempty_iff_eq_empty.mp hD]
      have hxmem : r.1 ∈ (K.pointPrime x).asIdeal := by
        simpa [D, PrimeSpectrum.mem_basicOpen] using hxnot
      change polynomialFunctionPointAlgHom K x r.1 = 0 at hxmem
      exact hxmem
    exact hr0 (by simp [hrzero])
  let E : Set (Variety.Point K) := f.toFun ⁻¹' U
  have hEopen : IsOpen E := hUopen.preimage f.continuous
  have hEne : E.Nonempty := by
    obtain ⟨y, hy⟩ := hUne
    obtain ⟨a, ha⟩ := hUrange hy
    refine ⟨a, ?_⟩
    change f.toFun a ∈ U
    rw [ha]
    exact hy
  obtain ⟨a, haD, haE⟩ :=
    nonempty_preirreducible_inter hDopen hEopen hDne hEne
  let M := (K.pointPrime a).asIdeal
  let N := (K.pointPrime (f.toFun a)).asIdeal
  let : M.IsPrime := (K.pointPrime a).2
  let : N.IsPrime := (K.pointPrime (f.toFun a)).2
  have hrM : r.1 ∉ M := by
    simpa [D, M, PrimeSpectrum.mem_basicOpen] using haD
  have hqfM : Algebra.QuasiFiniteAt P M :=
    quasiFiniteAt_of_fg_and_awayMap_bijective S' hS' r hrM hrbij
  let : Algebra.QuasiFiniteAt P M := hqfM
  let : Algebra.EssFiniteType P P :=
    Algebra.EssFiniteType.of_finiteType P P
  have hMN : M.LiesOver N := by
    constructor
    change Ideal.comap (algebraMap P P) M = N
    exact congrArg PrimeSpectrum.asIdeal (f.pointPrime_image a).symm
  let : M.LiesOver N := hMN
  obtain ⟨s, hsM, hs⟩ :=
    Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver (R := P) N M
  let O : Set (Variety.Point K) :=
    K.pointPrime ⁻¹' PrimeSpectrum.basicOpen s
  have hOopen : IsOpen O :=
    PrimeSpectrum.isOpen_basicOpen.preimage K.continuous_pointPrime
  have haO : a ∈ O := by
    simpa [O, M, PrimeSpectrum.mem_basicOpen] using hsM
  let F : Set (Variety.Point K) := {g | f.toFun g = f.toFun a}
  have hOisolates : O ∩ F = {a} := by
    ext x
    constructor
    · rintro ⟨hxO, hxF⟩
      have hxa : x = a := by
        by_contra hxa
        let Q := (K.pointPrime x).asIdeal
        have hQprime : Q.IsPrime := (K.pointPrime x).2
        have hQM : Q ≠ M := by
          intro hEq
          apply hxa
          apply K.pointPrime_injective
          apply PrimeSpectrum.ext
          exact hEq
        have hQN : Q.LiesOver N := by
          constructor
          change N = Ideal.comap (algebraMap P P) Q
          have hi := f.pointPrime_image x
          rw [hxF] at hi
          exact congrArg PrimeSpectrum.asIdeal hi
        have hsQ : s ∈ Q := hs Q hQprime hQM hQN
        have hnotO : x ∉ O := by
          simpa [O, Q, PrimeSpectrum.mem_basicOpen] using hsQ
        exact hnotO hxO
      simp [hxa]
    · intro hxa
      have : x = a := by simpa using hxa
      subst x
      exact ⟨haO, rfl⟩
  have hFdiscrete : IsDiscrete F := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro b hbF
    let c : Variety.Point K := a⁻¹ * b
    have hc : σ.onPoints c = c := by
      have haLang : a * σ.onPoints a⁻¹ = f.toFun a := by rfl
      have hbLang : b * σ.onPoints b⁻¹ = f.toFun a := by
        exact hbF
      have hfixed := congrArg
        (fun z => a⁻¹ * z * σ.onPoints b) (haLang.trans hbLang.symm)
      have hfixed' :
          σ.onPoints a⁻¹ * σ.onPoints b = a⁻¹ * b := by
        simpa [mul_assoc] using hfixed
      calc
        σ.onPoints c = σ.onPoints a⁻¹ * σ.onPoints b := by
          rw [σ.onPoints.map_mul]
        _ = c := hfixed'
    have hLang_mul_fixed (x : Variety.Point K) :
        f.toFun (x * c) = f.toFun x := by
      change (x * c) * σ.onPoints (x * c)⁻¹ =
        x * σ.onPoints x⁻¹
      rw [mul_inv_rev, σ.onPoints.map_mul, σ.onPoints.map_inv, hc]
      simp [mul_assoc]
    let e := rightTranslationHomeomorph (k := k) c
    refine ⟨e '' O, e.isOpenMap O hOopen, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨x, hxO, hxz⟩, hzF⟩
      change x * c = z at hxz
      have hxF : x ∈ F := by
        change f.toFun x = f.toFun a
        rw [← hLang_mul_fixed x, hxz]
        exact hzF
      have hxa : x = a := by
        have hx : x ∈ O ∩ F := ⟨hxO, hxF⟩
        rw [hOisolates] at hx
        simpa using hx
      have hzb : z = b := by
        rw [← hxz, hxa]
        simp [c]
      simp [hzb]
    · intro hzb
      have hzb' : z = b := by simpa using hzb
      subst z
      refine ⟨?_, hbF⟩
      refine ⟨a, haO, ?_⟩
      change a * c = b
      simp [c]
  have hFcompact : IsCompact F :=
    TopologicalSpace.NoetherianSpace.isCompact F
  exact ⟨a, haE, hFcompact.finite hFdiscrete⟩

/-- A nonempty open Lang range forces the fixed-point subtype to be finite. -/
public theorem finite_fixed_of_langMorphism_open_range
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hK : Variety.IsConnected K)
    (U : Set (Variety.Point K)) (hUopen : IsOpen U)
    (hUne : U.Nonempty)
    (hUrange : U ⊆ Set.range (langMorphism σ).toFun) :
    Finite {x : Variety.Point K | σ.onPoints x = x} := by
  obtain ⟨a, _, haFinite⟩ :=
    exists_finite_lang_fiber_in_open_range σ hK U hUopen hUne hUrange
  let fiber : Type u :=
    {g : Variety.Point K |
      (langMorphism σ).toFun g = (langMorphism σ).toFun a}
  let fixed : Type u := {x : Variety.Point K | σ.onPoints x = x}
  let : Finite fiber := Set.Finite.to_subtype haFinite
  let fixedToFiber : fixed → fiber := fun x => ⟨a * x.1, by
    change (a * x.1) * σ.onPoints (a * x.1)⁻¹ =
      a * σ.onPoints a⁻¹
    rw [mul_inv_rev, σ.onPoints.map_mul, σ.onPoints.map_inv, x.2]
    simp [mul_assoc]⟩
  exact Finite.of_injective fixedToFiber (by
    intro x z h
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val h))

end Theory.AlgebraicGroup
