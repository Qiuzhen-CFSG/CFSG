module

public import Theory.AlgebraicGroup.Morphism.BijectiveCoordinatePowers
public import Theory.AlgebraicGroup.Irreducible.Product
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.FiniteType

/-!
# A nonempty flat open for a bijective group morphism

Let `H → G` be a bijective morphism of algebraic groups over an algebraically
closed field of characteristic two, with `H` connected. Its coordinate-ring
map is flat after inverting a nonzero function on `G`.

Connectedness makes the source coordinate ring a domain, and point surjectivity
makes the pullback injective. Point injectivity makes the tensor differences
nilpotent. Passing to fraction fields and taking Frobenius powers makes those
differences zero; faithful flatness of field extensions then implies that the
coordinate-ring extension is algebraic. Clearing denominators in finitely many
algebra generators gives a finite subalgebra with the same localization. A
finite module over a Noetherian domain is free on a nonempty principal open,
which supplies the required flat localization.

This supplies the flat-open premise in the coordinate-power descent used for
inseparable isogenies in GLS3, Chapter 1, Sections 1.10--1.12
(`refs/KGroup/GLS3/Chapter1.tex`). It requires no separability or regular inverse.
-/

universe u

open scoped nonZeroDivisors TensorProduct
set_option linter.style.haveILetI false

private theorem exists_flat_away_of_finite
    {R B : Type*} [CommRing R] [CommRing B] [IsDomain R] [IsNoetherianRing R]
    [Algebra R B] [Module.Finite R B] :
    ∃ r : R, r ≠ 0 ∧ (Localization.awayMap (algebraMap R B) r).Flat := by
  let K := FractionRing R
  letI : Module.FinitePresentation R B := Module.finitePresentation_of_finite R B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    R⁰ (LocalizedModule.mkLinearMap R⁰ B) K
  refine ⟨r, nonZeroDivisors.ne_zero hr, ?_⟩
  let Br := Localization.Away (algebraMap R B r)
  letI : Algebra (Localization.Away r) Br := localizationAlgebra (.powers r) B
  letI : IsScalarTower R (Localization.Away r) Br :=
    isScalarTower_localizationAlgebra (.powers r) B
  letI := hfree
  let e : LocalizedModule.Away r B ≃ₗ[Localization.Away r] Br :=
    (IsLocalizedModule.iso (.powers r)
      (IsScalarTower.toAlgHom R B Br).toLinearMap).extendScalarsOfIsLocalization
        (.powers r) (Localization.Away r)
  have hflat : Module.Flat (Localization.Away r) Br := Module.Flat.of_linearEquiv e.symm
  exact hflat

private theorem flat_away_mul
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (r c : R) (hf : (Localization.awayMap f r).Flat) :
    (Localization.awayMap f (r * c)).Flat := by
  let Rr := Localization.Away r
  let Ar := Localization.Away (f r)
  let Rrc := Localization.Away (algebraMap R Rr c)
  let Arc := Localization.Away (algebraMap A Ar (f c))
  letI : Algebra R A := f.toAlgebra
  let fr : Rr →+* Ar := Localization.awayMap f r
  have heq : fr (algebraMap R Rr c) = algebraMap A Ar (f c) := by
    exact IsLocalization.map_eq _ c
  letI : IsLocalization.Away (fr (algebraMap R Rr c)) Arc := heq.symm ▸ inferInstance
  let g : Rrc →+* Arc := IsLocalization.Away.map Rrc Arc fr (algebraMap R Rr c)
  have hflat : g.Flat := RingHom.Flat.propertyIsLocal.localizationAwayPreserves
    fr (algebraMap R Rr c) Rrc Arc hf
  letI : IsLocalization.Away (r * c) Rrc := inferInstance
  letI : IsLocalization.Away (f (r * c)) Arc := by
    rw [map_mul]
    infer_instance
  let eR : Localization.Away (r * c) ≃ₐ[R] Rrc :=
    IsLocalization.algEquiv (.powers (r * c)) _ _
  let eA : Arc ≃ₐ[A] Localization.Away (f (r * c)) :=
    IsLocalization.algEquiv (.powers (f (r * c))) _ _
  have he : Localization.awayMap f (r * c) =
      eA.toRingHom.comp (g.comp eR.toRingHom) := by
    apply IsLocalization.ringHom_ext (.powers (r * c))
    ext x
    change Localization.awayMap f (r * c) (algebraMap R _ x) =
      eA (g (eR (algebraMap R _ x)))
    rw [eR.commutes, IsScalarTower.algebraMap_apply R Rr Rrc]
    rw [show g (algebraMap Rr Rrc (algebraMap R Rr x)) =
        algebraMap Ar Arc (fr (algebraMap R Rr x)) from IsLocalization.map_eq _ _]
    rw [show fr (algebraMap R Rr x) = algebraMap A Ar (f x) from
      IsLocalization.map_eq _ _]
    rw [← IsScalarTower.algebraMap_apply A Ar Arc, eA.commutes]
    exact IsLocalization.map_eq _ _
  rw [he]
  exact (RingHom.Flat.of_bijective eR.bijective).comp hflat |>.comp
    (RingHom.Flat.of_bijective eA.bijective)

private theorem exists_finite_subalgebra_away
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R]
    [Algebra R A] [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A] :
    ∃ (B : Subalgebra R A) (c : R), c ≠ 0 ∧ B.toSubmodule.FG ∧
      Function.Bijective (Localization.awayMap B.val.toRingHom (algebraMap R B c)) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  obtain ⟨c, hc, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples R s
  let B := Algebra.adjoin R ((fun x : A => c • x) '' (s : Set A))
  have hfg : B.toSubmodule.FG := fg_adjoin_of_finite
    (s.finite_toSet.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hint x hx)
  refine ⟨B, c, hc, hfg, IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, ?_⟩
  let d := algebraMap R A c
  let D : Subalgebra R A :=
    { carrier := {x | ∃ n : ℕ, d ^ n * x ∈ B}
      algebraMap_mem' := fun x => ⟨0, by simp⟩
      zero_mem' := ⟨0, by simp⟩
      one_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have he : d ^ (m + n) * (x + y) =
            algebraMap R A (c ^ n) * (d ^ m * x) +
              algebraMap R A (c ^ m) * (d ^ n * y) := by
          simp only [map_pow, pow_add, d]
          ring
        rw [he]
        exact B.add_mem (B.mul_mem (B.algebraMap_mem _) hm)
          (B.mul_mem (B.algebraMap_mem _) hn)
      mul_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have he : d ^ (m + n) * (x * y) = (d ^ m * x) * (d ^ n * y) := by
          rw [pow_add]
          ring
        rw [he]
        exact B.mul_mem hm hn }
  have hD : D = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Algebra.adjoin_le
    intro x hx
    refine ⟨1, ?_⟩
    rw [pow_one]
    change algebraMap R A c * x ∈ B
    rw [← Algebra.smul_def]
    exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  apply Localization.awayMap_surjective_iff.mpr
  intro x
  have hx : x ∈ D := by rw [hD]; trivial
  obtain ⟨n, hn⟩ := hx
  exact ⟨⟨d ^ n * x, hn⟩, n, rfl⟩

private theorem exists_flat_away_of_isAlgebraic
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] [IsNoetherianRing R]
    [Algebra R A] [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A] :
    ∃ c : R, c ≠ 0 ∧ (Localization.awayMap (algebraMap R A) c).Flat := by
  obtain ⟨B, c, hc, hfg, hbij⟩ := exists_finite_subalgebra_away (R := R) (A := A)
  letI : Module.Finite R B := ⟨(Submodule.fg_top _).mpr hfg⟩
  obtain ⟨r, hr, hflat⟩ := exists_flat_away_of_finite (R := R) (B := B)
  refine ⟨r * c, mul_ne_zero hr hc, ?_⟩
  have hflat' := flat_away_mul (algebraMap R B) r c hflat
  have hbij' := Localization.awayMap_bijective_of_dvd B.val.toRingHom
    (map_dvd (algebraMap R B) (dvd_mul_left c r)) hbij
  have he : Localization.awayMap (algebraMap R A) (r * c) =
      (Localization.awayMap B.val.toRingHom (algebraMap R B (r * c))).comp
        (Localization.awayMap (algebraMap R B) (r * c)) := by
    apply IsLocalization.ringHom_ext (.powers (r * c))
    ext x
    change Localization.awayMap (algebraMap R A) (r * c) (algebraMap R _ x) =
      Localization.awayMap B.val.toRingHom (algebraMap R B (r * c))
        (Localization.awayMap (algebraMap R B) (r * c) (algebraMap R _ x))
    simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  rw [he]
  exact hflat'.comp (RingHom.Flat.of_bijective hbij')

private theorem mem_range_of_tensor_eq
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (b : S) (h : b ⊗ₜ[R] (1 : S) = 1 ⊗ₜ[R] b) :
    b ∈ Set.range (algebraMap R S) := by
  let Q := S ⧸ LinearMap.range (Algebra.linearMap R S)
  let π : S →ₗ[R] Q := (LinearMap.range (Algebra.linearMap R S)).mkQ
  have h1 : π 1 = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨1, (algebraMap R S).map_one⟩
  have hb : (1 : S) ⊗ₜ[R] π b = 0 := by
    have h' := congrArg (TensorProduct.map (LinearMap.id : S →ₗ[R] S) π) h
    simpa [h1] using h'.symm
  have hb' : π b = 0 :=
    (Module.FaithfullyFlat.one_tmul_eq_zero_iff R Q (A := S) (π b)).mp hb
  exact (Submodule.Quotient.mk_eq_zero _).mp hb'

private theorem algebraic_of_tensor_nilpotent
    {R A : Type*} [CommRing R] [CommRing A] [IsDomain R] [IsDomain A]
    [Algebra R A] [FaithfulSMul R A] (p : ℕ) [Fact p.Prime] [CharP A p]
    (h : ∀ b : A, IsNilpotent (b ⊗ₜ[R] (1 : A) - 1 ⊗ₜ[R] b)) :
    Algebra.IsAlgebraic R A := by
  let K := FractionRing R
  let L := FractionRing A
  letI : Algebra K L := FractionRing.liftAlgebra R L
  letI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  letI : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K R⁰
  let τ : A ⊗[R] A →+* L ⊗[K] L := Algebra.TensorProduct.mapRingHom
    (algebraMap R K) (algebraMap A L) (algebraMap A L)
    (by rw [← IsScalarTower.algebraMap_eq R A L, ← IsScalarTower.algebraMap_eq R K L])
    (by rw [← IsScalarTower.algebraMap_eq R A L, ← IsScalarTower.algebraMap_eq R K L])
  letI : CharP L p := charP_of_injective_algebraMap (IsFractionRing.injective A L) p
  letI : Nontrivial (L ⊗[K] L) :=
    (Algebra.TensorProduct.lmul' K (S := L)).toRingHom.domain_nontrivial
  letI : CharP (L ⊗[K] L) p := charP_of_injective_algebraMap
    (algebraMap L (L ⊗[K] L)).injective p
  refine ⟨fun b => ?_⟩
  have hn : IsNilpotent (algebraMap A L b ⊗ₜ[K] (1 : L) -
      1 ⊗ₜ[K] algebraMap A L b) := by
    simpa [τ] using (h b).map τ
  obtain ⟨n, hn⟩ := hn
  have hp : (algebraMap A L b ⊗ₜ[K] (1 : L) -
      1 ⊗ₜ[K] algebraMap A L b) ^ (p ^ n) = 0 :=
    pow_eq_zero_of_le (Nat.le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)) hn
  rw [sub_pow_char_pow, sub_eq_zero] at hp
  have heq : (algebraMap A L b ^ (p ^ n)) ⊗ₜ[K] (1 : L) =
      1 ⊗ₜ[K] (algebraMap A L b ^ (p ^ n)) := by
    simpa only [Algebra.TensorProduct.tmul_pow, one_pow] using hp
  obtain ⟨x, hx⟩ := mem_range_of_tensor_eq _ heq
  have halg : IsAlgebraic K (algebraMap A L b) :=
    (hx ▸ isAlgebraic_algebraMap (R := K) (A := L) x).of_pow
      (pow_pos (Fact.out : p.Prime).pos _)
  have halgR : IsAlgebraic R (algebraMap A L b) :=
    (Algebra.IsAlgebraic.isAlgebraic_iff R K).mpr halg
  exact (isAlgebraic_algebraMap_iff (R := R) (IsFractionRing.injective A L)).mp halgR

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

/-- A bijective group morphism with connected source has flat pullback over
some nonempty principal open of the target. -/
public theorem Morphism.exists_flat_localization_of_bijective_of_connected
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hH : IsConnected (Set.univ : Set (Variety.Point H)))
    (hbij : Function.Bijective φ.onPoints) :
    ∃ c : Variety.PolynomialFunction G, c ≠ 0 ∧
      RingHom.Flat (Localization.awayMap φ.toVariety.pullbackRingHom c) := by
  let R := Variety.PolynomialFunction G
  let A := Variety.PolynomialFunction H
  letI : IsDomain (coordinateRing H) := connectedAlgebraicGroup_coordinateRing_domain H hH
  letI : IsDomain A := (coordinateRingAlgEquivPolynomialFunction H).toRingEquiv.isDomain_iff.mp
    inferInstance
  letI : Algebra R A := φ.toVariety.pullbackRingHom.toAlgebra
  have hinj : Function.Injective (algebraMap R A) := by
    intro a b hab
    apply Variety.PolynomialFunction.ext
    intro y
    obtain ⟨x, rfl⟩ := hbij.2 y
    exact congrArg (fun f : A => f x) hab
  letI : IsDomain R := Function.Injective.isDomain (algebraMap R A) hinj
  letI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hinj
  letI : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' (by
    exact φ.toVariety.pullbackAlgHom.comp_algebraMap.symm)
  letI : Algebra.FiniteType k R := polynomialFunction_finiteType G
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : Algebra.FiniteType k A := polynomialFunction_finiteType H
  letI : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType k R A
  letI : CharP A 2 := charP_of_injective_algebraMap (algebraMap k A).injective 2
  letI : Algebra.IsAlgebraic R A := algebraic_of_tensor_nilpotent 2
    (φ.toVariety.tensor_difference_isNilpotent_of_injective hbij.1)
  exact exists_flat_away_of_isAlgebraic (R := R) (A := A)

end Theory.AlgebraicGroup
