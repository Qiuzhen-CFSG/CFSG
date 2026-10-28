module

public import Theory.AlgebraicGroup.Bor1.MaximalAlgHom
public import Theory.AlgebraicGroup.CoordinateRing.Point
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.FiniteStability
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Flatness

/-!
# Frobenius powers and bijective affine morphisms

An injective map on points over an algebraically closed field makes every
coordinate difference `b ⊗ 1 - 1 ⊗ b` nilpotent in its scheme-theoretic fiber
product. Indeed, a maximal ideal of the relative tensor algebra gives two
points with the same image, and point injectivity identifies their evaluations.
The Nullstellensatz then places the difference in the nilradical.

For a flat point-surjective morphism, faithful flatness descends the resulting
equalities of characteristic powers to the target coordinate algebra. For group
morphisms, flatness on any nonempty principal open suffices, by translation.
The existence of such a flat open is an explicit outstanding premise here;
these conditional results do not assert flatness of every group morphism.

This is the coordinate descent step used in the inseparable isogeny comparison
in GLS3, Chapter 1, Sections 1.10--1.12 (`refs/KGroup/GLS3/Chapter1.tex`).
-/

open scoped TensorProduct

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Point injectivity makes the two pullbacks of any polynomial function
agree up to nilpotence on the scheme-theoretic fiber product. -/
public theorem Variety.Morphism.tensor_difference_isNilpotent_of_injective
    {V W : Variety k} (f : Variety.Morphism V W)
    (hf : Function.Injective f.toFun) (b : Variety.PolynomialFunction V) :
    letI : Algebra (Variety.PolynomialFunction W) (Variety.PolynomialFunction V) :=
      f.pullbackRingHom.toAlgebra
    IsNilpotent (b ⊗ₜ[Variety.PolynomialFunction W] 1 -
      1 ⊗ₜ[Variety.PolynomialFunction W] b) := by
  let C := Variety.PolynomialFunction W
  let A := Variety.PolynomialFunction V
  let F := f.pullbackRingHom
  letI : Algebra C A := F.toAlgebra
  letI : IsScalarTower k C A := IsScalarTower.of_algebraMap_eq' (by
    exact f.pullbackAlgHom.comp_algebraMap.symm)
  let T := A ⊗[C] A
  letI : Algebra.FiniteType k A := polynomialFunction_finiteType V
  letI : Algebra.FiniteType C A := Algebra.FiniteType.of_restrictScalars_finiteType k C A
  letI : Algebra.FiniteType A T := inferInstance
  letI : IsScalarTower k A T := inferInstance
  letI : Algebra.FiniteType k T :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k A) inferInstance
  letI : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := k) (B := T)
  rw [← mem_nilradical]
  change (b ⊗ₜ[C] 1 - 1 ⊗ₜ[C] b : T) ∈ Ideal.radical (⊥ : Ideal T)
  rw [Ideal.radical_eq_jacobson, Ideal.jacobson, Ideal.mem_sInf]
  intro m hm
  obtain ⟨-, hmmax⟩ := hm
  obtain ⟨φ, hφker⟩ :=
    Bor1.exists_algHom_ker_eq_of_isMaximal_finiteType (k := k) m hmmax
  let iL : A →ₐ[k] T := Algebra.TensorProduct.includeLeft (R := C) (S := k)
  let iR : A →ₐ[k] T :=
    (Algebra.TensorProduct.includeRight (R := C) (A := A) (B := A)).restrictScalars k
  let φL : A →ₐ[k] k := φ.comp iL
  let φR : A →ₐ[k] k := φ.comp iR
  let x : Variety.Point V := (polynomialFunctionPointAlgHomEquiv V).symm φL
  let y : Variety.Point V := (polynomialFunctionPointAlgHomEquiv V).symm φR
  have hx : polynomialFunctionPointAlgHom V x = φL :=
    (polynomialFunctionPointAlgHomEquiv V).apply_symm_apply φL
  have hy : polynomialFunctionPointAlgHom V y = φR :=
    (polynomialFunctionPointAlgHomEquiv V).apply_symm_apply φR
  have hfx : f.toFun x = f.toFun y := by
    apply (polynomialFunctionPointAlgHomEquiv W).injective
    apply AlgHom.ext
    intro c
    calc
      polynomialFunctionPointAlgHom W (f.toFun x) c =
          polynomialFunctionPointAlgHom V x (F c) := rfl
      _ = φ (iL (F c)) := by rw [hx]; rfl
      _ = φ (iR (F c)) := by
        congr 1
        dsimp [iL, iR, F]
        exact DFunLike.congr_fun
          Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap c
      _ = polynomialFunctionPointAlgHom V y (F c) := by rw [hy]; rfl
      _ = polynomialFunctionPointAlgHom W (f.toFun y) c := rfl
  have hxy := hf hfx
  rw [← hφker]
  change φ (b ⊗ₜ[C] 1 - 1 ⊗ₜ[C] b : T) = 0
  rw [map_sub, sub_eq_zero]
  calc
    φ (b ⊗ₜ[C] 1 : T) = b x := (AlgHom.congr_fun hx b).symm
    _ = b y := congrArg b hxy
    _ = φ (1 ⊗ₜ[C] b : T) := AlgHom.congr_fun hy b

private theorem mem_range_algebraMap_of_tensor_eq
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

/-- A flat morphism surjective on algebraically closed points has faithfully
flat pullback. Surjectivity on all prime ideals follows by generalization. -/
public theorem Variety.Morphism.pullback_faithfullyFlat_of_surjective_of_flat
    {V W : Variety k}
    (f : Variety.Morphism V W) (hsurj : Function.Surjective f.toFun)
    (hflat : f.pullbackRingHom.Flat) :
    letI : Algebra (Variety.PolynomialFunction W) (Variety.PolynomialFunction V) :=
      f.pullbackRingHom.toAlgebra
    Module.FaithfullyFlat (Variety.PolynomialFunction W) (Variety.PolynomialFunction V) := by
  let C := Variety.PolynomialFunction W
  let A := Variety.PolynomialFunction V
  let F := f.pullbackRingHom
  letI : Algebra C A := F.toAlgebra
  letI : Module.Flat C A := hflat
  apply Module.FaithfullyFlat.of_comap_surjective
  intro p
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  obtain ⟨y, hy⟩ := W.exists_pointPrime_eq_of_isMaximal m hm
  obtain ⟨x, hx⟩ := hsurj y
  let P := V.pointPrime x
  have hcomap : PrimeSpectrum.comap F P = W.pointPrime y := by
    rw [← f.pointPrime_image, hx]
  have hpmy : p ≤ W.pointPrime y := by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal, hy]
    exact hpm
  have hspec : p ⤳ PrimeSpectrum.comap F P := by
    rw [hcomap]
    exact (PrimeSpectrum.le_iff_specializes p (W.pointPrime y)).mp hpmy
  obtain ⟨P', -, hP'⟩ := hflat.generalizingMap_comap hspec
  exact ⟨P', hP'⟩

/-- Under faithful flatness, point injectivity descends some characteristic
power of each polynomial function to the target. -/
public theorem Variety.Morphism.exists_frobenius_power_mem_range_of_injective_of_faithfullyFlat
    {V W : Variety k} [Nonempty (Variety.Point V)]
    (f : Variety.Morphism V W) (hf : Function.Injective f.toFun)
    (hff : letI : Algebra (Variety.PolynomialFunction W) (Variety.PolynomialFunction V) :=
      f.pullbackRingHom.toAlgebra
      Module.FaithfullyFlat (Variety.PolynomialFunction W) (Variety.PolynomialFunction V))
    (p : ℕ) [Fact p.Prime] [CharP k p] (b : Variety.PolynomialFunction V) :
    ∃ n : ℕ, b ^ (p ^ n) ∈ Set.range f.pullbackRingHom := by
  let C := Variety.PolynomialFunction W
  let A := Variety.PolynomialFunction V
  let F := f.pullbackRingHom
  letI : Algebra C A := F.toAlgebra
  letI : IsScalarTower k C A := IsScalarTower.of_algebraMap_eq' (by
    exact f.pullbackAlgHom.comp_algebraMap.symm)
  letI : Module.FaithfullyFlat C A := hff
  let T := A ⊗[C] A
  letI : Nontrivial A :=
    (polynomialFunctionPointAlgHom V (Classical.choice inferInstance)).toRingHom.domain_nontrivial
  letI : Nontrivial T := (Algebra.TensorProduct.lmul' C (S := A)).toRingHom.domain_nontrivial
  letI : CharP T p := charP_of_injective_algebraMap (algebraMap k T).injective p
  obtain ⟨n, hn⟩ := f.tensor_difference_isNilpotent_of_injective hf b
  have hn' : (b ⊗ₜ[C] 1 - 1 ⊗ₜ[C] b : T) ^ (p ^ n) = 0 :=
    pow_eq_zero_of_le (Nat.le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)) hn
  rw [sub_pow_char_pow, sub_eq_zero] at hn'
  have heq : (b ^ (p ^ n)) ⊗ₜ[C] (1 : A) = 1 ⊗ₜ[C] (b ^ (p ^ n)) := by
    change Algebra.TensorProduct.includeLeftRingHom (b ^ (p ^ n)) =
      Algebra.TensorProduct.includeRight (R := C) (b ^ (p ^ n))
    rw [map_pow, map_pow]
    exact hn'
  exact ⟨n, mem_range_algebraMap_of_tensor_eq (b ^ (p ^ n)) heq⟩

/-- Characteristic powers of coordinates descend through a flat bijective
affine morphism. The exponent is allowed to depend on the coordinate. -/
public theorem Variety.Morphism.exists_coordinate_frobenius_powers_of_bijective_of_flat
    {V W : Variety k} [Nonempty (Variety.Point V)]
    (f : Variety.Morphism V W) (hf : Function.Bijective f.toFun)
    (hflat : f.pullbackRingHom.Flat) (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∀ i : V.Coordinates, ∃ n : ℕ, ∃ q : MvPolynomial W.Coordinates k,
      ∀ x : Variety.Point V,
        x.val i ^ (p ^ n) = evalPolynomial (f.toFun x).val q := by
  intro i
  let b : Variety.PolynomialFunction V :=
    Variety.PolynomialFunction.ofPolynomial V (MvPolynomial.X i)
  obtain ⟨n, a, ha⟩ := f.exists_frobenius_power_mem_range_of_injective_of_faithfullyFlat hf.1
    (f.pullback_faithfullyFlat_of_surjective_of_flat hf.2 hflat) p b
  obtain ⟨q, hq⟩ := a.representedBy
  refine ⟨n, q, fun x => ?_⟩
  have hx := congrArg (fun g : Variety.PolynomialFunction V => g x) ha
  change a (f.toFun x) = (b ^ (p ^ n)) x at hx
  rw [hq] at hx
  have hbeval : b x = x.val i := by
    change evalPolynomial x.val (MvPolynomial.X i) = x.val i
    rw [evalPolynomial_X]
  calc
    x.val i ^ (p ^ n) = polynomialFunctionPointAlgHom V x (b ^ (p ^ n)) := by
      rw [map_pow, polynomialFunctionPointAlgHom_apply, hbeval]
    _ = evalPolynomial (f.toFun x).val q := hx.symm

/-- For a bijective group morphism, one nonzero flat localization suffices for
coordinate descent: translations spread flatness over the entire target. -/
public theorem Morphism.exists_coordinate_frobenius_powers_of_bijective_of_flat_localization
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hφ : Function.Bijective φ.onPoints)
    (hlocal : ∃ c : Variety.PolynomialFunction G, c ≠ 0 ∧
      RingHom.Flat (Localization.awayMap φ.toVariety.pullbackRingHom c))
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∀ i : H.Coordinates, ∃ n : ℕ, ∃ q : MvPolynomial G.Coordinates k,
      ∀ x : Variety.Point H,
        x.val i ^ (p ^ n) = evalPolynomial (φ.onPoints x).val q := by
  obtain ⟨c, hc, hflat⟩ := hlocal
  exact φ.toVariety.exists_coordinate_frobenius_powers_of_bijective_of_flat hφ
    (pullbackRingHom_flat_of_awayMap_flat φ hφ.2 c hc hflat) p

end Theory.AlgebraicGroup
