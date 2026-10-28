module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Theory.AlgebraicGroup.CoordinateRing.PolynomialFunction

universe u

/-! Evaluation homomorphisms and point ideals of affine varieties. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

@[expose]
public def polynomialFunctionPointAlgHom (V : Variety k)
    (x : Variety.Point V) : Variety.PolynomialFunction V →ₐ[k] k where
  toFun := fun f ↦ f x
  map_one' := by
    rw [← (algebraMap k (Variety.PolynomialFunction V)).map_one]
    exact polynomialFunction_algebraMap_apply V 1 x
  map_mul' := fun f g ↦ polynomialFunction_mul_apply V f g x
  map_zero' := polynomialFunction_zero_apply V x
  map_add' := fun _ _ ↦ rfl
  commutes' := fun r ↦ polynomialFunction_algebraMap_apply V r x

@[simp] public lemma polynomialFunctionPointAlgHom_apply (V : Variety k)
    (x : Variety.Point V) (f : Variety.PolynomialFunction V) :
    polynomialFunctionPointAlgHom V x f = f x := rfl

@[expose]
public noncomputable def coordinatePointAlgHom (V : Variety k)
    (x : Variety.Point V) : coordinateRing V →ₐ[k] k :=
  (polynomialFunctionPointAlgHom V x).comp
    (coordinateRingAlgEquivPolynomialFunction V).toAlgHom

@[simp] public lemma coordinatePointAlgHom_apply (V : Variety k)
    (x : Variety.Point V) (a : coordinateRing V) :
    coordinatePointAlgHom V x a =
      (coordinateRingAlgEquivPolynomialFunction V a) x := rfl

@[simp] lemma polynomialFunction_ofPolynomial_apply (V : Variety k)
    (x : Variety.Point V) (p : MvPolynomial V.Coordinates k) :
    (Variety.PolynomialFunction.ofPolynomial V p) x =
      evalPolynomial x.val p := rfl

public lemma coordinatePointAlgHom_surjective (V : Variety k)
    (x : Variety.Point V) : Function.Surjective (coordinatePointAlgHom V x) := by
  intro r
  refine ⟨algebraMap k (coordinateRing V) r, ?_⟩
  exact (coordinatePointAlgHom V x).commutes r

@[expose]
public noncomputable def Variety.pointPrime (V : Variety k) (x : Variety.Point V) :
    PrimeSpectrum (Variety.PolynomialFunction V) :=
  ⟨RingHom.ker (polynomialFunctionPointAlgHom V x),
    RingHom.ker_isPrime (f := (polynomialFunctionPointAlgHom V x).toRingHom)⟩

public lemma polynomialFunctionPointAlgHom_surjective (V : Variety k)
    (x : Variety.Point V) :
    Function.Surjective (polynomialFunctionPointAlgHom V x) := by
  intro r
  refine ⟨algebraMap k (Variety.PolynomialFunction V) r, ?_⟩
  exact (polynomialFunctionPointAlgHom V x).commutes r

public lemma Variety.pointPrime_isMaximal (V : Variety k) (x : Variety.Point V) :
    (V.pointPrime x).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (polynomialFunctionPointAlgHom_surjective V x)

public lemma Variety.pointPrime_injective (V : Variety k) :
    Function.Injective V.pointPrime := by
  intro x y hxy
  apply Variety.Point.ext
  funext i
  let Xi : Variety.PolynomialFunction V :=
    Variety.PolynomialFunction.ofPolynomial V (MvPolynomial.X i)
  have hxmem : Xi - algebraMap k (Variety.PolynomialFunction V) (x.val i) ∈
      (V.pointPrime x).asIdeal := by
    change polynomialFunctionPointAlgHom V x
      (Xi - algebraMap k (Variety.PolynomialFunction V) (x.val i)) = 0
    rw [map_sub, (polynomialFunctionPointAlgHom V x).commutes,
      polynomialFunctionPointAlgHom_apply]
    dsimp [Xi]
    simp [evalPolynomial]
  have hymem : Xi - algebraMap k (Variety.PolynomialFunction V) (x.val i) ∈
      (V.pointPrime y).asIdeal := by
    rw [← hxy]
    exact hxmem
  change polynomialFunctionPointAlgHom V y
      (Xi - algebraMap k (Variety.PolynomialFunction V) (x.val i)) = 0 at hymem
  rw [map_sub, (polynomialFunctionPointAlgHom V y).commutes,
    polynomialFunctionPointAlgHom_apply] at hymem
  dsimp [Xi] at hymem
  have hyx : y.val i - x.val i = 0 := by
    simpa [evalPolynomial] using hymem
  exact (sub_eq_zero.mp hyx).symm

public lemma evaluationRingHom_surjective (V : Variety k) :
    Function.Surjective (evaluationRingHom (V := V)) := by
  intro f
  rcases f.representedBy with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  change evalPolynomial x.val p = f x
  exact (hp x).symm

public def polynomialFunctionPresentationAlgHom (V : Variety k) :
    MvPolynomial V.Coordinates k →ₐ[k] Variety.PolynomialFunction V where
  toRingHom := evaluationRingHom (V := V)
  commutes' := by
    intro r
    apply Variety.PolynomialFunction.ext
    intro x
    change evalPolynomial x.val (MvPolynomial.C r) =
      (algebraMap k (Variety.PolynomialFunction V) r) x
    rw [polynomialFunction_algebraMap_apply]
    simp [evalPolynomial]

public lemma polynomialFunction_finiteType (V : Variety k) :
    Algebra.FiniteType k (Variety.PolynomialFunction V) := by
  let : Algebra.FiniteType k (MvPolynomial V.Coordinates k) := inferInstance
  exact Algebra.FiniteType.of_surjective
    (polynomialFunctionPresentationAlgHom V) (evaluationRingHom_surjective V)

lemma Variety.Morphism.pullbackRingHom_finiteType {V W : Variety k}
    (f : Variety.Morphism V W) : f.pullbackRingHom.FiniteType := by
  have hcomp : (f.pullbackRingHom.comp
      (algebraMap k (Variety.PolynomialFunction W))).FiniteType := by
    have htarget : (algebraMap k (Variety.PolynomialFunction V)).FiniteType :=
      RingHom.finiteType_algebraMap.mpr (polynomialFunction_finiteType V)
    convert htarget using 1
    apply RingHom.ext
    intro r
    change f.pullbackAlgHom (algebraMap k (Variety.PolynomialFunction W) r) =
      algebraMap k (Variety.PolynomialFunction V) r
    exact f.pullbackAlgHom.commutes r
  exact RingHom.FiniteType.of_comp_finiteType hcomp

public lemma Variety.Morphism.pullbackRingHom_finitePresentation {V W : Variety k}
    (f : Variety.Morphism V W) : f.pullbackRingHom.FinitePresentation := by
  let : Algebra.FiniteType k (Variety.PolynomialFunction W) :=
    polynomialFunction_finiteType W
  let : IsNoetherianRing (Variety.PolynomialFunction W) :=
    Algebra.FiniteType.isNoetherianRing k _
  exact RingHom.FinitePresentation.of_finiteType.mp f.pullbackRingHom_finiteType

public lemma Variety.Morphism.pointPrime_image {V W : Variety k}
    (f : Variety.Morphism V W) (x : Variety.Point V) :
    W.pointPrime (f.toFun x) =
      PrimeSpectrum.comap f.pullbackRingHom (V.pointPrime x) := by
  apply PrimeSpectrum.ext
  ext a
  change polynomialFunctionPointAlgHom W (f.toFun x) a = 0 ↔
      polynomialFunctionPointAlgHom V x (f.pullbackRingHom a) = 0
  rw [polynomialFunctionPointAlgHom_apply,
    polynomialFunctionPointAlgHom_apply,
    f.pullbackRingHom_apply]
  rfl

public lemma Variety.exists_pointPrime_eq_of_isMaximal (V : Variety k)
    [IsAlgClosed k] (m : Ideal (Variety.PolynomialFunction V)) (hm : m.IsMaximal) :
    ∃ x : Variety.Point V, V.pointPrime x = ⟨m, hm.isPrime⟩ := by
  let q : Ideal (MvPolynomial V.Coordinates k) :=
    m.comap (evaluationRingHom (V := V))
  let : m.IsMaximal := hm
  have hqmax : q.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (evaluationRingHom_surjective V)
  obtain ⟨z, hz⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal
    k hqmax
  have hzPoint : ∀ p ∈ V.equations, evalPolynomial z p = 0 := by
    intro p hp
    have hpzero : evaluationRingHom (V := V) p = 0 := by
      apply Variety.PolynomialFunction.ext
      intro x
      change evalPolynomial x.val p = 0
      exact x.isZero p hp
    have hpq : p ∈ q := by
      change evaluationRingHom (V := V) p ∈ m
      rw [hpzero]
      exact m.zero_mem
    rw [hz, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hpq
    exact hpq
  let x : Variety.Point V := ⟨z, hzPoint⟩
  refine ⟨x, PrimeSpectrum.ext ?_⟩
  apply Ideal.comap_injective_of_surjective
    (evaluationRingHom (V := V)) (evaluationRingHom_surjective V)
  change (V.pointPrime x).asIdeal.comap (evaluationRingHom (V := V)) = q
  rw [hz]
  ext p
  change polynomialFunctionPointAlgHom V x
      (evaluationRingHom (V := V) p) = 0 ↔
    p ∈ MvPolynomial.vanishingIdeal k ({z} : Set (V.Coordinates → k))
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
  rfl

/-- Every base-field character of a polynomial-function algebra is evaluation
at a unique point. -/
public theorem polynomialFunctionPointAlgHom_existsUnique
    [IsAlgClosed k] (V : Variety k)
    (φ : Variety.PolynomialFunction V →ₐ[k] k) :
    ∃! x : Variety.Point V, polynomialFunctionPointAlgHom V x = φ := by
  have hφsurj : Function.Surjective φ := by
    intro r
    exact ⟨algebraMap k (Variety.PolynomialFunction V) r, φ.commutes r⟩
  have hm : (RingHom.ker φ.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective φ hφsurj
  obtain ⟨x, hx⟩ := V.exists_pointPrime_eq_of_isMaximal
    (RingHom.ker φ.toRingHom) hm
  have hker : RingHom.ker (polynomialFunctionPointAlgHom V x).toRingHom =
      RingHom.ker φ.toRingHom :=
    congrArg PrimeSpectrum.asIdeal hx
  refine ⟨x, ?_, ?_⟩
  · apply AlgHom.ext
    intro a
    let r := φ a
    have ha : a - algebraMap k (Variety.PolynomialFunction V) r ∈
        RingHom.ker φ.toRingHom := by
      change φ (a - algebraMap k (Variety.PolynomialFunction V) r) = 0
      rw [map_sub, φ.commutes]
      exact sub_self r
    rw [← hker] at ha
    change polynomialFunctionPointAlgHom V x
        (a - algebraMap k (Variety.PolynomialFunction V) r) = 0 at ha
    rw [map_sub, (polynomialFunctionPointAlgHom V x).commutes] at ha
    exact (sub_eq_zero.mp ha).trans rfl
  · intro y hy
    apply V.pointPrime_injective
    apply PrimeSpectrum.ext
    change RingHom.ker (polynomialFunctionPointAlgHom V y).toRingHom =
      RingHom.ker (polynomialFunctionPointAlgHom V x).toRingHom
    rw [hy, hker]

/-- Points of an affine variety are its base-field-valued characters. -/
@[expose]
public noncomputable def polynomialFunctionPointAlgHomEquiv
    [IsAlgClosed k] (V : Variety k) :
    Variety.Point V ≃ (Variety.PolynomialFunction V →ₐ[k] k) where
  toFun := polynomialFunctionPointAlgHom V
  invFun := fun φ => Classical.choose (polynomialFunctionPointAlgHom_existsUnique V φ)
  left_inv := by
    intro x
    exact (Classical.choose_spec
      (polynomialFunctionPointAlgHom_existsUnique V
        (polynomialFunctionPointAlgHom V x))).2 x rfl |>.symm
  right_inv := by
    intro φ
    exact (Classical.choose_spec (polynomialFunctionPointAlgHom_existsUnique V φ)).1

public lemma Variety.continuous_pointPrime (V : Variety k) : Continuous V.pointPrime := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
  rw [Variety.isClosed_iff_isZariskiClosed]
  let E : Set (MvPolynomial V.Coordinates k) :=
    {p | evaluationRingHom (V := V) p ∈ I}
  refine ⟨E, ?_⟩
  ext x
  rw [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus]
  change I ≤ (V.pointPrime x).asIdeal ↔
    ∀ p ∈ E, evalPolynomial x.val p = 0
  constructor
  · intro h p hp
    have := h hp
    change polynomialFunctionPointAlgHom V x
      (evaluationRingHom (V := V) p) = 0 at this
    exact this
  · intro h a ha
    obtain ⟨p, rfl⟩ := evaluationRingHom_surjective V a
    change polynomialFunctionPointAlgHom V x
      (evaluationRingHom (V := V) p) = 0
    exact h p ha

end Theory.AlgebraicGroup
