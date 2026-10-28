module

public import Mathlib.RepresentationTheory.Invariants
public import Theory.AlgebraicGroup.Dimension.Fiber
public import Theory.AlgebraicGroup.Instance.Additive
public import Theory.AlgebraicGroup.Jordan.Morphism
public import Theory.AlgebraicGroup.Morphism.FiniteKernel
public import Theory.AlgebraicGroup.Representations.Unipotent.Basic
public import Theory.AlgebraicGroup.RightTranslation.Representation
public import Theory.AlgebraicGroup.Variety.AffineSpace

universe u

/-!
Core definitions and proved lemmas for one-parameter algebraic groups from GLS
Number 3, Part I, Chapter A, section 1.3.

The coordinate points `kPlusPoint t` expose the additive point law and recover
every point from its affine coordinate.  These equations let concrete
one-parameter morphisms use the public `KPlus` interface without unfolding the
transported algebraic-group instance.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- GLS Definition 1.3.3: the additive one-dimensional algebraic group. -/
public abbrev KPlus (k : Type u) [Field k] := additiveGroupVariety k

/-- Scalar multiplication on the additive algebraic group. -/
@[expose]
public def additiveScalarMorphism (c : k) :
    AlgebraicGroup.Morphism (KPlus k) (KPlus k) where
  toVariety :=
    { toFun := fun x ↦
        (additiveGroupPointEquiv k).symm
          (Multiplicative.ofAdd (c * Multiplicative.toAdd
            (additiveGroupPointEquiv k x)))
      regular := by
        intro i
        refine ⟨MvPolynomial.C c * MvPolynomial.X PUnit.unit, ?_⟩
        intro x
        simp [evalPolynomial, additiveGroupPointEquiv]
        rfl }
  map_one := by
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd (c * 0) = Multiplicative.ofAdd 0
    simp
  map_mul := by
    intro x y
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd
        (c * (Multiplicative.toAdd (additiveGroupPointEquiv k x) +
          Multiplicative.toAdd (additiveGroupPointEquiv k y))) =
      Multiplicative.ofAdd (c * Multiplicative.toAdd (additiveGroupPointEquiv k x)) *
        Multiplicative.ofAdd (c * Multiplicative.toAdd (additiveGroupPointEquiv k y))
    simp [mul_add]

/-- For nonzero `c`, scalar multiplication by `c` is an algebraic-group
automorphism of `KPlus k`. -/
@[expose]
public def additiveScalarIso (c : k) (hc : c ≠ 0) :
    AlgebraicGroup.Iso (KPlus k) (KPlus k) where
  hom := additiveScalarMorphism c
  inv := additiveScalarMorphism c⁻¹
  hom_inv_id := by
    intro x
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd (c⁻¹ * (c *
      Multiplicative.toAdd (additiveGroupPointEquiv k x))) =
      additiveGroupPointEquiv k x
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    exact Multiplicative.ofAdd.apply_symm_apply (additiveGroupPointEquiv k x)
  inv_hom_id := by
    intro x
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd (c * (c⁻¹ *
      Multiplicative.toAdd (additiveGroupPointEquiv k x))) =
      additiveGroupPointEquiv k x
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    exact Multiplicative.ofAdd.apply_symm_apply (additiveGroupPointEquiv k x)

/-- GLS Definition 1.3.4: a parametrization of `X` is an algebraic-group
isomorphism from the additive group. -/
public abbrev OneParameterParametrization
    (X : Variety k) [AlgebraicGroup X] :=
  AlgebraicGroup.Iso (KPlus k) X

/-- GLS Definition 1.3.4: an algebraic group is one-parameter when it admits a
parametrization by `KPlus k`. -/
@[expose]
public def IsOneParameterGroup (X : Variety k) [AlgebraicGroup X] : Prop :=
  Nonempty (OneParameterParametrization X)

/-- The point of `KPlus k` with affine coordinate `t`. -/
@[expose]
public def kPlusPoint (t : k) : Variety.Point (KPlus k) :=
  (additiveGroupPointEquiv k).symm (Multiplicative.ofAdd t)

/-- The value `x(t)` of a one-parameter-group parametrization. -/
@[expose]
public noncomputable def OneParameterParametrization.value
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) (t : k) : Variety.Point X :=
  x.hom.onPoints (kPlusPoint t)

/-- Rescale a parametrization by the scalar automorphism `t ↦ c t`. -/
@[expose]
public noncomputable def OneParameterParametrization.rescale
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) (c : k) (hc : c ≠ 0) :
    OneParameterParametrization X :=
  x.comp (additiveScalarIso c hc)

/-- The affine line underlying `KPlus k` has zero vanishing ideal on its full
point space. -/
public lemma kPlus_vanishingIdeal_eq_bot [IsAlgClosed k] :
    vanishingIdeal (Set.univ : Set (Variety.Point (KPlus k))) = ⊥ :=
  affineSpaceVariety_vanishingIdeal_eq_bot

/-- The affine additive group is connected. -/
public lemma kPlus_isConnected [IsAlgClosed k] :
    Variety.IsConnected (KPlus k) :=
  affineSpaceVariety_isConnected

/-- The affine additive group has geometric dimension one. -/
public lemma kPlus_dimension_eq_one [IsAlgClosed k] :
    Variety.dimension (KPlus k) = 1 := by
  let : IsDomain (coordinateRing (KPlus k)) :=
    (Ideal.Quotient.isDomain_iff_prime
      (I := vanishingIdeal (Set.univ : Set (Variety.Point (KPlus k))))).mpr (by
        rw [kPlus_vanishingIdeal_eq_bot]
        exact Ideal.isPrime_bot)
  have hirreducible := connectedAlgebraicGroup_irreducible
    (KPlus k) (kPlus_isConnected (k := k))
  rw [dimension_eq_fractionRing_of_isIrreducible (KPlus k) hirreducible,
    trdeg_fractionRing_eq]
  change Algebra.trdeg k (MvPolynomial PUnit k ⧸
    vanishingIdeal (Set.univ : Set (Variety.Point (KPlus k)))) = 1
  rw [kPlus_vanishingIdeal_eq_bot]
  calc
    Algebra.trdeg k (MvPolynomial PUnit k ⧸
        (⊥ : Ideal (MvPolynomial PUnit k))) =
        Algebra.trdeg k (MvPolynomial PUnit k) :=
      (AlgEquiv.quotientBot k (MvPolynomial PUnit k)).trdeg_eq
    _ = 1 := by
      rw [MvPolynomial.trdeg_of_isDomain]
      simp

private noncomputable def polynomialFiniteDifference (a : k) :
    Polynomial k →ₗ[k] Polynomial k :=
  Polynomial.taylor a - LinearMap.id

private lemma polynomialFiniteDifference_degree_lt
    (a : k) {p : Polynomial k} (hp : p ≠ 0)
    (hdiff : polynomialFiniteDifference a p ≠ 0) :
    (polynomialFiniteDifference a p).natDegree < p.natDegree := by
  rw [Polynomial.natDegree_lt_iff_degree_lt hdiff]
  have h := Polynomial.degree_sub_lt_left
    (Polynomial.degree_taylor p a)
    ((Polynomial.taylor_eq_zero a p).not.mpr hp)
    (Polynomial.leadingCoeff_taylor a p)
  simpa [polynomialFiniteDifference, Polynomial.degree_eq_natDegree hp] using h

private lemma polynomialFiniteDifference_iterate_eq_zero
    (a : k) {p : Polynomial k} {x : ℕ} (hx : p.natDegree < x) :
    (polynomialFiniteDifference a)^[x] p = 0 := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p x with
  | _ _ ih =>
      subst h
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (pos_of_gt hx).ne'
      rw [Function.iterate_succ_apply]
      by_cases hp : p = 0
      · simp [hp]
      by_cases hdiff : polynomialFiniteDifference a p = 0
      · simp [hdiff]
      have hdegree := polynomialFiniteDifference_degree_lt a hp hdiff
      exact ih _ hdegree (hdegree.trans_le (Nat.le_of_lt_succ hx)) rfl

public lemma kPlusPoint_mul (s t : k) :
    kPlusPoint s * kPlusPoint t = kPlusPoint (s + t) := by
  apply (additiveGroupPointEquiv k).injective
  change Multiplicative.ofAdd (s + t) =
    Multiplicative.ofAdd s * Multiplicative.ofAdd t
  rfl

public lemma kPlusPoint_coordinate (x : Variety.Point (KPlus k)) :
    kPlusPoint (Multiplicative.toAdd (additiveGroupPointEquiv k x)) = x := by
  apply (additiveGroupPointEquiv k).injective
  change Multiplicative.ofAdd
      (Multiplicative.toAdd (additiveGroupPointEquiv k x)) =
    additiveGroupPointEquiv k x
  exact Multiplicative.ofAdd.apply_symm_apply _

/-- Multiplication of additive-group points adds their affine coordinates. -/
public lemma kPlusPoint_coordinate_mul (x y : Variety.Point (KPlus k)) :
    (x * y).val PUnit.unit = x.val PUnit.unit + y.val PUnit.unit := by
  rw [← kPlusPoint_coordinate x, ← kPlusPoint_coordinate y,
    kPlusPoint_mul]
  rfl

/-- Every point of the affine additive group is a unipotent element. -/
public theorem kPlus_isUnipotentAlgebraicGroup :
    IsUnipotentAlgebraicGroup (KPlus k) := by
  intro g
  simp only [IsUnipotentElement]
  intro f
  rcases f.representedBy with ⟨p, hp⟩
  let a : k := Multiplicative.toAdd (additiveGroupPointEquiv k g)
  let P : Polynomial k := MvPolynomial.uniqueAlgEquiv k PUnit p
  have hg : g = kPlusPoint a := (kPlusPoint_coordinate g).symm
  let T : Variety.PolynomialFunction (KPlus k) →ₗ[k]
      Variety.PolynomialFunction (KPlus k) :=
    rightTranslationPullback (KPlus k) g - 1
  let D : Polynomial k →ₗ[k] Polynomial k := polynomialFiniteDifference a
  have hT_apply (q : Variety.PolynomialFunction (KPlus k)) :
      T q = rightTranslationPullback (KPlus k) g q - q := by
    rfl
  have hD_apply (q : Polynomial k) :
      D q = Polynomial.taylor a q - q := by
    rfl
  have hiterate : ∀ n : ℕ, ∀ t : k,
      (T^[n]) f (kPlusPoint t) = ((D^[n]) P).eval t := by
    intro n
    induction n with
    | zero =>
        intro t
        change f (kPlusPoint t) = P.eval t
        rw [hp]
        change MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ t) p = P.eval t
        rw [← MvPolynomial.eval₂_const_uniqueAlgEquiv]
        rfl
    | succ n ih =>
        intro t
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hT_apply, hD_apply]
        change
          (rightTranslationPullback (KPlus k) g ((T^[n]) f))
                (kPlusPoint t) -
              (T^[n]) f (kPlusPoint t) =
            (Polynomial.taylor a ((D^[n]) P) - (D^[n]) P).eval t
        rw [rightTranslationPullback_apply, hg, kPlusPoint_mul,
          ih (t + a), ih t, Polynomial.eval_sub, Polynomial.taylor_eval]
  refine ⟨P.natDegree + 1, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  let t : k := Multiplicative.toAdd (additiveGroupPointEquiv k x)
  rw [← kPlusPoint_coordinate x, hiterate]
  change ((polynomialFiniteDifference a)^[P.natDegree + 1] P).eval t = 0
  rw [polynomialFiniteDifference_iterate_eq_zero a (Nat.lt_succ_self _)]
  simp

/-- GLS Proposition 1.3.5(b): every automorphism of `KPlus k` is uniquely
scalar multiplication by a nonzero field element. -/
public theorem kPlus_automorphism_eq_scalar [IsAlgClosed k]
    (e : AlgebraicGroup.Iso (KPlus k) (KPlus k)) :
    ∃! c : k, c ≠ 0 ∧ ∀ t : k,
      e.hom.onPoints (kPlusPoint t) = kPlusPoint (c * t) := by
  rcases e.hom.toVariety.regular PUnit.unit with ⟨p, hp⟩
  rcases e.inv.toVariety.regular PUnit.unit with ⟨q, hq⟩
  let P : Polynomial k := MvPolynomial.uniqueAlgEquiv k PUnit p
  let Q : Polynomial k := MvPolynomial.uniqueAlgEquiv k PUnit q
  have hP : ∀ t : k,
      (e.hom.onPoints (kPlusPoint t)).val PUnit.unit = P.eval t := by
    intro t
    change (e.hom.toVariety.toFun (kPlusPoint t)).val PUnit.unit = P.eval t
    rw [hp]
    change MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ t) p = P.eval t
    rw [← MvPolynomial.eval₂_const_uniqueAlgEquiv]
    rfl
  have hQ : ∀ t : k,
      (e.inv.onPoints (kPlusPoint t)).val PUnit.unit = Q.eval t := by
    intro t
    change (e.inv.toVariety.toFun (kPlusPoint t)).val PUnit.unit = Q.eval t
    rw [hq]
    change MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ t) q = Q.eval t
    rw [← MvPolynomial.eval₂_const_uniqueAlgEquiv]
    rfl
  have hhom_point : ∀ t : k,
      e.hom.onPoints (kPlusPoint t) = kPlusPoint (P.eval t) := by
    intro t
    apply Variety.Point.ext
    funext i
    exact hP t
  have hinv_point : ∀ t : k,
      e.inv.onPoints (kPlusPoint t) = kPlusPoint (Q.eval t) := by
    intro t
    apply Variety.Point.ext
    funext i
    exact hQ t
  have hcomp_eval : ∀ t : k, Q.eval (P.eval t) = t := by
    intro t
    have h := e.hom_inv_id (kPlusPoint t)
    rw [hhom_point t, hinv_point (P.eval t)] at h
    exact congrArg (fun z : Variety.Point (KPlus k) ↦ z.val PUnit.unit) h
  have hcomp : Q.comp P = Polynomial.X := by
    apply Polynomial.eq_of_infinite_eval_eq
    exact Set.infinite_univ.mono (by
      intro t _
      simpa [Polynomial.eval_comp] using hcomp_eval t)
  have hdegrees : Q.natDegree = 1 ∧ P.natDegree = 1 := by
    have hdegree : Q.natDegree * P.natDegree = 1 := by
      rw [← Polynomial.natDegree_comp, hcomp, Polynomial.natDegree_X]
    constructor
    · exact Nat.dvd_one.mp ⟨P.natDegree, hdegree.symm⟩
    · exact Nat.dvd_one.mp
        ⟨Q.natDegree, by simpa [mul_comm] using hdegree.symm⟩
  rcases Polynomial.natDegree_eq_one.mp hdegrees.2 with ⟨c, hc, b, hPshape⟩
  have hPzero : P.eval 0 = 0 := by
    calc
      P.eval 0 = (e.hom.onPoints (kPlusPoint 0)).val PUnit.unit := (hP 0).symm
      _ = (e.hom.onPoints 1).val PUnit.unit := by rfl
      _ = (1 : Variety.Point (KPlus k)).val PUnit.unit :=
        congrArg (fun z : Variety.Point (KPlus k) ↦ z.val PUnit.unit) e.hom.map_one
      _ = 0 := by rfl
  have hb : b = 0 := by
    have h := congrArg (Polynomial.eval 0) hPshape
    simpa [hPzero] using h
  have hPlinear : P = Polynomial.C c * Polynomial.X := by
    rw [← hPshape, hb]
    simp
  have hcformula : ∀ t : k,
      e.hom.onPoints (kPlusPoint t) = kPlusPoint (c * t) := by
    intro t
    rw [hhom_point, hPlinear]
    simp
  refine ⟨c, ⟨hc, hcformula⟩, ?_⟩
  intro d hd
  have hct := congrArg
    (fun z : Variety.Point (KPlus k) ↦ z.val PUnit.unit)
    ((hd.2 1).symm.trans (hcformula 1))
  simp [kPlusPoint, additiveGroupPointEquiv] at hct
  exact Multiplicative.ofAdd.injective hct

/-- GLS Proposition 1.3.5(a), forward direction: rescaling a parametrization
by a nonzero scalar evaluates as `x(c t)`. -/
public lemma oneParameterParametrization_rescale_apply
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) (c : k) (hc : c ≠ 0) (t : k) :
    (x.rescale c hc).value t = x.value (c * t) := by
  rfl

/-- GLS Proposition 1.3.5(a), classification direction: relative to a fixed
parametrization, every parametrization is uniquely a nonzero scalar rescaling. -/
public theorem oneParameterParametrization_eq_rescale [IsAlgClosed k]
    {X : Variety k} [AlgebraicGroup X]
    (x y : OneParameterParametrization X) :
    ∃! c : k, c ≠ 0 ∧ ∀ t : k, y.value t = x.value (c * t) := by
  let e : AlgebraicGroup.Iso (KPlus k) (KPlus k) := x.symm.comp y
  rcases kPlus_automorphism_eq_scalar e with ⟨c, hc, hunique⟩
  have hcformula : ∀ t : k, y.value t = x.value (c * t) := by
    intro t
    have h := congrArg x.hom.onPoints (hc.2 t)
    change y.hom.onPoints (kPlusPoint t) =
      x.hom.onPoints (kPlusPoint (c * t))
    change x.hom.onPoints
      (x.inv.onPoints (y.hom.onPoints (kPlusPoint t))) =
        x.hom.onPoints (kPlusPoint (c * t)) at h
    rw [x.inv_hom_id] at h
    exact h
  refine ⟨c, ⟨hc.1, hcformula⟩, ?_⟩
  intro d hd
  apply hunique d
  refine ⟨hd.1, ?_⟩
  intro t
  have h := congrArg x.inv.onPoints (hd.2 t)
  change (x.symm.comp y).hom.onPoints (kPlusPoint t) = kPlusPoint (d * t)
  change x.inv.onPoints (y.hom.onPoints (kPlusPoint t)) =
    x.inv.onPoints (x.hom.onPoints (kPlusPoint (d * t))) at h
  rw [x.hom_inv_id] at h
  exact h

/-- GLS Proposition 1.3.5(c): a one-parameter algebraic group is connected. -/
public lemma IsOneParameterGroup.isConnected [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y] (hY : IsOneParameterGroup Y) :
    Variety.IsConnected Y := by
  obtain ⟨x⟩ := hY
  exact (algebraicGroupIso_isConnected_iff x).mp (kPlus_isConnected (k := k))

/-- GLS Proposition 1.3.5(c): a one-parameter algebraic group has dimension
one. -/
public lemma IsOneParameterGroup.dimension_eq_one [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y] (hY : IsOneParameterGroup Y) :
    Variety.dimension Y = 1 := by
  obtain ⟨x⟩ := hY
  rw [← kPlus_dimension_eq_one (k := k)]
  exact (algebraicGroupIso_dimension_eq x).symm

/-- GLS Proposition 1.3.5(c): a one-parameter algebraic group is unipotent. -/
public theorem IsOneParameterGroup.isUnipotentAlgebraicGroup [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y] (hY : IsOneParameterGroup Y) :
    IsUnipotentAlgebraicGroup Y := by
  obtain ⟨x⟩ := hY
  intro y
  let g := x.inv.onPoints y
  have h := morphism_preserves_unipotentElement x.hom g
    (kPlus_isUnipotentAlgebraicGroup g)
  rw [x.inv_hom_id y] at h
  exact h

/-- A one-dimensional unipotent algebraic group has a nontrivial
algebraic-group morphism to the additive group. -/
public theorem exists_nontrivial_morphism_toKPlus_of_dimension_eq_one
    [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y]
    (hdimension : Variety.dimension Y = 1)
    (hunipotent : IsUnipotentAlgebraicGroup Y) :
    ∃ f : AlgebraicGroup.Morphism Y (KPlus k), ∃ y, f.onPoints y ≠ 1 := by
  let V := coordinateTranslationSubmodule Y
  let ρ : Representation k (Variety.Point Y) V :=
    (Units.coeHom _).comp (coordinateTranslationRepresentation Y)
  let : Module.Finite k V := coordinateTranslationSubmodule_finite Y
  let W : Submodule k V := ρ.invariants
  have hρunipotent : ∀ g : Variety.Point Y, IsNilpotent (ρ g - 1) := by
    intro g
    refine ⟨Module.finrank k V, ?_⟩
    exact coordinateTranslationRepresentation_sub_one_pow_finrank_eq_zero
      hunipotent g
  have hWmap : ∀ g : Variety.Point Y, W ≤ W.comap (ρ g) := by
    intro g w hw
    change ρ g w ∈ W
    have hwg : ρ g w = w := hw g
    rw [hwg]
    exact hw
  have hWne : W ≠ ⊤ := by
    intro hWtop
    have existsPointNeOne : ∃ g : Variety.Point Y, g ≠ 1 := by
      by_contra h
      push Not at h
      have : Subsingleton (Variety.Point Y) :=
        ⟨fun x y ↦ (h x).trans (h y).symm⟩
      have : Finite (Variety.Point Y) := Finite.of_subsingleton
      have hzero : Variety.dimension Y = 0 :=
        (dimension_zero_iff_finite_points Y).2 inferInstance
      exact zero_ne_one (hzero.symm.trans hdimension)
    obtain ⟨g, hg⟩ := existsPointNeOne
    apply hg
    apply coordinateTranslationRepresentation_injective Y
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hv : v ∈ W := by rw [hWtop]; trivial
    exact (show ρ g v = ρ 1 v by simpa using hv g)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, v₀ ∉ W :=
    SetLike.exists_not_mem_of_ne_top W hWne rfl
  let qρ := ρ.quotient W hWmap
  have : Nontrivial (V ⧸ W) := by
    refine ⟨⟨Submodule.Quotient.mk v₀, 0, ?_⟩⟩
    exact (not_congr (Submodule.Quotient.mk_eq_zero W)).mpr hv₀
  have hqρunipotent : ∀ g : Variety.Point Y, IsNilpotent (qρ g - 1) :=
    Representation.isNilpotent_quotient_sub_one ρ W hWmap hρunipotent
  obtain ⟨qv, hqvne, hqvfixed⟩ :=
    unipotentRepresentation_exists_common_fixed_ne_zero qρ hqρunipotent
  obtain ⟨v, hv⟩ := W.mkQ_surjective qv
  have hdeltaW (g : Variety.Point Y) : ρ g v - v ∈ W := by
    rw [← Submodule.Quotient.eq W]
    have hfix := hqvfixed g
    rw [← hv] at hfix
    simpa [qρ, Representation.quotient] using hfix
  have hdeltaExists : ∃ g : Variety.Point Y, ρ g v - v ≠ 0 := by
    by_contra h
    push Not at h
    have hvW : v ∈ W := by
      intro g
      exact sub_eq_zero.mp (h g)
    apply hqvne
    rw [← hv]
    exact (Submodule.Quotient.mk_eq_zero W).mpr hvW
  obtain ⟨g₀, hg₀⟩ := hdeltaExists
  obtain ⟨K, hK⟩ := Module.Projective.exists_dual_ne_zero k hg₀
  let e := coordinateTranslationBasis Y
  let generalMatrixCoefficient
      (L : Module.Dual k (coordinateTranslationSubmodule Y))
      (w : coordinateTranslationSubmodule Y) :
      Variety.PolynomialFunction Y :=
    ∑ j, e.repr w j •
      ∑ i, L (e i) • coordinateTranslationMatrixCoefficient Y e i j
  have generalMatrixCoefficient_apply
      (L : Module.Dual k (coordinateTranslationSubmodule Y))
      (w : coordinateTranslationSubmodule Y) (g : Variety.Point Y) :
      generalMatrixCoefficient L w g =
        L (rightTranslationOnCoordinateSubmodule Y g w) := by
    have hL (z : coordinateTranslationSubmodule Y) :
        ∑ i, L (e i) * e.repr z i = L z := by
      calc
        ∑ i, L (e i) * e.repr z i =
            ∑ i, e.repr z i * L (e i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [mul_comm]
        _ = L (∑ i, e.repr z i • e i) := by
              rw [map_sum]
              simp [smul_eq_mul]
        _ = L z := by rw [e.sum_repr]
    have hsum (j) :
        (∑ i, L (e i) • coordinateTranslationMatrixCoefficient Y e i j) g =
          ∑ i, L (e i) * coordinateTranslationMatrixCoefficient Y e i j g := by
      change polynomialFunctionEvalAddHom Y g
        (∑ i, L (e i) • coordinateTranslationMatrixCoefficient Y e i j) = _
      rw [map_sum]
      simp [polynomialFunction_smul_apply]
    change polynomialFunctionEvalAddHom Y g
      (∑ j, e.repr w j •
        ∑ i, L (e i) • coordinateTranslationMatrixCoefficient Y e i j) = _
    rw [map_sum]
    simp_rw [polynomialFunctionEvalAddHom_apply,
      polynomialFunction_smul_apply, hsum]
    simp_rw [coordinateTranslationMatrixCoefficient_apply, hL]
    calc
      ∑ j, e.repr w j *
          L (rightTranslationOnCoordinateSubmodule Y g (e j)) =
          L (∑ j, e.repr w j •
            rightTranslationOnCoordinateSubmodule Y g (e j)) := by
              rw [map_sum]
              simp [smul_eq_mul]
      _ = L (rightTranslationOnCoordinateSubmodule Y g
          (∑ j, e.repr w j • e j)) := by
            congr 1
            rw [map_sum]
            simp
      _ = L (rightTranslationOnCoordinateSubmodule Y g w) := by
            rw [e.sum_repr]
  let F : Variety.PolynomialFunction Y :=
    generalMatrixCoefficient K v - (K v) • 1
  have hF (g : Variety.Point Y) : F g = K (ρ g v - v) := by
    change polynomialFunctionEvalAddHom Y g
      (generalMatrixCoefficient K v - (K v) • 1) = _
    rw [map_sub]
    simp only [polynomialFunctionEvalAddHom_apply, polynomialFunction_smul_apply,
      generalMatrixCoefficient_apply, map_sub]
    change K (rightTranslationOnCoordinateSubmodule Y g v) - K v * 1 =
      K (rightTranslationOnCoordinateSubmodule Y g v) - K v
    rw [mul_one]
  have hFmul (g h : Variety.Point Y) : F (g * h) = F g + F h := by
    rw [hF, hF, hF]
    have hdh : ρ h v - v ∈ W := hdeltaW h
    have hfix : ρ g (ρ h v - v) = ρ h v - v := hdh g
    have hdelta : ρ (g * h) v - v =
        (ρ g v - v) + (ρ h v - v) := by
      rw [map_mul, Module.End.mul_apply]
      calc
        ρ g (ρ h v) - v = ρ g ((ρ h v - v) + v) - v := by
          congr 2
          abel
        _ = ρ g (ρ h v - v) + ρ g v - v := by rw [map_add]
        _ = (ρ g v - v) + (ρ h v - v) := by rw [hfix]; abel
    rw [hdelta, map_add]
  have hFone : F (1 : Variety.Point Y) = 0 := by
    rw [hF]
    simp
  let f : AlgebraicGroup.Morphism Y (KPlus k) :=
    { toVariety :=
        { toFun := fun y ↦ kPlusPoint (F y)
          regular := by
            intro i
            obtain ⟨p, hp⟩ := F.representedBy
            refine ⟨p, ?_⟩
            intro y
            rw [show i = PUnit.unit by rfl]
            change F y = evalPolynomial y.val p
            exact hp y }
      map_one := by
        apply Variety.Point.ext
        funext i
        rw [show i = PUnit.unit by rfl]
        change F 1 = 0
        exact hFone
      map_mul := by
        intro g h
        apply Variety.Point.ext
        funext i
        rw [show i = PUnit.unit by rfl]
        change F (g * h) = F g + F h
        exact hFmul g h }
  refine ⟨f, g₀, ?_⟩
  intro heq
  have hcoord := congrArg
    (fun z : Variety.Point (KPlus k) ↦ z.val PUnit.unit) heq
  change F g₀ = 0 at hcoord
  rw [hF] at hcoord
  exact hK hcoord

/-- A nontrivial morphism from a connected one-dimensional algebraic group to
`KPlus` has zero-dimensional kernel. -/
public lemma Morphism.kernel_dimension_eq_zero_of_nontrivial_toKPlus
    [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y]
    (f : AlgebraicGroup.Morphism Y (KPlus k))
    (hconnected : Variety.IsConnected Y)
    (hdimension : Variety.dimension Y = 1)
    (hnontrivial : ∃ y, f.onPoints y ≠ 1) :
    Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 := by
  have hkernel_ne_one :
      Variety.dimension f.kernelClosedSubgroup.carrierVariety ≠ 1 := by
    intro hkernel
    have hkernel_dimension :
        Variety.dimension f.kernelClosedSubgroup.carrierVariety =
          Variety.dimension Y :=
      hkernel.trans hdimension.symm
    have hcontains :=
      (closedSubgroup_dimension_eq_iff_contains_identityComponent
        Y f.kernelClosedSubgroup).mp hkernel_dimension
    have hidentity : AlgebraicGroup.identityComponent Y = Set.univ :=
      (identityComponent_eq_univ_iff_isConnected Y).mpr hconnected
    obtain ⟨y, hy⟩ := hnontrivial
    apply hy
    have hymem : y ∈ f.kernelClosedSubgroup.toSubgroup := by
      apply hcontains
      rw [hidentity]
      trivial
    exact hymem
  have hkernel_le_one :
      Variety.dimension f.kernelClosedSubgroup.carrierVariety ≤ 1 := by
    rw [← hdimension]
    exact closedSubvariety_dimension_le Y f.kernelClosedSubgroup.isZariskiClosed
  exact Cardinal.lt_one_iff.mp
    (lt_of_le_of_ne hkernel_le_one hkernel_ne_one)

/-- A nontrivial morphism from a connected one-dimensional algebraic group to
`KPlus` is surjective. -/
public lemma Morphism.surjective_of_nontrivial_toKPlus [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y]
    (f : AlgebraicGroup.Morphism Y (KPlus k))
    (hconnected : Variety.IsConnected Y)
    (hdimension : Variety.dimension Y = 1)
    (hnontrivial : ∃ y, f.onPoints y ≠ 1) :
    Function.Surjective f.onPoints := by
  have hkernel_zero :=
    f.kernel_dimension_eq_zero_of_nontrivial_toKPlus
      hconnected hdimension hnontrivial
  have himage_dimension :
      Variety.dimension f.imageClosedSubgroup.carrierVariety = 1 := by
    have hdimension_formula := morphism_dimension_eq_kernel_add_image f
    rw [hkernel_zero, zero_add, hdimension] at hdimension_formula
    exact hdimension_formula.symm
  have himage_ambient_dimension :
      Variety.dimension f.imageClosedSubgroup.carrierVariety =
        Variety.dimension (KPlus k) := by
    rw [himage_dimension, kPlus_dimension_eq_one]
  have hcontains :=
    (closedSubgroup_dimension_eq_iff_contains_identityComponent
      (KPlus k) f.imageClosedSubgroup).mp himage_ambient_dimension
  have hidentity : AlgebraicGroup.identityComponent (KPlus k) = Set.univ :=
    (identityComponent_eq_univ_iff_isConnected (KPlus k)).mpr kPlus_isConnected
  intro z
  have hz : z ∈ f.imageClosedSubgroup.toSubgroup := by
    apply hcontains
    rw [hidentity]
    trivial
  change z ∈ f.image at hz
  exact hz

/-- A connected one-dimensional unipotent algebraic group admits a surjective
additive character with zero-dimensional kernel. -/
public theorem exists_surjective_morphism_toKPlus_kernelDimension_eq_zero
    [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y]
    (hconnected : Variety.IsConnected Y)
    (hdimension : Variety.dimension Y = 1)
    (hunipotent : IsUnipotentAlgebraicGroup Y) :
    ∃ f : AlgebraicGroup.Morphism Y (KPlus k),
      Function.Surjective f.onPoints ∧
        Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 := by
  obtain ⟨f, hnontrivial⟩ :=
    exists_nontrivial_morphism_toKPlus_of_dimension_eq_one hdimension hunipotent
  exact ⟨f,
    f.surjective_of_nontrivial_toKPlus hconnected hdimension hnontrivial,
    f.kernel_dimension_eq_zero_of_nontrivial_toKPlus
      hconnected hdimension hnontrivial⟩

/-- A connected one-dimensional unipotent algebraic group admits a surjective
additive character with finite point kernel. -/
public theorem exists_surjective_morphism_toKPlus_finiteKernel [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y]
    (hconnected : Variety.IsConnected Y)
    (hdimension : Variety.dimension Y = 1)
    (hunipotent : IsUnipotentAlgebraicGroup Y) :
    ∃ f : AlgebraicGroup.Morphism Y (KPlus k),
      Function.Surjective f.onPoints ∧ Finite f.kernel := by
  obtain ⟨f, hsurjective, hkernel⟩ :=
    exists_surjective_morphism_toKPlus_kernelDimension_eq_zero
      hconnected hdimension hunipotent
  exact ⟨f, hsurjective,
    f.kernel_finite_of_kernelClosedSubgroup_dimension_eq_zero hkernel⟩

/-- A connected one-dimensional unipotent algebraic group has a commutative
rational-point group. -/
public theorem isMulCommutative_of_connected_dimension_eq_one_isUnipotent
    [IsAlgClosed k]
    {Y : Variety k} [AlgebraicGroup Y]
    (hconnected : Variety.IsConnected Y)
    (hdimension : Variety.dimension Y = 1)
    (hunipotent : IsUnipotentAlgebraicGroup Y) :
    IsMulCommutative (Variety.Point Y) := by
  obtain ⟨f, _, hkernel⟩ :=
    exists_surjective_morphism_toKPlus_kernelDimension_eq_zero
      hconnected hdimension hunipotent
  apply connected_isMulCommutative_of_finiteKernel f hconnected
    (f.kernel_finite_of_kernelClosedSubgroup_dimension_eq_zero hkernel)
  exact IsMulCommutative.of_comm fun x y ↦ by
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd
        (Multiplicative.toAdd (additiveGroupPointEquiv k x) +
          Multiplicative.toAdd (additiveGroupPointEquiv k y)) =
      Multiplicative.ofAdd
        (Multiplicative.toAdd (additiveGroupPointEquiv k y) +
          Multiplicative.toAdd (additiveGroupPointEquiv k x))
    rw [add_comm]

/-- A parametrization of a one-parameter closed subgroup has an affine
parameter coordinate obtained by restricting an ambient polynomial function. -/
public theorem oneParameterParametrization_exists_ambient_parameterPolynomial
    {G : Variety k} [AlgebraicGroup G] (X : ClosedSubgroup G)
    (x : OneParameterParametrization X.carrierVariety) :
    ∃ F : Variety.PolynomialFunction G,
      ∀ t : k, F (X.includePoint (x.value t)) = t := by
  let coordinate : Variety.PolynomialFunction (KPlus k) :=
    Variety.PolynomialFunction.ofPolynomial
      (KPlus k) (MvPolynomial.X PUnit.unit)
  let parameter : Variety.PolynomialFunction X.carrierVariety :=
    Variety.PolynomialFunction.pullback x.inv.toVariety coordinate
  obtain ⟨F, hF⟩ := X.exists_polynomialFunction_extension parameter
  refine ⟨F, ?_⟩
  intro t
  change F (X.inclusion.onPoints (x.value t)) = t
  rw [hF]
  change coordinate (x.inv.onPoints (x.hom.onPoints (kPlusPoint t))) = t
  rw [x.hom_inv_id]
  change evalPolynomial (kPlusPoint t).val (MvPolynomial.X PUnit.unit) = t
  rw [evalPolynomial_X]
  rfl

end Theory.AlgebraicGroup
