module

public import Theory.AlgebraicGroup.Automorphisms.Lang.FiniteFiberDominance
public import Theory.AlgebraicGroup.Automorphisms.Basic
public import Theory.AlgebraicGroup.RootData.Realization
public import Theory.AlgebraicGroup.RootSubgroups.Conjugation
public import Theory.AlgebraicGroup.Tori.Character.Operations
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.AdditivePolynomialDegree

universe u

/-!
# Positive-root factors of Steinberg endomorphisms

This module formalizes the root-orbit argument in Steinberg, *Endomorphisms of
Linear Algebraic Groups*, Theorem 10.5, as quoted in GLS3, Chapter 2.  The
geometric input is an actual based root-datum realization, a permutation of
the positive roots, and the induced character formula
`tau^*(rootPerm alpha) = alpha^(p^m)`.  These inputs are kept explicit because
raw `RootGroupData` does not itself classify the restriction of an
endomorphism to its realized root subgroups.

If every exponent on an orbit were zero, the product of the corresponding
root characters would be fixed by pullback.  It is nontrivial: the sum of
positive roots has strictly positive base height.  Surjectivity of the Lang
map on the torus, however, forces every fixed character to be trivial.  Thus
the exponent sum around the common permutation period is positive on every
positive-root orbit, giving one uniform positive iterate.
-/

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private noncomputable def rootBaseHeightHom
    {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem] (base : P.Base) : X →+ ℤ := by
  letI := Fintype.ofFinite base.support
  exact
    { toFun := fun x => ∑ j : base.support, base.toWeightBasis.repr x j
      map_zero' := by simp
      map_add' := by
        intro x y
        simpa [map_add] using
          (Finset.sum_add_distrib :
            (∑ j : base.support,
              (base.toWeightBasis.repr x j + base.toWeightBasis.repr y j)) = _) }

private lemma rootBaseHeightHom_root
    {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem] (base : P.Base) (i : ι) :
    rootBaseHeightHom P base (P.root i) = base.height i := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨f, _hfSupport, _hfSign, hfRoot⟩ := base.exists_root_eq_sum_int i
  have hfRootSubtype :
      P.root i = ∑ j : base.support, f j.1 • P.root j.1 := by
    exact hfRoot.trans
      (Finset.sum_subtype base.support (fun _ => Iff.rfl)
        (fun j => f j • P.root j))
  calc
    rootBaseHeightHom P base (P.root i) = ∑ j : base.support, f j.1 := by
      rw [rootBaseHeightHom, hfRootSubtype]
      simp
    _ = ∑ j ∈ base.support, f j := by
      exact (Finset.sum_subtype base.support (fun _ => Iff.rfl) f).symm
    _ = base.height i := (base.height_eq_sum hfRoot).symm

private lemma sum_roots_ne_zero_of_positive
    {A ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) (rootIndex : A → ι) (roots : Finset A)
    (hroots : roots.Nonempty)
    (hpositive : ∀ α ∈ roots, base.IsPos (rootIndex α)) :
    (∑ α ∈ roots, P.root (rootIndex α)) ≠ 0 := by
  intro hzero
  have hmap := congrArg (rootBaseHeightHom P base) hzero
  have hheightZero : (∑ α ∈ roots, base.height (rootIndex α)) = 0 := by
    simpa [map_sum, rootBaseHeightHom_root] using hmap
  have hheightPositive : 0 < ∑ α ∈ roots, base.height (rootIndex α) := by
    apply Finset.sum_pos'
    · intro α hα
      exact (hpositive α hα).le
    · obtain ⟨α, hα⟩ := hroots
      exact ⟨α, hα, hpositive α hα⟩
  exact hheightPositive.ne' hheightZero

private lemma prod_range_succ_mul_first
    {G : Type*} [CommGroup G] (f : ℕ → G) (n : ℕ) :
    (∏ i ∈ Finset.range n, f (i + 1)) * f 0 =
      (∏ i ∈ Finset.range n, f i) * f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        ((∏ i ∈ Finset.range n, f (i + 1)) * f (n + 1)) * f 0 =
            ((∏ i ∈ Finset.range n, f (i + 1)) * f 0) * f (n + 1) := by
              ac_rfl
        _ = ((∏ i ∈ Finset.range n, f i) * f n) * f (n + 1) := by rw [ih]

private lemma pullback_iterate_map_pow
    {G : Variety k} [AlgebraicGroup G]
    (tau : AlgebraicGroup.Morphism G G)
    (n q : ℕ) (χ : TorusCharacter G) :
    ((TorusCharacter.pullback tau : TorusCharacter G → TorusCharacter G)^[n])
        (χ ^ q) =
      (((TorusCharacter.pullback tau :
        TorusCharacter G → TorusCharacter G)^[n]) χ) ^ q := by
  induction n generalizing χ with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_pow, ih]

private lemma pullback_iterate_root_factor
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    (tau : AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety)
    (rootPerm : Equiv.Perm D.Root) (exponent : D.Root → ℕ)
    (hfactor : ∀ α,
      TorusCharacter.pullback tau (D.rootWeight (rootPerm α)) =
        D.rootWeight α ^ (ringChar k ^ exponent α))
    (α : D.Root) (n : ℕ) :
    ((TorusCharacter.pullback tau : TorusWeight T → TorusWeight T)^[n])
        (D.rootWeight ((rootPerm ^ n) α)) =
      D.rootWeight α ^
        (ringChar k ^ ∑ i ∈ Finset.range n, exponent ((rootPerm ^ i) α)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [show (rootPerm ^ (n + 1)) α =
          rootPerm ((rootPerm ^ n) α) by
        rw [pow_succ', Equiv.Perm.mul_apply]]
      rw [Function.iterate_succ_apply, hfactor, pullback_iterate_map_pow, ih]
      simp only [pow_add, pow_mul]

/-- If pullback sends every permuted positive-root character to a
`p`-power of its predecessor, Lang surjectivity forces the exponent sum over
the permutation period to be positive. -/
public theorem positive_root_orbit_exponent_sum_pos
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (positiveRoots : Set D.Root)
    (hActual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (tau : AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety)
    (hLang : Function.Surjective (langMorphism tau).toFun)
    (rootPerm : Equiv.Perm D.Root) (exponent : D.Root → ℕ)
    (hpositive : ∀ α, α ∈ positiveRoots ↔ rootPerm α ∈ positiveRoots)
    (hfactor : ∀ α,
      TorusCharacter.pullback tau (D.rootWeight (rootPerm α)) =
        D.rootWeight α ^ (ringChar k ^ exponent α))
    {α : D.Root} (hα : α ∈ positiveRoots) :
    0 < ∑ i ∈ Finset.range (orderOf rootPerm),
      exponent ((rootPerm ^ i) α) := by
  classical
  let _ := Fintype.ofFinite D.Root
  let n := orderOf rootPerm
  have hn : 0 < n := orderOf_pos rootPerm
  have hperiod : (rootPerm ^ n) α = α := by
    rw [pow_orderOf_eq_one]
    rfl
  have hiterPositive : ∀ i : ℕ, (rootPerm ^ i) α ∈ positiveRoots := by
    intro i
    induction i with
    | zero => simpa using hα
    | succ i ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact (hpositive _).mp ih
  by_contra hnot
  have hsumZero : ∑ i ∈ Finset.range n, exponent ((rootPerm ^ i) α) = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hexponentZero : ∀ i < n, exponent ((rootPerm ^ i) α) = 0 := by
    intro i hi
    have hle : exponent ((rootPerm ^ i) α) ≤
        ∑ j ∈ Finset.range n, exponent ((rootPerm ^ j) α) :=
      Finset.single_le_sum (f := fun j => exponent ((rootPerm ^ j) α))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
    omega
  let orbitCharacter : TorusWeight T :=
    ∏ i ∈ Finset.range n, D.rootWeight ((rootPerm ^ (i + 1)) α)
  have horbitNontrivial : orbitCharacter ≠ 1 := by
    have hsumRoots :
        (∑ i ∈ Finset.range n,
          P.root (e ((rootPerm ^ (i + 1)) α))) ≠ 0 := by
      apply sum_roots_ne_zero_of_positive P base
        (fun i => e ((rootPerm ^ (i + 1)) α)) (Finset.range n)
      · exact ⟨0, Finset.mem_range.mpr hn⟩
      · intro i _hi
        exact (hActual.2.2 _).mp (hiterPositive (i + 1))
    intro hone
    have hcharacterEq : orbitCharacter =
        weightEquiv (Multiplicative.ofAdd
          (∑ i ∈ Finset.range n,
            P.root (e ((rootPerm ^ (i + 1)) α)))) := by
      calc
        orbitCharacter =
            ∏ i ∈ Finset.range n,
              weightEquiv (Multiplicative.ofAdd
                (P.root (e ((rootPerm ^ (i + 1)) α)))) := by
              apply Finset.prod_congr rfl
              intro i _hi
              rw [hActual.2.1]
        _ = weightEquiv (Multiplicative.ofAdd
              (∑ i ∈ Finset.range n,
                P.root (e ((rootPerm ^ (i + 1)) α)))) := by
              rw [← map_prod weightEquiv]
              congr 1
    have hzero : Multiplicative.ofAdd
        (∑ i ∈ Finset.range n,
          P.root (e ((rootPerm ^ (i + 1)) α))) = 1 := by
      apply weightEquiv.injective
      rw [← hcharacterEq, hone, map_one]
    apply hsumRoots
    have := congrArg Multiplicative.toAdd hzero
    simpa using this
  have horbitFixed : TorusCharacter.pullback tau orbitCharacter = orbitCharacter := by
    rw [show TorusCharacter.pullback tau orbitCharacter =
        ∏ i ∈ Finset.range n,
          TorusCharacter.pullback tau
            (D.rootWeight ((rootPerm ^ (i + 1)) α)) by
      exact map_prod (TorusCharacter.pullback tau) _ _]
    have hfactorIter : ∀ i < n,
        TorusCharacter.pullback tau
            (D.rootWeight ((rootPerm ^ (i + 1)) α)) =
          D.rootWeight ((rootPerm ^ i) α) := by
      intro i hi
      rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hfactor, hexponentZero i hi]
      simp
    rw [show (∏ i ∈ Finset.range n,
          TorusCharacter.pullback tau
            (D.rootWeight ((rootPerm ^ (i + 1)) α))) =
        ∏ i ∈ Finset.range n, D.rootWeight ((rootPerm ^ i) α) by
      apply Finset.prod_congr rfl
      intro i hi
      exact hfactorIter i (Finset.mem_range.mp hi)]
    symm
    apply mul_right_cancel (b := D.rootWeight α)
    simpa [orbitCharacter, hperiod] using
      (prod_range_succ_mul_first
        (fun i => D.rootWeight ((rootPerm ^ i) α)) n)
  have horbitTrivial : orbitCharacter = 1 := by
    apply TorusCharacter.pointCharacter_injective
    ext t
    obtain ⟨x, rfl⟩ := hLang t
    rw [langMorphism_apply]
    simp only [map_mul, map_inv]
    change orbitCharacter.pointCharacter x *
        (orbitCharacter.pointCharacter (tau.onPoints x))⁻¹ =
          (1 : k) * 1⁻¹
    rw [one_mul, inv_one]
    have hpullPoint := congrArg
      (fun χ : TorusWeight T => χ.pointCharacter x) horbitFixed
    change orbitCharacter.pointCharacter (tau.onPoints x) =
      orbitCharacter.pointCharacter x at hpullPoint
    rw [hpullPoint]
    exact mul_inv_cancel₀ (by
      exact Units.ne_zero (dPointEquiv 1 (orbitCharacter.onPoints x) 0))
  exact horbitNontrivial horbitTrivial

/-- The order of the root permutation is one common positive iterate whose
accumulated exponent is positive on every positive root. -/
public theorem exists_positive_root_iterate_exponent_sum_pos
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (positiveRoots : Set D.Root)
    (hActual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (tau : AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety)
    (hLang : Function.Surjective (langMorphism tau).toFun)
    (rootPerm : Equiv.Perm D.Root) (exponent : D.Root → ℕ)
    (hpositive : ∀ α, α ∈ positiveRoots ↔ rootPerm α ∈ positiveRoots)
    (hfactor : ∀ α,
      TorusCharacter.pullback tau (D.rootWeight (rootPerm α)) =
        D.rootWeight α ^ (ringChar k ^ exponent α)) :
    ∃ n : ℕ, 0 < n ∧ rootPerm ^ n = 1 ∧
      ∀ α ∈ positiveRoots,
        0 < ∑ i ∈ Finset.range n, exponent ((rootPerm ^ i) α) := by
  classical
  let _ := Fintype.ofFinite D.Root
  refine ⟨orderOf rootPerm, orderOf_pos rootPerm,
    pow_orderOf_eq_one rootPerm, ?_⟩
  intro α hα
  exact positive_root_orbit_exponent_sum_pos D P base e weightEquiv
    positiveRoots hActual tau hLang rootPerm exponent hpositive hfactor hα

/-- A common positive iterate fixes every root label and pulls each positive
root character back by a strictly positive Frobenius exponent. -/
public theorem exists_positive_root_iterate_factor
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (positiveRoots : Set D.Root)
    (hActual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (tau : AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety)
    (hLang : Function.Surjective (langMorphism tau).toFun)
    (rootPerm : Equiv.Perm D.Root) (exponent : D.Root → ℕ)
    (hpositive : ∀ α, α ∈ positiveRoots ↔ rootPerm α ∈ positiveRoots)
    (hfactor : ∀ α,
      TorusCharacter.pullback tau (D.rootWeight (rootPerm α)) =
        D.rootWeight α ^ (ringChar k ^ exponent α)) :
    ∃ n : ℕ, 0 < n ∧ rootPerm ^ n = 1 ∧
      ∀ α ∈ positiveRoots,
        0 < ∑ i ∈ Finset.range n, exponent ((rootPerm ^ i) α) ∧
          ((TorusCharacter.pullback tau : TorusWeight T → TorusWeight T)^[n])
              (D.rootWeight α) =
            D.rootWeight α ^
              (ringChar k ^
                ∑ i ∈ Finset.range n, exponent ((rootPerm ^ i) α)) := by
  obtain ⟨n, hn, hperm, hpositiveSum⟩ :=
    exists_positive_root_iterate_exponent_sum_pos D P base e weightEquiv
      positiveRoots hActual tau hLang rootPerm exponent hpositive hfactor
  refine ⟨n, hn, hperm, ?_⟩
  intro α hα
  refine ⟨hpositiveSum α hα, ?_⟩
  have hiter := pullback_iterate_root_factor D tau rootPerm exponent hfactor α n
  rw [hperm] at hiter
  simpa using hiter

end Theory.AlgebraicGroup

/-!
## Surjective root factors

This section supplies the source-faithful geometric bridge used by Steinberg
10.5.  A witness records the actual closed image of each realized
one-parameter root subgroup and its parameter polynomial.  The finite root set
then gives a permutation by injectivity.  Equivariance with the torus action
and comparison of the top coefficient identify the pullback character with
the top-degree power.  The parameter identity makes the polynomial additive,
so the characteristic-power degree theorem rewrites this power as a Frobenius
factor.  In characteristic zero that theorem specializes to degree one without
introducing a Frobenius convention.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public structure RootSubgroupFrobeniusWitness
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicGroup.Morphism K K) (α : D.Root) where
  target : D.Root
  image_eq :
    (σ.comp (D.rootSubgroup α).inclusion).imageClosedSubgroup =
      D.rootSubgroup target
  sourceParam : OneParameterParametrization
      (D.rootSubgroup α).carrierVariety
  targetParam : OneParameterParametrization
      (D.rootSubgroup target).carrierVariety
  sourceWeightEquation :
    RootWeightEquation T (D.rootSubgroup α) (D.rootWeight α)
  targetWeightEquation :
    RootWeightEquation T (D.rootSubgroup target) (D.rootWeight target)
  polynomial : Polynomial k
  polynomial_ne_zero : polynomial ≠ 0
  parameter_eq : ∀ t : k,
    σ.onPoints ((D.rootSubgroup α).includePoint (sourceParam.value t)) =
      (D.rootSubgroup target).includePoint
        (targetParam.value (polynomial.eval t))

private lemma surjective_semisimple_injective
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hK : IsSemisimpleAlgebraicGroup K)
    (hσ : Function.Surjective σ.onPoints) :
    Function.Injective σ.onPoints := by
  obtain ⟨a, ha, _⟩ :=
    existsUnique_algebraicAutomorphism_realizing_surjective_endomorphism σ hK hσ
  intro x y hxy
  apply a.injective
  calc
    a x = σ.onPoints x := ha x
    _ = σ.onPoints y := hxy
    _ = a y := (ha y).symm

private lemma root_subgroup_eq_of_equal_image
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicGroup.Morphism K K)
    (hσinj : Function.Injective σ.onPoints)
    {α β : D.Root}
    (hαβ :
      (σ.comp (D.rootSubgroup α).inclusion).imageClosedSubgroup =
        (σ.comp (D.rootSubgroup β).inclusion).imageClosedSubgroup) :
    D.rootSubgroup α = D.rootSubgroup β := by
  apply SetLike.ext
  intro x
  constructor
  · intro hx
    let xa : Variety.Point (D.rootSubgroup α).carrierVariety :=
      (D.rootSubgroup α).pointEquiv.symm ⟨x, hx⟩
    have hmem : σ.onPoints x ∈
        (σ.comp (D.rootSubgroup β).inclusion).imageClosedSubgroup := by
      rw [← hαβ]
      change σ.onPoints ((D.rootSubgroup α).includePoint xa) ∈
        (σ.comp (D.rootSubgroup α).inclusion).imageClosedSubgroup
      exact ⟨xa, rfl⟩
    rcases hmem with ⟨y, hy⟩
    have hxy : x = (D.rootSubgroup β).includePoint y := by
      apply hσinj
      change σ.onPoints ((D.rootSubgroup β).includePoint y) = σ.onPoints x at hy
      exact hy.symm
    rw [hxy]
    exact (D.rootSubgroup β).pointEquiv y |>.property
  · intro hx
    let xb : Variety.Point (D.rootSubgroup β).carrierVariety :=
      (D.rootSubgroup β).pointEquiv.symm ⟨x, hx⟩
    have hmem : σ.onPoints x ∈
        (σ.comp (D.rootSubgroup α).inclusion).imageClosedSubgroup := by
      rw [hαβ]
      change σ.onPoints ((D.rootSubgroup β).includePoint xb) ∈
        (σ.comp (D.rootSubgroup β).inclusion).imageClosedSubgroup
      exact ⟨xb, rfl⟩
    rcases hmem with ⟨y, hy⟩
    have hxy : x = (D.rootSubgroup α).includePoint y := by
      apply hσinj
      change σ.onPoints ((D.rootSubgroup α).includePoint y) = σ.onPoints x at hy
      exact hy.symm
    rw [hxy]
    exact (D.rootSubgroup α).pointEquiv y |>.property

omit [IsAlgClosed k] in
private lemma one_parameter_value_injective
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) : Function.Injective x.value := by
  intro s t hst
  have h := congrArg x.inv.onPoints hst
  change x.inv.onPoints (x.hom.onPoints (kPlusPoint s)) =
      x.inv.onPoints (x.hom.onPoints (kPlusPoint t)) at h
  rw [x.hom_inv_id, x.hom_inv_id] at h
  exact congrArg (fun z : Variety.Point (KPlus k) =>
    Multiplicative.toAdd (additiveGroupPointEquiv k z)) h

omit [IsAlgClosed k] in
private lemma torus_character_pointCharacter_pow
    {T : Variety k} [AlgebraicGroup T]
    (χ : TorusCharacter T) (n : ℕ) (s : Variety.Point T) :
    (χ ^ n).pointCharacter s = χ.pointCharacter s ^ n := by
  induction n with
  | zero =>
    change (dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 : k) = _
    rw [dPointEquiv_one]
    simp
  | succ n ih =>
    rw [pow_succ]
    change (dPointEquiv 1 ((χ ^ n).onPoints s * χ.onPoints s) 0 : k) = _
    rw [dPointEquiv_mul]
    change (χ ^ n).pointCharacter s * χ.pointCharacter s = _
    rw [ih, pow_succ]

private lemma root_parameter_scaling
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicGroup.Morphism K K)
    (tau : AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety)
    (hτ : ∀ s, T.includePoint (tau.onPoints s) =
      σ.onPoints (T.includePoint s))
    {α : D.Root}
    (w : RootSubgroupFrobeniusWitness D σ α)
    (hα : RootWeightEquation T (D.rootSubgroup α) (D.rootWeight α))
    (hβ : RootWeightEquation T (D.rootSubgroup w.target)
      (D.rootWeight w.target))
    (s : Variety.Point T.carrierVariety) (t : k) :
    (D.rootWeight w.target).pointCharacter (tau.onPoints s) *
        w.polynomial.eval t =
      w.polynomial.eval ((D.rootWeight α).pointCharacter s * t) := by
  have hs := hα w.sourceParam t s
  have hsσ := congrArg σ.onPoints hs
  simp only [map_mul, map_inv] at hsσ
  have ht := hβ w.targetParam (w.polynomial.eval t) (tau.onPoints s)
  rw [← hτ s] at hsσ
  rw [w.parameter_eq, w.parameter_eq] at hsσ
  have hpoint := ht.symm.trans hsσ
  have hparam : w.targetParam.value
      ((D.rootWeight w.target).pointCharacter (tau.onPoints s) *
        w.polynomial.eval t) =
      w.targetParam.value
        (w.polynomial.eval ((D.rootWeight α).pointCharacter s * t)) := by
    apply (D.rootSubgroup w.target).inclusion_injective
    exact hpoint
  exact one_parameter_value_injective w.targetParam hparam

omit [IsAlgClosed k] in
private lemma root_parameter_value_add
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) (s t : k) :
    x.value (s + t) = x.value s * x.value t := by
  change x.hom.onPoints (kPlusPoint (s + t)) =
    x.hom.onPoints (kPlusPoint s) * x.hom.onPoints (kPlusPoint t)
  rw [show kPlusPoint (s + t) = kPlusPoint s * kPlusPoint t by
    apply (additiveGroupPointEquiv k).injective
    rfl, map_mul]

private lemma root_parameter_additive
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicGroup.Morphism K K) {α : D.Root}
    (w : RootSubgroupFrobeniusWitness D σ α) :
    IsAdditivePolynomial w.polynomial := by
  apply (isAdditivePolynomial_iff _).mpr
  intro s t
  apply one_parameter_value_injective w.targetParam
  apply (D.rootSubgroup w.target).inclusion_injective
  calc
    (D.rootSubgroup w.target).includePoint
        (w.targetParam.value (w.polynomial.eval (s + t))) =
        σ.onPoints ((D.rootSubgroup α).includePoint
          (w.sourceParam.value (s + t))) := by
          rw [w.parameter_eq]
    _ = σ.onPoints ((D.rootSubgroup α).includePoint
          (w.sourceParam.value s) *
          (D.rootSubgroup α).includePoint (w.sourceParam.value t)) := by
          rw [root_parameter_value_add]
          rfl
    _ = σ.onPoints ((D.rootSubgroup α).includePoint
          (w.sourceParam.value s)) *
        σ.onPoints ((D.rootSubgroup α).includePoint
          (w.sourceParam.value t)) := σ.map_mul _ _
    _ = (D.rootSubgroup w.target).includePoint
          (w.targetParam.value (w.polynomial.eval s)) *
        (D.rootSubgroup w.target).includePoint
          (w.targetParam.value (w.polynomial.eval t)) := by
          rw [w.parameter_eq, w.parameter_eq]
    _ = (D.rootSubgroup w.target).includePoint
          (w.targetParam.value (w.polynomial.eval s + w.polynomial.eval t)) := by
          rw [root_parameter_value_add]
          rfl

private lemma root_parameter_degree_charPower
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicGroup.Morphism K K) {α : D.Root}
    (w : RootSubgroupFrobeniusWitness D σ α) :
    ∃ m : ℕ, w.polynomial.natDegree = ringChar k ^ m := by
  exact additivePolynomial_natDegree_eq_ringChar_pow
    (root_parameter_additive D σ w) w.polynomial_ne_zero

private lemma root_parameter_character_formula
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicGroup.Morphism K K)
    (tau : AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety)
    (hτ : ∀ s, T.includePoint (tau.onPoints s) =
      σ.onPoints (T.includePoint s))
    {α : D.Root}
    (w : RootSubgroupFrobeniusWitness D σ α)
    (hα : RootWeightEquation T (D.rootSubgroup α) (D.rootWeight α))
    (hβ : RootWeightEquation T (D.rootSubgroup w.target)
      (D.rootWeight w.target))
    (hm : ∃ m : ℕ, w.polynomial.natDegree = ringChar k ^ m) :
    TorusCharacter.pullback tau (D.rootWeight w.target) =
      D.rootWeight α ^ (ringChar k ^
        Classical.choose hm) := by
  apply TorusCharacter.pointCharacter_injective
  ext s
  let m := Classical.choose hm
  have hm' : w.polynomial.natDegree = ringChar k ^ m :=
    Classical.choose_spec hm
  let c := (D.rootWeight α).pointCharacter s
  let d := (D.rootWeight w.target).pointCharacter (tau.onPoints s)
  have hev : ∀ t : k, w.polynomial.eval (c * t) = d *
      w.polynomial.eval t := by
    intro t
    simpa [c, d, mul_comm] using
      (root_parameter_scaling D σ tau hτ w hα hβ s t).symm
  have hpoly : w.polynomial.comp (Polynomial.C c * Polynomial.X) =
      Polynomial.C d * w.polynomial := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    exact hev t
  let n := w.polynomial.natDegree
  have hcoeff : w.polynomial.coeff n ≠ 0 := by
    rw [show w.polynomial.coeff n = w.polynomial.leadingCoeff by rfl]
    exact Polynomial.leadingCoeff_ne_zero.mpr w.polynomial_ne_zero
  have hc := congrArg (fun p : Polynomial k => p.coeff n) hpoly
  rw [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul] at hc
  have hcd : c ^ n = d := by
    apply (mul_right_cancel₀ hcoeff)
    calc
      c ^ n * w.polynomial.coeff n =
          w.polynomial.coeff n * c ^ n := mul_comm _ _
      _ = d * w.polynomial.coeff n := hc
  have hpull : (D.rootWeight w.target).pointCharacter (tau.onPoints s) =
      (D.rootWeight α).pointCharacter s ^ (ringChar k ^ m) := by
    have hc_exp : c ^ n = c ^ (ringChar k ^ m) := by
      rw [show n = ringChar k ^ m by simpa [n] using hm']
    exact (show (D.rootWeight w.target).pointCharacter (tau.onPoints s) = d by
      rfl).trans (hcd.symm.trans hc_exp)
  have hcharpow :
      (D.rootWeight α ^ (ringChar k ^ m)).pointCharacter s =
        (D.rootWeight α).pointCharacter s ^ (ringChar k ^ m) := by
    exact torus_character_pointCharacter_pow (D.rootWeight α)
      (ringChar k ^ m) s
  exact hpull.trans hcharpow.symm

public theorem exists_surjective_root_frobenius_factors
    {K : Variety k} [AlgebraicGroup K]
    {T B : ClosedSubgroup K} (D : RootGroupData K T) [Finite D.Root]
    {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (positiveRoots : Set D.Root)
    (_hActual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (hD : D.IsRealization)
    (hpositiveSubgroup : ∀ α, α ∈ positiveRoots ↔ D.rootSubgroup α ≤ B)
    (hK : IsSemisimpleAlgebraicGroup K)
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : Function.Surjective σ.onPoints)
    (hσB : σ.onPoints '' (B : Set (Variety.Point K)) =
      (B : Set (Variety.Point K)))
    (tau : AlgebraicGroup.Morphism T.carrierVariety T.carrierVariety)
    (hτ : ∀ s, T.includePoint (tau.onPoints s) = σ.onPoints (T.includePoint s))
    (hroot : ∀ α, Nonempty (RootSubgroupFrobeniusWitness D σ α)) :
    ∃ rootPerm : Equiv.Perm D.Root, ∃ exponent : D.Root → ℕ,
      (∀ α, α ∈ positiveRoots ↔ rootPerm α ∈ positiveRoots) ∧
      (∀ α,
        TorusCharacter.pullback tau (D.rootWeight (rootPerm α)) =
          D.rootWeight α ^ (ringChar k ^ exponent α)) := by
  classical
  let _ := Fintype.ofFinite D.Root
  have hσinj := surjective_semisimple_injective σ hK hσ
  let β : D.Root → D.Root := fun α => (hroot α).some.target
  have hβinj : Function.Injective β := by
    intro α γ hαγ
    have htarg : (hroot α).some.target = (hroot γ).some.target := by
      simpa [β] using hαγ
    have hsub : D.rootSubgroup α = D.rootSubgroup γ := by
      apply root_subgroup_eq_of_equal_image D σ hσinj
      rw [(hroot α).some.image_eq, (hroot γ).some.image_eq, htarg]
    have hαsub := hD.2.2.1 α
    have hγsub := hD.2.2.1 γ
    have hαeq := hαsub.2
    have hγeq := hγsub.2
    have hγeq' : RootWeightEquation T (D.rootSubgroup α)
        (D.rootWeight γ) := by simpa [hsub] using hγeq
    have hw : D.rootWeight α = D.rootWeight γ := by
      apply rootWeightEquation_unique T (D.rootSubgroup α) hαsub.1.2
        hαeq hγeq'
    exact hD.1 hw
  let rootPerm : Equiv.Perm D.Root :=
    Equiv.ofBijective β ⟨hβinj, (Finite.injective_iff_surjective.mp hβinj)⟩
  let exponent : D.Root → ℕ := fun α =>
    Classical.choose (root_parameter_degree_charPower D σ (hroot α).some)
  have hfactor : ∀ α,
      TorusCharacter.pullback tau (D.rootWeight (rootPerm α)) =
        D.rootWeight α ^ (ringChar k ^ exponent α) := by
    intro α
    let w := (hroot α).some
    have hformula := root_parameter_character_formula D σ tau hτ w
      (hD.2.2.1 α).2 (hD.2.2.1 (β α)).2
      (root_parameter_degree_charPower D σ w)
    have hrootperm : rootPerm α = β α := rfl
    rw [hrootperm]
    simpa [exponent, w] using hformula
  have hpositive : ∀ α, α ∈ positiveRoots ↔ rootPerm α ∈ positiveRoots := by
    intro α
    have hforward : α ∈ positiveRoots → β α ∈ positiveRoots := by
      intro hα
      apply (hpositiveSubgroup (β α)).2
      intro y hy
      have hmem : y ∈
          (σ.comp (D.rootSubgroup α).inclusion).imageClosedSubgroup := by
        rw [(hroot α).some.image_eq]
        exact hy
      rcases hmem with ⟨x, hx⟩
      have hxB : (D.rootSubgroup α).includePoint x ∈ B :=
        ((hpositiveSubgroup α).1 hα)
          ((D.rootSubgroup α).pointEquiv x).property
      have hsigB : σ.onPoints ((D.rootSubgroup α).includePoint x) ∈
          (B : Set (Variety.Point K)) := by
        have him : σ.onPoints ((D.rootSubgroup α).includePoint x) ∈
            σ.onPoints '' (B : Set (Variety.Point K)) :=
          ⟨(D.rootSubgroup α).includePoint x, hxB, rfl⟩
        exact hσB ▸ him
      simpa [show σ.onPoints ((D.rootSubgroup α).includePoint x) = y from hx]
        using hsigB
    constructor
    · exact hforward
    · intro hβpos
      apply (hpositiveSubgroup α).2
      intro x hx
      have hsigB : σ.onPoints x ∈ B := by
        let xa : Variety.Point (D.rootSubgroup α).carrierVariety :=
          (D.rootSubgroup α).pointEquiv.symm ⟨x, hx⟩
        have hy : σ.onPoints x ∈ D.rootSubgroup (β α) := by
          rw [← (hroot α).some.image_eq]
          have hxa : (D.rootSubgroup α).includePoint xa = x := by
            exact congrArg Subtype.val
              ((D.rootSubgroup α).pointEquiv.apply_symm_apply ⟨x, hx⟩)
          rw [← hxa]
          exact ⟨xa, rfl⟩
        exact (hpositiveSubgroup (β α)).1 hβpos hy
      have hsigB' : σ.onPoints x ∈ (B : Set (Variety.Point K)) := hsigB
      have him : σ.onPoints x ∈
          σ.onPoints '' (B : Set (Variety.Point K)) := hσB.symm ▸ hsigB'
      rcases him with ⟨b, hb, hbs⟩
      have hxb : x = b := (hσinj hbs).symm
      simpa [hxb] using hb
  exact ⟨rootPerm, exponent, hpositive, hfactor⟩

end Theory.AlgebraicGroup
