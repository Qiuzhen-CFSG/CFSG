module

public import Theory.AlgebraicGroup.Variety.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Base change for polynomial Proj

For a field `k`, a commutative `k`-algebra `R`, and a finite coordinate type `sigma`, this
module constructs the canonical isomorphism from `Proj (MvPolynomial sigma R)` to the base
change of coordinate projective space over `k`.  The principal result is
`Geometric.polynomialProjBaseChangeIso`; its projection formulas identify the comparison with
coefficient extension and the `R`-structure morphism.

The proof follows the standard homogeneous-coordinate cover.  On `D₊(X i)`, degree-zero
homogeneous localization is identified with the polynomial ring in all coordinates except `i`.
The resulting tensor/localization algebra equivalence proves the affine chart square is a
pullback.  These squares are transported through `Proj.basicOpenIsoSpec` and glued with
`Scheme.isPullback_of_openCover`.

The remaining declarations record functoriality under scalar extension and arbitrary coefficient
homomorphisms.  Consequently a graded substitution over `R` yields a morphism from the base-changed
projective space, and specializing through `R →ₐ[k] k` gives the `Proj.map` of the coefficientwise
specialized substitution, including its formula on `k`-rational points.  The construction uses the
Mathlib polynomial `Proj`, homogeneous-localization, affine pullback, and scheme-gluing APIs; it
does not rely on projective-space point classifications.
-/

set_option linter.style.haveILetI false

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {A : Type u} [CommRing A]
variable {sigma : Type} [Finite sigma]

private abbrev CoordinateComplement (i : sigma) := {j : sigma // j ≠ i}

private abbrev CoordinateChart (A : Type u) [CommRing A] (sigma : Type) (i : sigma) :=
  HomogeneousLocalization.Away (projectiveGrading A sigma) (MvPolynomial.X i)

private noncomputable def coordinateDehomogenize (i : sigma) :
    MvPolynomial sigma A →ₐ[A] MvPolynomial (CoordinateComplement i) A := by
  classical
  exact MvPolynomial.aeval fun j ↦ if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

omit [Finite sigma] in
@[simp] private lemma coordinateDehomogenize_X_self (i : sigma) :
    coordinateDehomogenize (A := A) i (MvPolynomial.X i) = 1 := by
  simp [coordinateDehomogenize]

omit [Finite sigma] in
@[simp] private lemma coordinateDehomogenize_X_ne (i j : sigma) (h : j ≠ i) :
    coordinateDehomogenize (A := A) i (MvPolynomial.X j) = MvPolynomial.X ⟨j, h⟩ := by
  simp [coordinateDehomogenize, h]

private theorem coordinateDehomogenize_injective_of_isHomogeneous
    (i : sigma) (n : ℕ) (p : MvPolynomial sigma A) (hp : p.IsHomogeneous n) :
    coordinateDehomogenize (A := A) i p = 0 ↔ p = 0 := by
  classical
  let e := Equiv.optionSubtypeNe i
  let p' : MvPolynomial (Option (CoordinateComplement i)) A :=
    MvPolynomial.renameEquiv A e.symm p
  let q : Polynomial (MvPolynomial (CoordinateComplement i) A) :=
    MvPolynomial.optionEquivLeft A (CoordinateComplement i) p'
  have hp' : p'.IsHomogeneous n := hp.rename_isHomogeneous
  have hq : ((MvPolynomial.optionEquivLeft A (CoordinateComplement i)).symm q).IsHomogeneous n := by
    simpa [q] using hp'
  have hEval : Polynomial.eval 1 q = coordinateDehomogenize (A := A) i p := by
    let lhs : MvPolynomial sigma A →ₐ[A] MvPolynomial (CoordinateComplement i) A :=
      { toRingHom := (Polynomial.evalRingHom
          (R := MvPolynomial (CoordinateComplement i) A) 1).comp
          ((MvPolynomial.optionEquivLeft A (CoordinateComplement i)).toRingEquiv.toRingHom.comp
            (MvPolynomial.renameEquiv A e.symm).toRingEquiv.toRingHom)
        commutes' := by simp }
    have hlhs : lhs = coordinateDehomogenize (A := A) i := by
      apply MvPolynomial.algHom_ext
      intro j
      by_cases hj : j = i
      · subst j
        simp [lhs, e, coordinateDehomogenize]
      · simp [lhs, e, coordinateDehomogenize, hj]
    simpa [lhs, q, p'] using DFunLike.congr_fun hlhs p
  constructor
  · intro h
    have hq0 : Polynomial.eval 1 q = 0 := hEval.trans h
    have hnat : q.natDegree ≤ n := by
      rw [MvPolynomial.natDegree_optionEquivLeft]
      exact (MvPolynomial.degreeOf_le_totalDegree p' none).trans hp'.totalDegree_le
    have q_coeff_eq_zero (j : ℕ) : q.coeff j = 0 := by
      by_cases hj : j ≤ n
      · have hcomponent := congr_arg
          (MvPolynomial.homogeneousComponent (n - j)) hq0
        rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hnat)] at hcomponent
        simp only [one_pow, mul_one, map_sum, map_zero] at hcomponent
        have component_coeff (l : ℕ) (hl : l ∈ Finset.range (n + 1)) :
            MvPolynomial.homogeneousComponent (n - j) (q.coeff l) =
              if l = j then q.coeff l else 0 := by
          have hln : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          have hql : (q.coeff l).IsHomogeneous (n - l) :=
            hq.coeff_isHomogeneous_of_optionEquivLeft_symm l (n - l)
              (Nat.add_sub_of_le hln)
          rw [MvPolynomial.homogeneousComponent_of_mem hql]
          by_cases hlj : l = j
          · simp [hlj]
          · have hsub : n - j ≠ n - l := by omega
            simp [hlj, hsub]
        have hcomponent' :
            (∑ l ∈ Finset.range (n + 1),
              if l = j then q.coeff l else 0) = 0 := by
          calc
            _ = ∑ l ∈ Finset.range (n + 1),
                MvPolynomial.homogeneousComponent (n - j) (q.coeff l) := by
              apply Finset.sum_congr rfl
              intro l hl
              exact (component_coeff l hl).symm
            _ = 0 := hcomponent
        simpa [hj] using hcomponent'
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hnat (lt_of_not_ge hj))
    apply (MvPolynomial.renameEquiv A e.symm).injective
    change p' = 0
    apply (MvPolynomial.optionEquivLeft A (CoordinateComplement i)).injective
    change q = 0
    exact Polynomial.ext fun j ↦ by simpa using q_coeff_eq_zero j
  · rintro rfl
    simp

omit [Finite sigma] in
lemma coordinate_X_mem (i : sigma) :
    MvPolynomial.X i ∈ projectiveGrading A sigma 1 := by
  exact (MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X i)).mpr
    (MvPolynomial.isHomogeneous_X A i)

omit [Finite sigma] in
private lemma coordinate_homogeneous_mem (n : ℕ) (p : MvPolynomial sigma A)
    (hp : p.IsHomogeneous n) : p ∈ projectiveGrading A sigma (n • 1) := by
  simpa using (MvPolynomial.mem_homogeneousSubmodule n p).mpr hp

private noncomputable instance coordinateChartAlgebra (i : sigma) :
    Algebra A (HomogeneousLocalization.Away
      (projectiveGrading A sigma) (MvPolynomial.X i)) :=
  ((HomogeneousLocalization.fromZeroRingHom (projectiveGrading A sigma)
      (Submonoid.powers (MvPolynomial.X i))).comp
    (algebraMap A (projectiveGrading A sigma 0))).toAlgebra

private noncomputable def coordinateChartToPolynomial (i : sigma) :
    HomogeneousLocalization.Away (projectiveGrading A sigma) (MvPolynomial.X i) →ₐ[A]
      MvPolynomial (CoordinateComplement i) A := by
  let lift : Localization.Away (MvPolynomial.X i) →+*
      MvPolynomial (CoordinateComplement i) A :=
    Localization.awayLift (coordinateDehomogenize (A := A) i).toRingHom
      (MvPolynomial.X i) (by simp)
  exact
    { toRingHom := lift.comp (algebraMap
        (HomogeneousLocalization.Away
          (projectiveGrading A sigma) (MvPolynomial.X i))
        (Localization.Away (MvPolynomial.X i)))
      commutes' := by
        intro a
        change lift (HomogeneousLocalization.val
          (HomogeneousLocalization.fromZeroRingHom (projectiveGrading A sigma)
            (Submonoid.powers (MvPolynomial.X i))
            ((algebraMap A (projectiveGrading A sigma 0)) a))) = MvPolynomial.C a
        change lift (Localization.mk (MvPolynomial.C a) 1) = MvPolynomial.C a
        rw [Localization.mk_one_eq_algebraMap]
        simp [lift, coordinateDehomogenize] }

private noncomputable def coordinatePolynomialToChart (i : sigma) :
    MvPolynomial (CoordinateComplement i) A →ₐ[A]
      HomogeneousLocalization.Away (projectiveGrading A sigma) (MvPolynomial.X i) :=
  MvPolynomial.aeval fun j ↦
    HomogeneousLocalization.Away.mk (projectiveGrading A sigma)
      (coordinate_X_mem (A := A) i) 1 (MvPolynomial.X j.1)
        (coordinate_homogeneous_mem (A := A) 1 (MvPolynomial.X j.1)
          (MvPolynomial.isHomogeneous_X A j.1))

omit [Finite sigma] in
@[simp] private lemma coordinateChartToPolynomial_mk (i : sigma) (n : ℕ)
    (p : MvPolynomial sigma A) (hp : p.IsHomogeneous n) :
    coordinateChartToPolynomial (A := A) i
        (HomogeneousLocalization.Away.mk (projectiveGrading A sigma)
          (coordinate_X_mem (A := A) i) n p
          (coordinate_homogeneous_mem (A := A) n p hp)) =
      coordinateDehomogenize (A := A) i p := by
  let hunit : IsUnit
      ((coordinateDehomogenize (A := A) i).toRingHom (MvPolynomial.X i)) := by simp
  change (Localization.awayLift (coordinateDehomogenize (A := A) i).toRingHom
      (MvPolynomial.X i) hunit) (Localization.mk p ⟨MvPolynomial.X i ^ n, by use n⟩) = _
  rw [Localization.awayLift_mk _ _ _ 1 (by simp) n]
  simp

omit [Finite sigma] in
private theorem coordinateChartToPolynomial_comp_coordinatePolynomialToChart (i : sigma) :
    (coordinateChartToPolynomial (A := A) i).comp
        (coordinatePolynomialToChart (A := A) i) =
      AlgHom.id A (MvPolynomial (CoordinateComplement i) A) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.coe_comp, Function.comp_apply, coordinatePolynomialToChart,
    MvPolynomial.aeval_X, AlgHom.id_apply]
  calc
    _ = coordinateDehomogenize (A := A) i (MvPolynomial.X j.1) :=
      coordinateChartToPolynomial_mk i 1 (MvPolynomial.X j.1)
        (MvPolynomial.isHomogeneous_X A j.1)
    _ = MvPolynomial.X j := coordinateDehomogenize_X_ne i j.1 j.2

private theorem coordinateChartToPolynomial_bijective (i : sigma) :
    Function.Bijective (coordinateChartToPolynomial (A := A) i) := by
  constructor
  · intro x y hxy
    suffices x - y = 0 by exact sub_eq_zero.mp this
    obtain ⟨n, p, hp, hrepr⟩ :=
      HomogeneousLocalization.Away.mk_surjective (projectiveGrading A sigma)
        (coordinate_X_mem (A := A) i) (x - y)
    have hp' : p.IsHomogeneous n := by
      change p ∈ MvPolynomial.homogeneousSubmodule sigma A (n • 1) at hp
      rw [nsmul_eq_mul, mul_one] at hp
      exact (MvPolynomial.mem_homogeneousSubmodule n p).mp hp
    rw [← hrepr]
    have hdehom : coordinateDehomogenize (A := A) i p = 0 := by
      rw [← coordinateChartToPolynomial_mk (hp := hp')]
      rw [hrepr, map_sub, hxy, sub_self]
    have hp0 : p = 0 :=
      (coordinateDehomogenize_injective_of_isHomogeneous i n p hp').mp hdehom
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk]
    rw [hp0]
    rw [HomogeneousLocalization.val_zero]
    exact Localization.mk_zero _
  · intro p
    refine ⟨coordinatePolynomialToChart (A := A) i p, ?_⟩
    exact DFunLike.congr_fun
      (coordinateChartToPolynomial_comp_coordinatePolynomialToChart (A := A) i) p

private noncomputable def coordinateChartAlgEquiv (i : sigma) :
    HomogeneousLocalization.Away (projectiveGrading A sigma) (MvPolynomial.X i) ≃ₐ[A]
      MvPolynomial (CoordinateComplement i) A :=
  AlgEquiv.ofBijective (coordinateChartToPolynomial (A := A) i)
    (coordinateChartToPolynomial_bijective (A := A) i)

omit [Finite sigma] in
private theorem coordinate_irrelevant_le_span :
    (HomogeneousIdeal.irrelevant (projectiveGrading A sigma)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : sigma → MvPolynomial sigma A)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ Ideal.span (Set.range (MvPolynomial.X : sigma → MvPolynomial sigma A))
  rw [show Set.range (MvPolynomial.X : sigma → MvPolynomial sigma A) =
    MvPolynomial.X '' (Set.univ : Set sigma) by simp]
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hdegree :=
    ((MvPolynomial.mem_homogeneousSubmodule n p).mp hp).degree_eq_sum_deg_support hm
  have hsupp : m.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hdegree
    omega
  obtain ⟨i, hi⟩ := hsupp
  exact ⟨i, Set.mem_univ i, Finsupp.mem_support_iff.mp hi⟩

private noncomputable def coordinateOpenCover :
    (Proj (projectiveGrading A sigma)).OpenCover :=
  Scheme.Cover.mkOfCovers sigma
    (fun i ↦ (Proj.basicOpen (projectiveGrading A sigma) (MvPolynomial.X i)).toScheme)
    (fun i ↦ (Proj.basicOpen (projectiveGrading A sigma) (MvPolynomial.X i)).ι)
    (fun x ↦ by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((Proj.iSup_basicOpen_eq_top (projectiveGrading A sigma) MvPolynomial.X
          (coordinate_irrelevant_le_span (A := A) (sigma := sigma))).ge (Set.mem_univ x))
      exact ⟨i, ⟨x, hi⟩, rfl⟩)

noncomputable def polynomialCoefficientExtension
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] (sigma : Type) :
    projectiveGrading k sigma →+*ᵍ projectiveGrading R sigma :=
  GradedRingHom.mk (MvPolynomial.map (algebraMap k R)) fun {n} p hp ↦ by
    exact (MvPolynomial.mem_homogeneousSubmodule n _).mpr
      (((MvPolynomial.mem_homogeneousSubmodule n _).mp hp).map (algebraMap k R))

@[simp] private theorem polynomialCoefficientExtension_apply
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] (sigma : Type)
    (p : MvPolynomial sigma k) :
    polynomialCoefficientExtension (k := k) (R := R) sigma p =
      MvPolynomial.map (algebraMap k R) p :=
  rfl

@[simp] private theorem polynomialCoefficientExtension_X
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] (sigma : Type) (i : sigma) :
    polynomialCoefficientExtension (k := k) (R := R) sigma (MvPolynomial.X i) =
      MvPolynomial.X i := by
  simp [polynomialCoefficientExtension]

private noncomputable def coordinatePolynomialMap
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) (i : sigma) :
    MvPolynomial (CoordinateComplement i) k →ₐ[k]
      MvPolynomial (CoordinateComplement i) R where
  toRingHom := MvPolynomial.map (algebraMap k R)
  commutes' := by simp

private noncomputable def coordinateAwayCongrMap
    (A : Type u) [CommRing A] (sigma : Type)
    {f f' : MvPolynomial sigma A} (h : f = f') :
    HomogeneousLocalization.Away (projectiveGrading A sigma) f →+*
      HomogeneousLocalization.Away (projectiveGrading A sigma) f' := by
  refine HomogeneousLocalization.map
    (P := Submonoid.powers f) (Q := Submonoid.powers f')
      (.id (projectiveGrading A sigma)) ?_
  intro x hx
  change (GradedRingHom.id (projectiveGrading A sigma)) x ∈ Submonoid.powers f'
  simpa only [GradedRingHom.coe_id, id_eq, h] using hx

private noncomputable def coordinateChartMap
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) (i : sigma) :
    CoordinateChart k sigma i →+* CoordinateChart R sigma i := by
  let g := polynomialCoefficientExtension (k := k) (R := R) sigma
  have h : g (MvPolynomial.X i) = MvPolynomial.X i :=
    polynomialCoefficientExtension_X sigma i
  exact (coordinateAwayCongrMap R sigma h).comp
    (HomogeneousLocalization.Away.map g (MvPolynomial.X i))

private theorem coordinateDehomogenize_map
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) (p : MvPolynomial sigma k) :
    coordinateDehomogenize (A := R) i (MvPolynomial.map (algebraMap k R) p) =
      MvPolynomial.map (algebraMap k R) (coordinateDehomogenize (A := k) i p) := by
  classical
  let lhs : MvPolynomial sigma k →ₐ[k] MvPolynomial (CoordinateComplement i) R :=
    { toRingHom := (coordinateDehomogenize (A := R) i).toRingHom.comp
        (MvPolynomial.map (algebraMap k R))
      commutes' := by simp [coordinateDehomogenize] }
  let rhs : MvPolynomial sigma k →ₐ[k] MvPolynomial (CoordinateComplement i) R :=
    (coordinatePolynomialMap (k := k) (R := R) sigma i).comp
      (coordinateDehomogenize (A := k) i)
  have h : lhs = rhs := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i
    · subst j
      simp [lhs, rhs, coordinateDehomogenize, coordinatePolynomialMap]
    · change coordinateDehomogenize (A := R) i
          (MvPolynomial.map (algebraMap k R) (MvPolynomial.X j)) =
        coordinatePolynomialMap (k := k) (R := R) sigma i
          (coordinateDehomogenize (A := k) i (MvPolynomial.X j))
      rw [MvPolynomial.map_X]
      rw [coordinateDehomogenize_X_ne (A := R) i j hj]
      rw [coordinateDehomogenize_X_ne (A := k) i j hj]
      change MvPolynomial.X (⟨j, hj⟩ : CoordinateComplement i) =
        MvPolynomial.map (algebraMap k R)
          (MvPolynomial.X (⟨j, hj⟩ : CoordinateComplement i))
      rw [MvPolynomial.map_X]
  exact DFunLike.congr_fun h p

@[simp] private theorem coordinateChartMap_mk
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) (n : ℕ) (p : MvPolynomial sigma k)
    (hp : p ∈ projectiveGrading k sigma (n • 1)) :
    coordinateChartMap (k := k) (R := R) sigma i
        (HomogeneousLocalization.Away.mk (projectiveGrading k sigma)
          (coordinate_X_mem (A := k) i) n p hp) =
      HomogeneousLocalization.Away.mk (projectiveGrading R sigma)
        (coordinate_X_mem (A := R) i) n
        (polynomialCoefficientExtension (k := k) (R := R) sigma p)
        ((polynomialCoefficientExtension (k := k) (R := R) sigma).2 hp) := by
  unfold coordinateChartMap
  dsimp only
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.Away.map_mk]
  unfold coordinateAwayCongrMap
  unfold HomogeneousLocalization.Away.mk
  rw [HomogeneousLocalization.map_mk]
  simp only [GradedRingHom.coe_id, id_eq,
    polynomialCoefficientExtension_X]

private noncomputable def coordinateChartBaseChangeEquiv
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    R ⊗[k] CoordinateChart k sigma i ≃ₐ[R] CoordinateChart R sigma i :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
      (coordinateChartAlgEquiv (A := k) i)).trans <|
    (MvPolynomial.algebraTensorAlgEquiv k R).trans <|
      (coordinateChartAlgEquiv (A := R) i).symm

private theorem coordinateChartBaseChangeEquiv_includeRight
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) (x : CoordinateChart k sigma i) :
    coordinateChartBaseChangeEquiv (k := k) (R := R) sigma i
        (Algebra.TensorProduct.includeRight x) =
      coordinateChartMap (k := k) (R := R) sigma i x := by
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (projectiveGrading k sigma)
      (coordinate_X_mem (A := k) i) x
  have hp' : p.IsHomogeneous n := by
    change p ∈ MvPolynomial.homogeneousSubmodule sigma k (n • 1) at hp
    rw [nsmul_eq_mul, mul_one] at hp
    exact (MvPolynomial.mem_homogeneousSubmodule n p).mp hp
  apply (coordinateChartAlgEquiv (A := R) i).injective
  rw [show (coordinateChartAlgEquiv (A := R) i)
      (coordinateChartBaseChangeEquiv (k := k) (R := R) sigma i
        (Algebra.TensorProduct.includeRight
          (HomogeneousLocalization.Away.mk (projectiveGrading k sigma)
            (coordinate_X_mem (A := k) i) n p hp))) =
      MvPolynomial.map (algebraMap k R) (coordinateDehomogenize (A := k) i p) by
        simp [coordinateChartBaseChangeEquiv, coordinateChartAlgEquiv,
          coordinateChartToPolynomial_mk (A := k) (hp := hp')]]
  rw [coordinateChartMap_mk]
  have hgp :
      (polynomialCoefficientExtension (k := k) (R := R) sigma p).IsHomogeneous n :=
    hp'.map (algebraMap k R)
  change MvPolynomial.map (algebraMap k R) (coordinateDehomogenize (A := k) i p) =
    coordinateChartToPolynomial (A := R) i
      (HomogeneousLocalization.Away.mk (projectiveGrading R sigma)
        (coordinate_X_mem (A := R) i) n
        (polynomialCoefficientExtension (k := k) (R := R) sigma p)
        ((polynomialCoefficientExtension (k := k) (R := R) sigma).2 hp))
  have hchart := coordinateChartToPolynomial_mk (A := R) i n
    (polynomialCoefficientExtension (k := k) (R := R) sigma p) hgp
  rw [hchart]
  exact (coordinateDehomogenize_map sigma i p).symm

private noncomputable def coordinateChartTensorEquiv
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    CoordinateChart k sigma i ⊗[k] R ≃+* CoordinateChart R sigma i := by
  letI : SMul R (CoordinateChart R sigma i) :=
    (coordinateChartAlgebra (A := R) i).toSMul
  letI : Algebra k (CoordinateChart R sigma i) :=
    Algebra.restrictScalars k R (CoordinateChart R sigma i)
  letI : SMul k (CoordinateChart R sigma i) :=
    (Algebra.restrictScalars k R (CoordinateChart R sigma i)).toSMul
  letI : IsScalarTower k R (CoordinateChart R sigma i) := by
    exact IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact ((Algebra.TensorProduct.comm k (CoordinateChart k sigma i) R).trans
    ((coordinateChartBaseChangeEquiv (k := k) (R := R) sigma i).restrictScalars k)).toRingEquiv

private theorem coordinateChartTensorEquiv_includeLeft
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) (x : CoordinateChart k sigma i) :
    coordinateChartTensorEquiv (k := k) (R := R) sigma i
        (Algebra.TensorProduct.includeLeftRingHom x) =
      coordinateChartMap (k := k) (R := R) sigma i x := by
  change coordinateChartBaseChangeEquiv (k := k) (R := R) sigma i
      (Algebra.TensorProduct.includeRight x) =
    coordinateChartMap (k := k) (R := R) sigma i x
  exact coordinateChartBaseChangeEquiv_includeRight sigma i x

private theorem coordinateChartTensorEquiv_includeRight
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) (r : R) :
    coordinateChartTensorEquiv (k := k) (R := R) sigma i
        (Algebra.TensorProduct.includeRight r) =
      algebraMap R (CoordinateChart R sigma i) r := by
  change coordinateChartBaseChangeEquiv (k := k) (R := R) sigma i
      (Algebra.TensorProduct.includeLeftRingHom r) =
    algebraMap R (CoordinateChart R sigma i) r
  exact (coordinateChartBaseChangeEquiv (k := k) (R := R) sigma i).commutes r

private theorem polynomialCoefficientExtension_irrelevant
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] :
    HomogeneousIdeal.irrelevant (projectiveGrading R sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading k sigma)).map
        (polynomialCoefficientExtension (k := k) (R := R) sigma) := by
  rw [← toIdeal_le_toIdeal_iff]
  refine (coordinate_irrelevant_le_span (A := R) (sigma := sigma)).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [← polynomialCoefficientExtension_X (k := k) (R := R) sigma i]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem (projectiveGrading k sigma) one_pos
      (coordinate_X_mem (A := k) i))

noncomputable def polynomialProjMap
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] :
    Proj (projectiveGrading R sigma) ⟶ Proj (projectiveGrading k sigma) :=
  Proj.map (polynomialCoefficientExtension (k := k) (R := R) sigma)
    (polynomialCoefficientExtension_irrelevant (k := k) (R := R) sigma)

noncomputable def polynomialProjStructureMap
    (A : Type u) [CommRing A] (sigma : Type) :
    Proj (projectiveGrading A sigma) ⟶ Spec (.of A) :=
  Proj.toSpecZero (projectiveGrading A sigma) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (projectiveGrading A sigma 0)))

public theorem polynomialProjStructureMap_eq_projectiveSpaceByCoordinates
    (A : Type u) [Field A] (sigma : Type) [Finite sigma] :
    polynomialProjStructureMap A sigma =
      (projectiveSpaceByCoordinates A sigma).structureMap := by
  rfl

private noncomputable abbrev coordinateChartBaseRingHom
    (A : Type u) [CommRing A] (sigma : Type) (i : sigma) :
    A →+* CoordinateChart A sigma i :=
  (HomogeneousLocalization.fromZeroRingHom (projectiveGrading A sigma)
    (Submonoid.powers (MvPolynomial.X i))).comp
      (algebraMap A (projectiveGrading A sigma 0))

private noncomputable def coordinateChartPullbackSpecIso
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    pullback
        (Spec.map (CommRingCat.ofHom (coordinateChartBaseRingHom k sigma i)))
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ≅
      Spec (.of (CoordinateChart R sigma i)) := by
  letI : Algebra k (CoordinateChart R sigma i) :=
    Algebra.restrictScalars k R (CoordinateChart R sigma i)
  exact pullbackSpecIso k (CoordinateChart k sigma i) R ≪≫
    Scheme.Spec.mapIso
      ((coordinateChartTensorEquiv (k := k) (R := R) sigma i).symm.toCommRingCatIso.op)

private theorem coordinateChartPullbackSpecIso_inv_fst
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    (coordinateChartPullbackSpecIso (k := k) (R := R) sigma i).inv ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom (coordinateChartBaseRingHom k sigma i)))
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) =
      Spec.map (CommRingCat.ofHom
        (coordinateChartMap (k := k) (R := R) sigma i)) := by
  change (coordinateChartPullbackSpecIso (k := k) (R := R) sigma i).inv ≫
      pullback.fst
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (CoordinateChart k sigma i))))
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) =
    Spec.map (CommRingCat.ofHom
      (coordinateChartMap (k := k) (R := R) sigma i))
  unfold coordinateChartPullbackSpecIso
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact coordinateChartTensorEquiv_includeLeft sigma i x

private theorem coordinateChartPullbackSpecIso_inv_snd
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    (coordinateChartPullbackSpecIso (k := k) (R := R) sigma i).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (coordinateChartBaseRingHom k sigma i)))
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) =
      Spec.map (CommRingCat.ofHom (coordinateChartBaseRingHom R sigma i)) := by
  change (coordinateChartPullbackSpecIso (k := k) (R := R) sigma i).inv ≫
      pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (CoordinateChart k sigma i))))
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) =
    Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateChart R sigma i)))
  unfold coordinateChartPullbackSpecIso
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact coordinateChartTensorEquiv_includeRight sigma i r

private theorem coordinateChartSpec_isPullback
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (coordinateChartMap (k := k) (R := R) sigma i)))
      (Spec.map (CommRingCat.ofHom (coordinateChartBaseRingHom R sigma i)))
      (Spec.map (CommRingCat.ofHom (coordinateChartBaseRingHom k sigma i)))
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  refine (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (coordinateChartBaseRingHom k sigma i)))
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))).of_iso'
      (coordinateChartPullbackSpecIso (k := k) (R := R) sigma i).symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa using coordinateChartPullbackSpecIso_inv_fst
      (k := k) (R := R) sigma i
  · simpa using coordinateChartPullbackSpecIso_inv_snd
      (k := k) (R := R) sigma i
  · simp
  · simp

private noncomputable def coordinatePullbackIso
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    pullback (polynomialProjMap (k := k) (R := R) sigma)
        (Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i)).ι ≅
      Spec (.of (CoordinateChart R sigma i)) :=
  pullbackRestrictIsoRestrict
      (polynomialProjMap (k := k) (R := R) sigma)
      (Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i)) ≪≫
    (Proj (projectiveGrading R sigma)).isoOfEq (by
      simp only [polynomialProjMap, Proj.map_preimage_basicOpen]
      rw [polynomialCoefficientExtension_X]) ≪≫
    Proj.basicOpenIsoSpec (projectiveGrading R sigma) (MvPolynomial.X i)
      (coordinate_X_mem (A := R) i) one_pos

private theorem awayι_comp_polynomialProjStructureMap
    (A : Type u) [CommRing A] (sigma : Type) [Finite sigma] (i : sigma) :
    Proj.awayι (projectiveGrading A sigma) (MvPolynomial.X i)
        (coordinate_X_mem (A := A) i) one_pos ≫
      polynomialProjStructureMap A sigma =
    Spec.map (CommRingCat.ofHom (coordinateChartBaseRingHom A sigma i)) := by
  rw [polynomialProjStructureMap, ← Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

private theorem awayι_comp_polynomialProjStructureMap_general
    (A : Type u) [CommRing A] (sigma : Type) [Finite sigma]
    {d : ℕ} (p : MvPolynomial sigma A) (hp : p ∈ projectiveGrading A sigma d)
    (hd : 0 < d) :
    Proj.awayι (projectiveGrading A sigma) p hp hd ≫
      polynomialProjStructureMap A sigma =
    Spec.map (CommRingCat.ofHom
      ((HomogeneousLocalization.fromZeroRingHom (projectiveGrading A sigma)
        (Submonoid.powers p)).comp
        (algebraMap A (projectiveGrading A sigma 0)))) := by
  rw [polynomialProjStructureMap, ← Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem polynomialProjMap_preserves_structureMap
    (A : Type u) [CommRing A] (sigma : Type) [Finite sigma]
    (f : projectiveGrading A sigma →+*ᵍ projectiveGrading A sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading A sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading A sigma)).map f)
    (hC : ∀ r : A, f (MvPolynomial.C r) = MvPolynomial.C r) :
    Proj.map f hf ≫ polynomialProjStructureMap A sigma =
      polynomialProjStructureMap A sigma := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s => ?_
  have hs := Proj.mapAffineOpenCover_f f hf s
  change (Proj.mapAffineOpenCover f hf).f s ≫ _ =
    (Proj.mapAffineOpenCover f hf).f s ≫ _
  rw [hs]
  have hmap := Proj.awayι_comp_map_assoc f hf s.fst.2 (s.snd : _)
    s.snd.property
    (polynomialProjStructureMap A sigma)
  have hsrc := awayι_comp_polynomialProjStructureMap_general A sigma
    (s.snd : MvPolynomial sigma A) s.snd.property s.fst.2
  have htar := awayι_comp_polynomialProjStructureMap_general A sigma
    (f (s.snd : MvPolynomial sigma A)) (f.2 s.snd.property) s.fst.2
  apply hmap.trans
  calc
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f
        (s.snd : MvPolynomial sigma A))) ≫
        Proj.awayι (projectiveGrading A sigma) (s.snd : MvPolynomial sigma A)
          s.snd.property s.fst.2 ≫ polynomialProjStructureMap A sigma =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f
        (s.snd : MvPolynomial sigma A))) ≫
        Spec.map (CommRingCat.ofHom
          ((HomogeneousLocalization.fromZeroRingHom (projectiveGrading A sigma)
            (Submonoid.powers (s.snd : MvPolynomial sigma A))).comp
            (algebraMap A (projectiveGrading A sigma 0)))) := by
          exact congrArg (fun q ↦
            Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f
              (s.snd : MvPolynomial sigma A))) ≫ q) hsrc
    _ = Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (projectiveGrading A sigma)
          (Submonoid.powers (f (s.snd : MvPolynomial sigma A)))).comp
          (algebraMap A (projectiveGrading A sigma 0)))) := by
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      change HomogeneousLocalization.Away.map f (s.snd : MvPolynomial sigma A)
          ((HomogeneousLocalization.fromZeroRingHom (projectiveGrading A sigma)
            (Submonoid.powers (s.snd : MvPolynomial sigma A))).comp
            (algebraMap A (projectiveGrading A sigma 0)) x) =
        (HomogeneousLocalization.fromZeroRingHom (projectiveGrading A sigma)
          (Submonoid.powers (f (s.snd : MvPolynomial sigma A)))).comp
        (algebraMap A (projectiveGrading A sigma 0)) x
      have hfx : f ((algebraMap A (projectiveGrading A sigma 0)) x) =
          (algebraMap A (projectiveGrading A sigma 0)) x := by
        change f (MvPolynomial.C x) = MvPolynomial.C x
        exact hC x
      have hmap_fromZero (a : projectiveGrading A sigma 0) :
          HomogeneousLocalization.Away.map f (s.snd : MvPolynomial sigma A)
              ((HomogeneousLocalization.fromZeroRingHom (projectiveGrading A sigma)
                (Submonoid.powers (s.snd : MvPolynomial sigma A))) a) =
            HomogeneousLocalization.fromZeroRingHom (projectiveGrading A sigma)
              (Submonoid.powers (f (s.snd : MvPolynomial sigma A)))
              ⟨f a, f.2 a.property⟩ := by
        change HomogeneousLocalization.map f _ (HomogeneousLocalization.mk _) =
          HomogeneousLocalization.mk _
        rw [HomogeneousLocalization.map_mk]
        congr 1
        cases a
        congr 1
        simp
        apply Subtype.ext
        rfl
      have hfx' :
          (⟨f ((algebraMap A (projectiveGrading A sigma 0)) x),
            f.2 ((algebraMap A (projectiveGrading A sigma 0)) x).property⟩ :
              projectiveGrading A sigma 0) =
            (algebraMap A (projectiveGrading A sigma 0)) x := by
        apply Subtype.ext
        exact hfx
      rw [RingHom.comp_apply, hmap_fromZero, hfx']
      rfl
    _ = Proj.awayι (projectiveGrading A sigma) (f (s.snd : MvPolynomial sigma A))
          (f.2 s.snd.property) s.fst.2 ≫ polynomialProjStructureMap A sigma := htar.symm

private theorem coordinateAwayCongrMap_comp_awayι
    (A : Type u) [CommRing A] (sigma : Type)
    {f f' : MvPolynomial sigma A} (h : f = f')
    {n : ℕ} (hf : f ∈ projectiveGrading A sigma n)
    (hf' : f' ∈ projectiveGrading A sigma n) (hn : 0 < n) :
    Spec.map (CommRingCat.ofHom (coordinateAwayCongrMap A sigma h)) ≫
        Proj.awayι (projectiveGrading A sigma) f hf hn =
      Proj.awayι (projectiveGrading A sigma) f' hf' hn := by
  subst f'
  have heq : coordinateAwayCongrMap A sigma (Eq.refl f) =
      RingHom.id (HomogeneousLocalization.Away (projectiveGrading A sigma) f) := by
    simp [coordinateAwayCongrMap]
  rw [heq]
  simp

private theorem coordinateChartMap_comp_awayι
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    Spec.map (CommRingCat.ofHom (coordinateChartMap (k := k) (R := R) sigma i)) ≫
        Proj.awayι (projectiveGrading k sigma) (MvPolynomial.X i)
          (coordinate_X_mem (A := k) i) one_pos =
      Proj.awayι (projectiveGrading R sigma) (MvPolynomial.X i)
          (coordinate_X_mem (A := R) i) one_pos ≫
        polynomialProjMap (k := k) (R := R) sigma := by
  let g := polynomialCoefficientExtension (k := k) (R := R) sigma
  let hg := polynomialCoefficientExtension_irrelevant (k := k) (R := R) sigma
  let h := polynomialCoefficientExtension_X (k := k) (R := R) sigma i
  rw [← coordinateAwayCongrMap_comp_awayι R sigma h
    (g.2 (coordinate_X_mem (A := k) i)) (coordinate_X_mem (A := R) i) one_pos]
  unfold polynomialProjMap
  rw [Category.assoc, Proj.awayι_comp_map g hg one_pos
    (MvPolynomial.X i) (coordinate_X_mem (A := k) i)]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

@[reassoc] private theorem coordinatePullbackIso_hom_awayι
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    (coordinatePullbackIso (k := k) (R := R) sigma i).hom ≫
        Proj.awayι (projectiveGrading R sigma) (MvPolynomial.X i)
          (coordinate_X_mem (A := R) i) one_pos =
      pullback.fst (polynomialProjMap (k := k) (R := R) sigma)
        (Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i)).ι := by
  simp [coordinatePullbackIso, Proj.awayι]

private theorem coordinatePullback_isPullback
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    IsPullback
      (pullback.snd (polynomialProjMap (k := k) (R := R) sigma)
        (Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i)).ι)
      (pullback.fst (polynomialProjMap (k := k) (R := R) sigma)
          (Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i)).ι ≫
        polynomialProjStructureMap R sigma)
      ((Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i)).ι ≫
        polynomialProjStructureMap k sigma)
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let e := coordinatePullbackIso (k := k) (R := R) sigma i
  let eₖ := Proj.basicOpenIsoSpec (projectiveGrading k sigma) (MvPolynomial.X i)
    (coordinate_X_mem (A := k) i) one_pos
  refine (coordinateChartSpec_isPullback (k := k) (R := R) sigma i).of_iso'
    e eₖ (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono eₖ.inv, ← cancel_mono
      (Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i)).ι]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [Proj.basicOpenIsoSpec_inv_ι]
    rw [coordinateChartMap_comp_awayι]
    rw [← Category.assoc, coordinatePullbackIso_hom_awayι]
    exact pullback.condition
  · rw [← awayι_comp_polynomialProjStructureMap R sigma i]
    simpa [e] using coordinatePullbackIso_hom_awayι_assoc
      (k := k) (R := R) sigma i (polynomialProjStructureMap R sigma)
  · rw [← awayι_comp_polynomialProjStructureMap k sigma i]
    simp [eₖ, Proj.awayι]
  · simp

theorem polynomialProjBaseChange_isPullback
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] :
    IsPullback
      (polynomialProjMap (k := k) (R := R) sigma)
      (polynomialProjStructureMap R sigma)
      (polynomialProjStructureMap k sigma)
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _
    (coordinateOpenCover (A := k) (sigma := sigma)) ?_
  intro i
  change sigma at i
  change IsPullback
    (pullback.snd (polynomialProjMap (k := k) (R := R) sigma)
      (Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i)).ι)
    (pullback.fst (polynomialProjMap (k := k) (R := R) sigma)
        (Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i)).ι ≫
      polynomialProjStructureMap R sigma)
    ((Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i)).ι ≫
      polynomialProjStructureMap k sigma)
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  exact coordinatePullback_isPullback (k := k) (R := R) sigma i

/-- The polynomial `Proj` over `R` is the base change of coordinate projective space from `k`.
The isomorphism is the canonical comparison associated to the pullback square. -/
noncomputable def polynomialProjBaseChangeIso
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] :
    Proj (projectiveGrading R sigma) ≅
      pullback (projectiveSpaceByCoordinates k sigma).structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
  (polynomialProjBaseChange_isPullback (k := k) (R := R) sigma).isoPullback

@[reassoc (attr := simp)]
theorem polynomialProjBaseChangeIso_hom_fst
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] :
    (polynomialProjBaseChangeIso k R sigma).hom ≫
        pullback.fst (projectiveSpaceByCoordinates k sigma).structureMap
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) =
      polynomialProjMap (k := k) (R := R) sigma :=
  (polynomialProjBaseChange_isPullback (k := k) (R := R) sigma).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem polynomialProjBaseChangeIso_hom_snd
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] :
    (polynomialProjBaseChangeIso k R sigma).hom ≫
        pullback.snd (projectiveSpaceByCoordinates k sigma).structureMap
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) =
      polynomialProjStructureMap R sigma :=
  (polynomialProjBaseChange_isPullback (k := k) (R := R) sigma).isoPullback_hom_snd

theorem polynomialCoefficientExtension_comp
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (sigma : Type) :
    polynomialCoefficientExtension (k := k) (R := S) sigma =
      (polynomialCoefficientExtension (k := R) (R := S) sigma).comp
        (polynomialCoefficientExtension (k := k) (R := R) sigma) := by
  apply GradedRingHom.ext
  intro p
  change MvPolynomial.map (algebraMap k S) p =
    MvPolynomial.map (algebraMap R S) (MvPolynomial.map (algebraMap k R) p)
  rw [MvPolynomial.map_map]
  congr 1
  exact congrArg MvPolynomial.map (IsScalarTower.algebraMap_eq k R S)

theorem polynomialProjMap_comp
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (sigma : Type) [Finite sigma] :
    polynomialProjMap (k := k) (R := S) sigma =
      polynomialProjMap (k := R) (R := S) sigma ≫
        polynomialProjMap (k := k) (R := R) sigma := by
  unfold polynomialProjMap
  rw [← Proj.map_comp]
  congr 1
  exact polynomialCoefficientExtension_comp (k := k) (R := R) (S := S) sigma

/-- Map coefficients of a homogeneous polynomial along an arbitrary ring homomorphism. -/
noncomputable def polynomialCoefficientMap
    {A B : Type u} [CommRing A] [CommRing B]
    (sigma : Type) (f : A →+* B) :
    projectiveGrading A sigma →+*ᵍ projectiveGrading B sigma :=
  GradedRingHom.mk (MvPolynomial.map f) fun {n} p hp ↦ by
    exact (MvPolynomial.mem_homogeneousSubmodule n _).mpr
      (((MvPolynomial.mem_homogeneousSubmodule n _).mp hp).map f)

@[simp] theorem polynomialCoefficientMap_X
    {A B : Type u} [CommRing A] [CommRing B]
    (sigma : Type) (f : A →+* B) (i : sigma) :
    polynomialCoefficientMap sigma f (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [polynomialCoefficientMap]

@[simp] theorem polynomialCoefficientMap_C
    {A B : Type u} [CommRing A] [CommRing B]
    (sigma : Type) (f : A →+* B) (r : A) :
    polynomialCoefficientMap sigma f (MvPolynomial.C r) = MvPolynomial.C (f r) := by
  simp [polynomialCoefficientMap]

theorem polynomialCoefficientMap_irrelevant
    {A B : Type u} [CommRing A] [CommRing B]
    (sigma : Type) [Finite sigma] (f : A →+* B) :
    HomogeneousIdeal.irrelevant (projectiveGrading B sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading A sigma)).map
        (polynomialCoefficientMap sigma f) := by
  rw [← toIdeal_le_toIdeal_iff]
  refine (coordinate_irrelevant_le_span (A := B) (sigma := sigma)).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [← polynomialCoefficientMap_X sigma f i]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem (projectiveGrading A sigma) one_pos
      (coordinate_X_mem (A := A) i))

/-- Contravariant polynomial `Proj` map induced by an arbitrary coefficient homomorphism. -/
noncomputable def polynomialProjMapOfRingHom
    {A B : Type u} [CommRing A] [CommRing B]
    (sigma : Type) [Finite sigma] (f : A →+* B) :
    Proj (projectiveGrading B sigma) ⟶ Proj (projectiveGrading A sigma) :=
  Proj.map (polynomialCoefficientMap sigma f)
    (polynomialCoefficientMap_irrelevant sigma f)

theorem polynomialProjMap_eq_mapOfRingHom
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] :
    polynomialProjMap (k := k) (R := R) sigma =
      polynomialProjMapOfRingHom sigma (algebraMap k R) := by
  rfl

theorem polynomialCoefficientMap_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (sigma : Type) (f : A →+* B) (g : B →+* C) :
    polynomialCoefficientMap sigma (g.comp f) =
      (polynomialCoefficientMap sigma g).comp (polynomialCoefficientMap sigma f) := by
  apply GradedRingHom.ext
  intro p
  change MvPolynomial.map (g.comp f) p =
    MvPolynomial.map g (MvPolynomial.map f p)
  exact (MvPolynomial.map_map f g p).symm

theorem polynomialProjMapOfRingHom_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (sigma : Type) [Finite sigma] (f : A →+* B) (g : B →+* C) :
    polynomialProjMapOfRingHom sigma (g.comp f) =
      polynomialProjMapOfRingHom sigma g ≫ polynomialProjMapOfRingHom sigma f := by
  unfold polynomialProjMapOfRingHom
  rw [← Proj.map_comp]
  congr 1
  exact polynomialCoefficientMap_comp sigma f g

@[simp] theorem polynomialProjMapOfRingHom_id
    (A : Type u) [CommRing A] (sigma : Type) [Finite sigma] :
    polynomialProjMapOfRingHom sigma (RingHom.id A) =
      𝟙 (Proj (projectiveGrading A sigma)) := by
  unfold polynomialProjMapOfRingHom
  have h : polynomialCoefficientMap sigma (RingHom.id A) =
      GradedRingHom.id (projectiveGrading A sigma) := by
    apply GradedRingHom.ext
    intro p
    exact MvPolynomial.map_id p
  simpa only [h] using
    (Proj.map_id :
      Proj.map (GradedRingHom.id (projectiveGrading A sigma)) (by simp) =
        𝟙 (Proj (projectiveGrading A sigma)))

theorem polynomialProjMapOfRingHom_structureMap
    {A B : Type u} [CommRing A] [CommRing B]
    (sigma : Type) [Finite sigma] (f : A →+* B) :
    polynomialProjMapOfRingHom sigma f ≫ polynomialProjStructureMap A sigma =
      polynomialProjStructureMap B sigma ≫ Spec.map (CommRingCat.ofHom f) := by
  letI : Algebra A B := f.toAlgebra
  change polynomialProjMap (k := A) (R := B) sigma ≫
      polynomialProjStructureMap A sigma =
    polynomialProjStructureMap B sigma ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))
  exact (polynomialProjBaseChange_isPullback (k := A) (R := B) sigma).w

/-- A graded endomorphism over `R`, transported across polynomial `Proj` base change, defines a
family of endomorphisms of coordinate projective space over `Spec R`. -/
noncomputable def polynomialProjFamilyMap
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma]
    (f : projectiveGrading R sigma →+*ᵍ projectiveGrading R sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading R sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading R sigma)).map f) :
    pullback (projectiveSpaceByCoordinates k sigma).structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶
      (projectiveSpaceByCoordinates k sigma).toScheme :=
  (polynomialProjBaseChangeIso k R sigma).inv ≫ Proj.map f hf ≫
    polynomialProjMap (k := k) (R := R) sigma

theorem polynomialProjFamilyMap_overBase
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma]
    (f : projectiveGrading R sigma →+*ᵍ projectiveGrading R sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading R sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading R sigma)).map f)
    (hbase : Proj.map f hf ≫ polynomialProjStructureMap R sigma =
      polynomialProjStructureMap R sigma) :
    polynomialProjFamilyMap k R sigma f hf ≫
        (projectiveSpaceByCoordinates k sigma).structureMap =
      pullback.snd (projectiveSpaceByCoordinates k sigma).structureMap
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
  change ((polynomialProjBaseChangeIso k R sigma).inv ≫ Proj.map f hf ≫
      polynomialProjMap (k := k) (R := R) sigma) ≫
        polynomialProjStructureMap k sigma =
    pullback.snd (projectiveSpaceByCoordinates k sigma).structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))
  simp only [Category.assoc]
  rw [(polynomialProjBaseChange_isPullback (k := k) (R := R) sigma).w]
  rw [← Category.assoc (Proj.map f hf) (polynomialProjStructureMap R sigma), hbase]
  exact (polynomialProjBaseChange_isPullback
    (k := k) (R := R) sigma).isoPullback_inv_snd_assoc _

/-- The standard affine chart of polynomial `Proj` in which the coordinate `X i` is nonzero. -/
abbrev polynomialProjCoordinateChart
    (A : Type u) [CommRing A] (sigma : Type) (i : sigma) :=
  HomogeneousLocalization.Away (projectiveGrading A sigma) (MvPolynomial.X i)

/-- Coefficient extension on a standard homogeneous-coordinate chart. -/
noncomputable def polynomialProjCoordinateChartMap
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) (i : sigma) :
    polynomialProjCoordinateChart k sigma i →+*
      polynomialProjCoordinateChart R sigma i :=
  coordinateChartMap (k := k) (R := R) sigma i

/-- The polynomial `Proj` coefficient map restricts on each standard affine chart to the
homogeneous-localization coefficient map. -/
@[reassoc] theorem polynomialProjCoordinateChartMap_comp_awayι
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (i : sigma) :
    Spec.map (CommRingCat.ofHom
          (polynomialProjCoordinateChartMap (k := k) (R := R) sigma i)) ≫
        Proj.awayι (projectiveGrading k sigma) (MvPolynomial.X i)
          (coordinate_X_mem (A := k) i) one_pos =
      Proj.awayι (projectiveGrading R sigma) (MvPolynomial.X i)
          (coordinate_X_mem (A := R) i) one_pos ≫
        polynomialProjMap (k := k) (R := R) sigma := by
  exact coordinateChartMap_comp_awayι (k := k) (R := R) sigma i

/-- Specialize the base-changed projective space along a `k`-algebra retraction `R → k`. -/
noncomputable def polynomialProjSpecializationLift
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (φ : R →ₐ[k] k) :
    Proj (projectiveGrading k sigma) ⟶
      pullback (projectiveSpaceByCoordinates k sigma).structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
  polynomialProjMapOfRingHom sigma φ.toRingHom ≫
    (polynomialProjBaseChangeIso k R sigma).hom

@[reassoc (attr := simp)] theorem polynomialProjSpecializationLift_fst
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (φ : R →ₐ[k] k) :
    polynomialProjSpecializationLift k R sigma φ ≫
        pullback.fst (projectiveSpaceByCoordinates k sigma).structureMap
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) =
      𝟙 (Proj (projectiveGrading k sigma)) := by
  unfold polynomialProjSpecializationLift
  rw [Category.assoc, polynomialProjBaseChangeIso_hom_fst]
  change polynomialProjMapOfRingHom sigma φ.toRingHom ≫
      polynomialProjMap (k := k) (R := R) sigma =
    𝟙 (Proj (projectiveGrading k sigma))
  rw [polynomialProjMap_eq_mapOfRingHom]
  have h : φ.toRingHom.comp (algebraMap k R) = RingHom.id k := by
    ext x
    exact φ.commutes x
  calc
    polynomialProjMapOfRingHom sigma φ.toRingHom ≫
        polynomialProjMapOfRingHom sigma (algebraMap k R) =
      polynomialProjMapOfRingHom sigma
        (φ.toRingHom.comp (algebraMap k R)) :=
          (polynomialProjMapOfRingHom_comp sigma (algebraMap k R) φ.toRingHom).symm
    _ = 𝟙 (Proj (projectiveGrading k sigma)) := by
      rw [h]
      exact polynomialProjMapOfRingHom_id k sigma

@[reassoc] theorem polynomialProjSpecializationLift_snd
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (φ : R →ₐ[k] k) :
    polynomialProjSpecializationLift k R sigma φ ≫
        pullback.snd (projectiveSpaceByCoordinates k sigma).structureMap
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) =
      polynomialProjStructureMap k sigma ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  unfold polynomialProjSpecializationLift
  rw [Category.assoc, polynomialProjBaseChangeIso_hom_snd]
  exact polynomialProjMapOfRingHom_structureMap sigma φ.toRingHom

theorem polynomialProjSpecializedMap_irrelevant
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (φ : R →ₐ[k] k)
    (f : projectiveGrading R sigma →+*ᵍ projectiveGrading R sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading R sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading R sigma)).map f) :
    HomogeneousIdeal.irrelevant (projectiveGrading k sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading k sigma)).map
        ((polynomialCoefficientMap sigma φ.toRingHom).comp f |>.comp
          (polynomialCoefficientMap sigma (algebraMap k R))) := by
  exact HomogeneousIdeal.irrelevant_le_map_comp
    (polynomialCoefficientMap_irrelevant sigma (algebraMap k R))
    (HomogeneousIdeal.irrelevant_le_map_comp hf
      (polynomialCoefficientMap_irrelevant sigma φ.toRingHom))

/-- The endomorphism of projective space obtained by specializing a graded `R`-linear
substitution through `φ : R →ₐ[k] k`. -/
noncomputable def polynomialProjSpecializedMap
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (φ : R →ₐ[k] k)
    (f : projectiveGrading R sigma →+*ᵍ projectiveGrading R sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading R sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading R sigma)).map f) :
    Proj (projectiveGrading k sigma) ⟶ Proj (projectiveGrading k sigma) :=
  Proj.map
    ((polynomialCoefficientMap sigma φ.toRingHom).comp f |>.comp
      (polynomialCoefficientMap sigma (algebraMap k R)))
    (polynomialProjSpecializedMap_irrelevant k R sigma φ f hf)

@[simp]
theorem polynomialProjSpecializedMap_eq_projMap
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (φ : R →ₐ[k] k)
    (f : projectiveGrading R sigma →+*ᵍ projectiveGrading R sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading R sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading R sigma)).map f) :
    polynomialProjSpecializedMap k R sigma φ f hf =
      Proj.map
        ((polynomialCoefficientMap sigma φ.toRingHom).comp f |>.comp
          (polynomialCoefficientMap sigma (algebraMap k R)))
        (polynomialProjSpecializedMap_irrelevant k R sigma φ f hf) :=
  by
    unfold polynomialProjSpecializedMap
    congr 1

/-- Specializing the family induced by `f` is the `Proj.map` of the coefficientwise
specialized graded substitution. -/
theorem polynomialProjFamilyMap_specialization
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (φ : R →ₐ[k] k)
    (f : projectiveGrading R sigma →+*ᵍ projectiveGrading R sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading R sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading R sigma)).map f) :
    polynomialProjSpecializationLift k R sigma φ ≫
        polynomialProjFamilyMap k R sigma f hf =
      polynomialProjSpecializedMap k R sigma φ f hf := by
  unfold polynomialProjSpecializationLift polynomialProjFamilyMap
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change polynomialProjMapOfRingHom sigma φ.toRingHom ≫ Proj.map f hf ≫
      polynomialProjMap (k := k) (R := R) sigma =
    polynomialProjSpecializedMap k R sigma φ f hf
  rw [polynomialProjMap_eq_mapOfRingHom]
  unfold polynomialProjMapOfRingHom polynomialProjSpecializedMap
  rw [← Category.assoc]
  rw [← Proj.map_comp, ← Proj.map_comp]

/-- Rational-point formula for specialization of a projective family. -/
theorem polynomialProjFamilyMap_specialization_point
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (φ : R →ₐ[k] k)
    (f : projectiveGrading R sigma →+*ᵍ projectiveGrading R sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading R sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading R sigma)).map f)
    (x : Spec (.of k) ⟶ Proj (projectiveGrading k sigma)) :
    x ≫ polynomialProjSpecializationLift k R sigma φ ≫
        polynomialProjFamilyMap k R sigma f hf =
      x ≫ polynomialProjSpecializedMap k R sigma φ f hf := by
  simpa only [Category.assoc, projectiveSpaceByCoordinates_toScheme] using
    congrArg (fun g ↦ x ≫ g)
      (polynomialProjFamilyMap_specialization k R sigma φ f hf)

theorem polynomialProjSpecializedMap_overBase
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (sigma : Type) [Finite sigma] (φ : R →ₐ[k] k)
    (f : projectiveGrading R sigma →+*ᵍ projectiveGrading R sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading R sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading R sigma)).map f)
    (hbase : Proj.map f hf ≫ polynomialProjStructureMap R sigma =
      polynomialProjStructureMap R sigma) :
    polynomialProjSpecializedMap k R sigma φ f hf ≫
        (projectiveSpaceByCoordinates k sigma).structureMap =
      (projectiveSpaceByCoordinates k sigma).structureMap := by
  rw [← polynomialProjFamilyMap_specialization k R sigma φ f hf]
  change polynomialProjSpecializationLift k R sigma φ ≫
      (polynomialProjFamilyMap k R sigma f hf ≫
        (projectiveSpaceByCoordinates k sigma).structureMap) = _
  rw [polynomialProjFamilyMap_overBase k R sigma f hf hbase]
  rw [← Category.assoc, polynomialProjSpecializationLift_snd]
  change (polynomialProjStructureMap k sigma ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) =
    polynomialProjStructureMap k sigma
  rw [Category.assoc, ← Spec.map_comp]
  have hcomp : φ.toRingHom.comp (algebraMap k R) = RingHom.id k := by
    ext x
    exact φ.commutes x
  change polynomialProjStructureMap k sigma ≫
      Spec.map (CommRingCat.ofHom (φ.toRingHom.comp (algebraMap k R))) =
    polynomialProjStructureMap k sigma
  rw [hcomp]
  have hid : CommRingCat.ofHom (RingHom.id k) = 𝟙 (CommRingCat.of k) := by
    ext x
    rfl
  rw [hid, Spec.map_id, Category.comp_id]

end Theory.AlgebraicGroup.Variety.Geometric
