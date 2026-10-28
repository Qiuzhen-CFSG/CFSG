module

public import Theory.AlgebraicGroup.RootSystems.ClassicalSymplecticModel
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.IsogenyRootDataTransportCore

/-!
# The projective symplectic root model

This module constructs the type-C root model on the actual central quotient of
the standard symplectic carrier.  The quotient is built from its finite center
with a bijective identity differential and surjective invariant-coordinate
pullback.  These properties let each explicit symplectic root curve descend to
a closed one-parameter subgroup of the quotient.

The quotient image of the diagonal torus is maximal and self-centralizing.
Every quotient torus root lifts through the bijective differential to a
nontrivial source tangent weight, so the explicit projected root curves exhaust
the quotient roots.  Their parameter functions descend without a Frobenius
power, giving exact character pullback.  The source type-C combinatorics and
cocharacters then assemble an actual based root-pairing realization on the
projective carrier.  Semisimplicity is inherited directly along the quotient
isogeny.

The construction follows the standard symplectic central quotient and root
subgroups used in GLS, Part I, Chapter A, Sections 1.9--1.10.
-/

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

noncomputable section

private structure ProjectiveSymplecticQuotientData (m : ℕ) where
  projective : Variety k
  group : AlgebraicGroup projective
  quotient :
    letI := (standardSymplecticClosedSubgroup (k := k) m).carrierAlgebraicGroup
    letI := group
    AlgebraicGroup.Morphism
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety projective
  quotient_isogeny :
    letI := (standardSymplecticClosedSubgroup (k := k) m).carrierAlgebraicGroup
    letI := group
    IsIsogeny quotient
  quotient_kernel :
    letI := (standardSymplecticClosedSubgroup (k := k) m).carrierAlgebraicGroup
    letI := group
    quotient.kernel = Subgroup.center
      (Variety.Point
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
  quotient_universal :
    letI := (standardSymplecticClosedSubgroup (k := k) m).carrierAlgebraicGroup
    letI := group
    ∀ {H : Variety k} [AlgebraicGroup H]
      (f : AlgebraicGroup.Morphism
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety H),
      Subgroup.center
          (Variety.Point
            (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) ≤
        f.kernel →
      ∃! r : AlgebraicGroup.Morphism projective H, r.comp quotient = f
  point_equiv :
    letI := (standardSymplecticClosedSubgroup (k := k) m).carrierAlgebraicGroup
    letI := group
    Variety.Point projective ≃*
      Variety.Point
          (standardSymplecticClosedSubgroup (k := k) m).carrierVariety ⧸
        Subgroup.center
          (Variety.Point
            (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
  point_equiv_quotient :
    letI := (standardSymplecticClosedSubgroup (k := k) m).carrierAlgebraicGroup
    letI := group
    ∀ x, point_equiv (quotient.onPoints x) =
      QuotientGroup.mk'
        (Subgroup.center
          (Variety.Point
            (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)) x
  differential_bijective :
    letI := (standardSymplecticClosedSubgroup (k := k) m).carrierAlgebraicGroup
    letI := group
    Function.Bijective (identityTangentMorphismLinearMap quotient)
  invariant_coordinate_descends :
    letI := (standardSymplecticClosedSubgroup (k := k) m).carrierAlgebraicGroup
    letI := group
    ∀ F : Variety.PolynomialFunction
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety,
      F ∈ AlgebraicGroup.rightInvariantCoordinateRing
        ((ClosedSubgroup.top (G :=
          (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)).centralizer) →
      ∃ A : Variety.PolynomialFunction projective,
        Variety.PolynomialFunction.pullback quotient.toVariety A = F

private theorem projectiveSymplecticQuotientData_exists (m : ℕ) :
    Nonempty (ProjectiveSymplecticQuotientData (k := k) m) := by
  let S := standardSymplecticClosedSubgroup (k := k) m
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  let B := standardSymplecticBilinForm (k := k) m
  let e : Variety.Point S.carrierVariety ≃*
      bilinearIsometrySubgroup B :=
    standardSymplecticClosedSubgroupPoints (k := k) m
  letI : Finite (Subgroup.center (Variety.Point S.carrierVariety)) :=
    finite_center_of_mulEquiv_standardSymplectic_all m e
  let Z : ClosedSubgroup S.carrierVariety :=
    ClosedSubgroup.ofSubgroup
      (Subgroup.center (Variety.Point S.carrierVariety))
      (isZariskiClosed_of_finite
        (Set.toFinite (Subgroup.center (Variety.Point S.carrierVariety) :
          Set (Variety.Point S.carrierVariety))))
  have hZnormal : Z.toSubgroup.Normal := by
    change (Subgroup.center (Variety.Point S.carrierVariety)).Normal
    infer_instance
  obtain ⟨P⟩ :=
    Bor1.ClosedSubgroup.chevalleyWeightBlockExactDifferentialKernel_nonempty
      Z hZnormal
  letI : AddCommGroup P.V := P.addCommGroup
  letI : Module k P.V := P.module
  letI : FiniteDimensional k P.V := P.finiteDimensional
  let Q := P.morphism.imageClosedSubgroup
  letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
  obtain ⟨q, hqsurj, hqker, hqdfker, hqdfsurj⟩ :=
    Bor1.ExactKernelDifferentialRationalRepresentation.closedImageProjection_exactTangentKernel_surjective_exists
      Z P
  have hqpull : Function.Surjective
      (q.pullbackToRightInvariantCoordinateRing Z (by rw [hqker])) :=
    Bor1.pullbackToRightInvariantCoordinateRing_surjective
      Z q hqsurj hqker hqdfsurj
  letI : AlgebraicGroup Z.carrierVariety := Z.carrierAlgebraicGroup
  letI : Finite Z.toSubgroup := by
    change Finite (Subgroup.center (Variety.Point S.carrierVariety))
    infer_instance
  have hZpoints : Finite (Variety.Point Z.carrierVariety) :=
    (Equiv.finite_iff Z.pointEquiv).mpr inferInstance
  have hZdim : Variety.dimension Z.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points Z.carrierVariety).2 hZpoints
  have hZfinrank : Module.finrank k
      (IdentityPointDerivation Z.carrierVariety) = 0 := by
    rw [Bor1.identityPointDerivation_finrank_eq_dimension, hZdim]
    simp
  have hZzero : ∀ D : IdentityPointDerivation Z.carrierVariety, D = 0 :=
    finrank_zero_iff_forall_zero.mp hZfinrank
  have hqdfkerBot :
      LinearMap.ker (identityTangentMorphismLinearMap q) = ⊥ := by
    have hqdfker' :
        LinearMap.ker (identityTangentMorphismLinearMap q) =
          LinearMap.range (identityTangentMorphismLinearMap Z.inclusion) := by
      simpa only [Bor1.identityTangentMorphismLinearMap,
        Theory.AlgebraicGroup.identityTangentMorphismLinearMap] using hqdfker
    rw [hqdfker']
    apply le_antisymm
    · rintro D ⟨E, rfl⟩
      rw [hZzero E, map_zero]
      exact Submodule.zero_mem _
    · exact bot_le
  have hqdfinj : Function.Injective (identityTangentMorphismLinearMap q) :=
    LinearMap.ker_eq_bot.mp hqdfkerBot
  have hqdfsurj' :
      Function.Surjective (identityTangentMorphismLinearMap q) := by
    simpa only [Bor1.identityTangentMorphismLinearMap,
      Theory.AlgebraicGroup.identityTangentMorphismLinearMap] using hqdfsurj
  have hZcenter : Z =
      (ClosedSubgroup.top (G := S.carrierVariety)).centralizer := by
    apply SetLike.coe_injective
    change (Subgroup.center (Variety.Point S.carrierVariety) :
      Set (Variety.Point S.carrierVariety)) =
      Subgroup.centralizer
        ((⊤ : Subgroup (Variety.Point S.carrierVariety)) :
          Set (Variety.Point S.carrierVariety))
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
  have hkernelCenter : q.kernel =
      Subgroup.center (Variety.Point S.carrierVariety) := by
    rw [hqker]
    rfl
  have hqfinite : Finite q.kernel := by
    rw [hkernelCenter]
    infer_instance
  have hqiso : IsIsogeny q := ⟨hqsurj, hqfinite⟩
  have hfactor :
      ∀ {H : Variety k} [AlgebraicGroup H]
        (f : AlgebraicGroup.Morphism S.carrierVariety H),
        Subgroup.center (Variety.Point S.carrierVariety) ≤ f.kernel →
          ∃! r : AlgebraicGroup.Morphism Q.carrierVariety H, r.comp q = f := by
    intro H _ f hf
    apply Bor1.quotient_universal_of_surjective_invariant_pullback
      Z hZnormal q hqsurj hqker hqpull (inferInstance : AlgebraicGroup H) f
    change Subgroup.center (Variety.Point S.carrierVariety) ≤ f.kernel
    exact hf
  let e0 : (Variety.Point S.carrierVariety ⧸ q.kernel) ≃*
      Variety.Point Q.carrierVariety :=
    QuotientGroup.quotientKerEquivOfSurjective q.onPoints hqsurj
  let e1 : (Variety.Point S.carrierVariety ⧸
      Subgroup.center (Variety.Point S.carrierVariety)) ≃*
      (Variety.Point S.carrierVariety ⧸ q.kernel) :=
    QuotientGroup.quotientMulEquivOfEq hkernelCenter.symm
  let eQ : Variety.Point Q.carrierVariety ≃*
      Variety.Point S.carrierVariety ⧸
        Subgroup.center (Variety.Point S.carrierVariety) :=
    (e1.trans e0).symm
  have heQ (x : Variety.Point S.carrierVariety) :
      eQ (q.onPoints x) = QuotientGroup.mk'
        (Subgroup.center (Variety.Point S.carrierVariety)) x := by
    change e1.symm (e0.symm (q.onPoints x)) = _
    apply e1.injective
    rw [e1.apply_symm_apply]
    apply e0.injective
    rw [e0.apply_symm_apply]
    change e0 (QuotientGroup.mk' q.kernel x) = q.onPoints x
    exact QuotientGroup.kerLift_mk q.onPoints x
  refine ⟨{
    projective := Q.carrierVariety
    group := Q.carrierAlgebraicGroup
    quotient := q
    quotient_isogeny := hqiso
    quotient_kernel := hkernelCenter
    quotient_universal := hfactor
    point_equiv := eQ
    point_equiv_quotient := heQ
    differential_bijective := ⟨hqdfinj, hqdfsurj'⟩
    invariant_coordinate_descends := ?_
  }⟩
  intro F hF
  have hFZ : F ∈ AlgebraicGroup.rightInvariantCoordinateRing Z := by
    rw [hZcenter]
    exact hF
  obtain ⟨A, hA⟩ := hqpull ⟨F, hFZ⟩
  exact ⟨A, congrArg Subtype.val hA⟩

private noncomputable def projectiveSymplecticTorus
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    letI := C.group
    ClosedSubgroup C.projective := by
  letI := C.group
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact (C.quotient.comp
    (symplecticDiagonalTorus (k := k) m).inclusion).imageClosedSubgroup

private noncomputable def projectiveSymplecticRootMorphism
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    AlgebraicGroup.Morphism (KPlus k) C.projective := by
  letI := C.group
  exact C.quotient.comp (symplecticRootMorphism (k := k) m r)

private noncomputable def projectiveSymplecticRootSubgroup
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    ClosedSubgroup C.projective := by
  letI := C.group
  exact (projectiveSymplecticRootMorphism (k := k) m C r).imageClosedSubgroup

private theorem projectiveSymplecticRoot_parameter_exists
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    ∃ A : Variety.PolynomialFunction C.projective,
      ∀ x : Variety.Point (KPlus k),
        A ((projectiveSymplecticRootMorphism (k := k) m C r).onPoints x) =
          x.val PUnit.unit := by
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  let X := symplecticRootSubgroup (k := k) m r
  letI := T.carrierAlgebraicGroup
  letI := X.carrierAlgebraicGroup
  have hX : IsTorusRootSubgroup T X :=
    ⟨symplecticRootSubgroup_invariant (k := k) m r,
      symplecticRootSubgroup_isOneParameter (k := k) m r⟩
  have hchi : symplecticRootWeight (k := k) m r ≠ 1 :=
    hX.rootWeight_ne_one_of_centralizer_eq
      (symplecticDiagonalTorus_isSubtorus (k := k) m)
      (symplecticDiagonalTorus_centralizer_eq (k := k) m)
      (symplecticRootWeight (k := k) m r)
      (symplecticRootWeight_equation (k := k) m r)
  obtain ⟨F, hFinv, hF⟩ := rootParameter_exists_centerInvariantPolynomial
    T X (symplecticRootWeight (k := k) m r)
    (symplecticRootWeight_equation (k := k) m r) hchi
    (symplecticRootParametrization (k := k) m r)
  obtain ⟨A, hA⟩ := C.invariant_coordinate_descends F hFinv
  refine ⟨A, ?_⟩
  intro x
  let a : k := x.val PUnit.unit
  have hx : x = kPlusPoint a := (kPlusPoint_coordinate x).symm
  change A ((projectiveSymplecticRootMorphism (k := k) m C r).onPoints x) = a
  calc
    A ((projectiveSymplecticRootMorphism (k := k) m C r).onPoints x) =
        A ((projectiveSymplecticRootMorphism (k := k) m C r).onPoints
          (kPlusPoint a)) := congrArg
            (fun z => A ((projectiveSymplecticRootMorphism (k := k) m C r).onPoints z)) hx
    _ = a := by
      let z := (symplecticRootMorphism (k := k) m r).onPoints (kPlusPoint a)
      calc
        A (C.quotient.onPoints z) = F z := by
          exact congrArg (fun G : Variety.PolynomialFunction
            (standardSymplecticClosedSubgroup (k := k) m).carrierVariety => G z) hA
        _ = a := by
          dsimp only [z]
          rw [symplecticRootMorphism_kPlusPoint]
          rw [← symplecticRootParametrization_include_value]
          exact hF a

private theorem projectiveSymplecticRootMorphism_injective
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    Function.Injective
      (projectiveSymplecticRootMorphism (k := k) m C r).onPoints := by
  letI := C.group
  obtain ⟨A, hA⟩ := projectiveSymplecticRoot_parameter_exists
    (k := k) m C r
  intro x y hxy
  apply Variety.Point.ext
  funext i
  rw [show i = PUnit.unit by rfl]
  rw [← hA x, ← hA y, hxy]

private theorem projectiveSymplecticRootMorphism_coordinate_preimage
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    ∀ c : (KPlus k).Coordinates,
      ∃ A : Variety.PolynomialFunction C.projective,
        Variety.PolynomialFunction.pullback
            (projectiveSymplecticRootMorphism (k := k) m C r).toVariety A =
          Variety.PolynomialFunction.ofPolynomial (KPlus k)
            (MvPolynomial.X c) := by
  letI := C.group
  intro c
  obtain ⟨A, hA⟩ := projectiveSymplecticRoot_parameter_exists
    (k := k) m C r
  refine ⟨A, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  change A ((projectiveSymplecticRootMorphism (k := k) m C r).onPoints x) =
    evalPolynomial x.val (MvPolynomial.X c)
  rw [hA]
  rw [evalPolynomial_X]

private theorem projectiveSymplecticRootMorphism_mem_rootSubgroup
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) (x : Variety.Point (KPlus k)) :
    letI := C.group
    (projectiveSymplecticRootMorphism (k := k) m C r).onPoints x ∈
      projectiveSymplecticRootSubgroup (k := k) m C r := by
  letI := C.group
  exact ⟨x, rfl⟩

private noncomputable def projectiveSymplecticRootParametrization
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    let Y := projectiveSymplecticRootSubgroup (k := k) m C r
    letI := Y.carrierAlgebraicGroup
    OneParameterParametrization Y.carrierVariety := by
  letI := C.group
  let Y := projectiveSymplecticRootSubgroup (k := k) m C r
  letI := Y.carrierAlgebraicGroup
  exact Classical.choose
    (AlgebraicGroup.Morphism.iso_imageClosedSubgroup_of_coordinate_preimage
      (projectiveSymplecticRootMorphism (k := k) m C r)
      (projectiveSymplecticRootMorphism_injective (k := k) m C r)
      (projectiveSymplecticRootMorphism_coordinate_preimage (k := k) m C r))

private theorem projectiveSymplecticRootParametrization_hom
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    let Y := projectiveSymplecticRootSubgroup (k := k) m C r
    letI := Y.carrierAlgebraicGroup
    (projectiveSymplecticRootParametrization (k := k) m C r).hom =
      AlgebraicGroup.Morphism.codRestrictClosedSubgroup
        (projectiveSymplecticRootMorphism (k := k) m C r)
        Y (projectiveSymplecticRootMorphism_mem_rootSubgroup
          (k := k) m C r) := by
  letI := C.group
  let Y := projectiveSymplecticRootSubgroup (k := k) m C r
  letI := Y.carrierAlgebraicGroup
  exact Classical.choose_spec
    (AlgebraicGroup.Morphism.iso_imageClosedSubgroup_of_coordinate_preimage
      (projectiveSymplecticRootMorphism (k := k) m C r)
      (projectiveSymplecticRootMorphism_injective (k := k) m C r)
      (projectiveSymplecticRootMorphism_coordinate_preimage (k := k) m C r))

private theorem projectiveSymplecticRootParametrization_include_value
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) (a : k) :
    letI := C.group
    let Y := projectiveSymplecticRootSubgroup (k := k) m C r
    letI := Y.carrierAlgebraicGroup
    Y.includePoint
        ((projectiveSymplecticRootParametrization (k := k) m C r).value a) =
      C.quotient.onPoints (symplecticRootPoint (k := k) m r a) := by
  letI := C.group
  let Y := projectiveSymplecticRootSubgroup (k := k) m C r
  letI := Y.carrierAlgebraicGroup
  change Y.inclusion.onPoints
      ((projectiveSymplecticRootParametrization (k := k) m C r).hom.onPoints
        (kPlusPoint a)) = _
  rw [projectiveSymplecticRootParametrization_hom]
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  rfl

private theorem projectiveSymplecticRootSubgroup_eq_source_image
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    let X := symplecticRootSubgroup (k := k) m r
    letI := X.carrierAlgebraicGroup
    (C.quotient.comp
      X.inclusion).imageClosedSubgroup =
        projectiveSymplecticRootSubgroup (k := k) m C r := by
  letI := C.group
  let X := symplecticRootSubgroup (k := k) m r
  letI := X.carrierAlgebraicGroup
  let x := symplecticRootParametrization (k := k) m r
  apply SetLike.coe_injective
  ext y
  change y ∈ (C.quotient.comp X.inclusion).image ↔
    y ∈ (projectiveSymplecticRootMorphism (k := k) m C r).image
  constructor
  · rintro ⟨z, rfl⟩
    let w := x.inv.onPoints z
    refine ⟨w, ?_⟩
    change C.quotient.onPoints ((symplecticRootMorphism (k := k) m r).onPoints w) =
      C.quotient.onPoints (X.inclusion.onPoints z)
    congr 1
    have hx := congrArg X.inclusion.onPoints (x.inv_hom_id z)
    change X.inclusion.onPoints (x.hom.onPoints w) = X.inclusion.onPoints z at hx
    rw [symplecticRootParametrization_hom] at hx
    have hinclude :=
      (symplecticRootMorphism (k := k) m r).codRestrictClosedSubgroup_inclusion_apply
        X (fun y => ⟨y, rfl⟩) w
    exact hinclude.symm.trans hx
  · rintro ⟨z, rfl⟩
    refine ⟨x.hom.onPoints z, ?_⟩
    change C.quotient.onPoints (X.inclusion.onPoints (x.hom.onPoints z)) =
      C.quotient.onPoints ((symplecticRootMorphism (k := k) m r).onPoints z)
    congr 1
    rw [symplecticRootParametrization_hom]
    exact
      (symplecticRootMorphism (k := k) m r).codRestrictClosedSubgroup_inclusion_apply
        X (fun y => ⟨y, rfl⟩) z

private theorem projectiveSymplecticRootSubgroup_isTorusRootSubgroup
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    IsTorusRootSubgroup
      (projectiveSymplecticTorus (k := k) m C)
      (projectiveSymplecticRootSubgroup (k := k) m C r) := by
  letI := C.group
  constructor
  · rw [← projectiveSymplecticRootSubgroup_eq_source_image]
    exact morphism_image_rootSubgroup_invariant C.quotient
      (symplecticDiagonalTorus (k := k) m)
      (symplecticRootSubgroup (k := k) m r)
      (symplecticRootSubgroup_invariant (k := k) m r)
  · exact ⟨projectiveSymplecticRootParametrization (k := k) m C r⟩

private noncomputable def projectiveSymplecticRootWeight
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    TorusWeight (projectiveSymplecticTorus (k := k) m C) := by
  letI := C.group
  exact Classical.choose (existsUnique_rootWeight_of_isTorusRootSubgroup
    (projectiveSymplecticTorus (k := k) m C)
    (projectiveSymplecticRootSubgroup (k := k) m C r)
    (projectiveSymplecticRootSubgroup_isTorusRootSubgroup (k := k) m C r))

private theorem projectiveSymplecticRootWeight_equation
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    RootWeightEquation
      (projectiveSymplecticTorus (k := k) m C)
      (projectiveSymplecticRootSubgroup (k := k) m C r)
      (projectiveSymplecticRootWeight (k := k) m C r) := by
  letI := C.group
  exact (Classical.choose_spec (existsUnique_rootWeight_of_isTorusRootSubgroup
    (projectiveSymplecticTorus (k := k) m C)
    (projectiveSymplecticRootSubgroup (k := k) m C r)
    (projectiveSymplecticRootSubgroup_isTorusRootSubgroup (k := k) m C r))).1

private noncomputable def projectiveSymplecticRootImageWitness
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    let X := symplecticRootSubgroup (k := k) m r
    letI := X.carrierAlgebraicGroup
    IsogenyRootImageWitness C.quotient
      X
      (projectiveSymplecticRootSubgroup (k := k) m C r) := by
  letI := C.group
  let X := symplecticRootSubgroup (k := k) m r
  letI := X.carrierAlgebraicGroup
  let Y := projectiveSymplecticRootSubgroup (k := k) m C r
  letI := Y.carrierAlgebraicGroup
  exact {
    image_eq := projectiveSymplecticRootSubgroup_eq_source_image (k := k) m C r
    source := symplecticRootParametrization (k := k) m r
    target := projectiveSymplecticRootParametrization (k := k) m C r
    polynomial := Polynomial.X
    polynomial_ne_zero := by simp
    parameter_eq := by
      intro a
      rw [Polynomial.eval_X]
      rw [symplecticRootParametrization_include_value]
      rw [projectiveSymplecticRootParametrization_include_value]
  }

private theorem projectiveSymplecticTorusMorphism_mem_image
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (x : Variety.Point (symplecticDiagonalTorus (k := k) m).carrierVariety) :
    letI := C.group
    let T := symplecticDiagonalTorus (k := k) m
    letI := T.carrierAlgebraicGroup
    (C.quotient.comp
      (symplecticDiagonalTorus (k := k) m).inclusion).onPoints x ∈
        projectiveSymplecticTorus (k := k) m C := by
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  letI := T.carrierAlgebraicGroup
  exact ⟨x, rfl⟩

private noncomputable def projectiveSymplecticTorusMorphism
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    letI := C.group
    let T := symplecticDiagonalTorus (k := k) m
    letI := T.carrierAlgebraicGroup
    let T' := projectiveSymplecticTorus (k := k) m C
    letI := T'.carrierAlgebraicGroup
    AlgebraicGroup.Morphism
      T.carrierVariety T'.carrierVariety := by
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  letI := T.carrierAlgebraicGroup
  let T' := projectiveSymplecticTorus (k := k) m C
  letI := T'.carrierAlgebraicGroup
  exact (C.quotient.comp T.inclusion).codRestrictClosedSubgroup T'
    (projectiveSymplecticTorusMorphism_mem_image (k := k) m C)

private theorem projectiveSymplecticTorusMorphism_surjective
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    letI := C.group
    let T := symplecticDiagonalTorus (k := k) m
    letI := T.carrierAlgebraicGroup
    let T' := projectiveSymplecticTorus (k := k) m C
    letI := T'.carrierAlgebraicGroup
    Function.Surjective
      (projectiveSymplecticTorusMorphism (k := k) m C).onPoints := by
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  letI := T.carrierAlgebraicGroup
  let T' := projectiveSymplecticTorus (k := k) m C
  letI := T'.carrierAlgebraicGroup
  exact (C.quotient.comp T.inclusion).codRestrictImageClosedSubgroup_surjective
    (projectiveSymplecticTorusMorphism_mem_image (k := k) m C)

private theorem projectiveSymplecticTorusMorphism_include_apply
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (s : Variety.Point (symplecticDiagonalTorus (k := k) m).carrierVariety) :
    letI := C.group
    let T := symplecticDiagonalTorus (k := k) m
    letI := T.carrierAlgebraicGroup
    let T' := projectiveSymplecticTorus (k := k) m C
    letI := T'.carrierAlgebraicGroup
    (projectiveSymplecticTorus (k := k) m C).includePoint
        ((projectiveSymplecticTorusMorphism (k := k) m C).onPoints s) =
      C.quotient.onPoints
        ((symplecticDiagonalTorus (k := k) m).includePoint s) := by
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  letI := T.carrierAlgebraicGroup
  let T' := projectiveSymplecticTorus (k := k) m C
  letI := T'.carrierAlgebraicGroup
  exact
    (C.quotient.comp
      (symplecticDiagonalTorus (k := k) m).inclusion).codRestrictClosedSubgroup_inclusion_apply
        (projectiveSymplecticTorus (k := k) m C)
        (projectiveSymplecticTorusMorphism_mem_image (k := k) m C) s

private theorem projectiveSymplecticTorus_isMaximalTorus
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    letI := C.group
    IsMaximalTorus (projectiveSymplecticTorus (k := k) m C) := by
  letI := C.group
  exact isogenyImageTorus_isMaximalTorus C.quotient C.quotient_isogeny
    (symplecticDiagonalTorus (k := k) m)
    (symplecticDiagonalTorus_isMaximalTorus (k := k) m)

private theorem projectiveSymplecticTorus_centralizer_eq
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    letI := C.group
    (projectiveSymplecticTorus (k := k) m C).centralizer.toSubgroup =
      (projectiveSymplecticTorus (k := k) m C).toSubgroup := by
  let S := standardSymplecticClosedSubgroup (k := k) m
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let T' := projectiveSymplecticTorus (k := k) m C
  letI : AlgebraicGroup T'.carrierVariety := T'.carrierAlgebraicGroup
  let e : Variety.Point S.carrierVariety ≃*
      bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m) :=
    standardSymplecticClosedSubgroupPoints (k := k) m
  letI : Finite (Subgroup.center (Variety.Point S.carrierVariety)) :=
    finite_center_of_mulEquiv_standardSymplectic_all m e
  apply SetLike.coe_injective
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := C.quotient_isogeny.1 y
    let commutatorSlice : Variety.Morphism T.carrierVariety S.carrierVariety :=
      (AlgebraicGroup.commutatorMorphism S.carrierVariety).comp
        ((Variety.Morphism.const T.carrierVariety S.carrierVariety x).pair
          T.inclusion.toVariety)
    have hslice (t : Variety.Point T.carrierVariety) :
        commutatorSlice.toFun t =
          x * T.includePoint t * x⁻¹ * (T.includePoint t)⁻¹ := by
      change (AlgebraicGroup.commutatorMorphism S.carrierVariety).toFun
        ((Variety.prodPointEquiv S.carrierVariety S.carrierVariety).symm
          (x, T.includePoint t)) = _
      exact AlgebraicGroup.commutatorMorphism_apply S.carrierVariety
        x (T.includePoint t)
    have hrange : Set.range commutatorSlice.toFun ⊆
        (Subgroup.center (Variety.Point S.carrierVariety) :
          Set (Variety.Point S.carrierVariety)) := by
      rintro z ⟨t, rfl⟩
      rw [← C.quotient_kernel]
      change C.quotient.onPoints (commutatorSlice.toFun t) = 1
      rw [hslice]
      simp only [map_mul, map_inv]
      have hqt : C.quotient.onPoints (T.includePoint t) ∈ T'.toSubgroup :=
        ⟨t, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hy _ hqt
      rw [hx, ← hcomm]
      group
    have hrangeFinite : (Set.range commutatorSlice.toFun).Finite :=
      (Set.toFinite
        (Subgroup.center (Variety.Point S.carrierVariety) :
          Set (Variety.Point S.carrierVariety))).subset hrange
    have hrangeSubsingleton := connected_finite_morphism_range_subsingleton
      commutatorSlice
      (symplecticDiagonalTorus_isSubtorus (k := k) m).isConnected
      hrangeFinite
    have hxcentral : x ∈ T.centralizer.toSubgroup := by
      change x ∈ Subgroup.centralizer
        (T.toSubgroup : Set (Variety.Point S.carrierVariety))
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      let t : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨z, hz⟩
      have ht : T.includePoint t = z := by
        change (T.pointEquiv t).val = z
        simp [t]
      have h := hrangeSubsingleton
        (Set.mem_range_self t)
        (Set.mem_range_self (1 : Variety.Point T.carrierVariety))
      have h' : x * z * x⁻¹ * z⁻¹ = 1 := by
        calc
          x * z * x⁻¹ * z⁻¹ = commutatorSlice.toFun t := by rw [hslice, ht]
          _ = commutatorSlice.toFun 1 := h
          _ = 1 := by
            rw [hslice]
            have hone : T.includePoint
                (1 : Variety.Point T.carrierVariety) = 1 :=
              map_one T.inclusion.onPoints
            rw [hone]
            group
      have hcomm : x * z = z * x := by
        calc
          x * z = (x * z * x⁻¹ * z⁻¹) * (z * x) := by group
          _ = z * x := by rw [h', one_mul]
      exact hcomm.symm
    have hxT : x ∈ T.toSubgroup := by
      rw [← symplecticDiagonalTorus_centralizer_eq (k := k) m]
      exact hxcentral
    let xt : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨x, hxT⟩
    refine ⟨xt, ?_⟩
    change C.quotient.onPoints (T.includePoint xt) = y
    have hxt : T.includePoint xt = x := by
      change (T.pointEquiv xt).val = x
      simp [xt]
    rw [hxt, hx]
  · intro hy
    change y ∈ Subgroup.centralizer
      (T'.toSubgroup : Set (Variety.Point C.projective))
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    let yt : Variety.Point T'.carrierVariety := T'.pointEquiv.symm ⟨y, hy⟩
    let zt : Variety.Point T'.carrierVariety := T'.pointEquiv.symm ⟨z, hz⟩
    have hcomm :=
      (projectiveSymplecticTorus_isMaximalTorus (k := k) m C).1.isMulCommutative
    rw [isMulCommutative_iff] at hcomm
    have h := congrArg T'.inclusion.onPoints (hcomm zt yt)
    simp only [map_mul] at h
    have hyt : T'.includePoint yt = y := by
      change (T'.pointEquiv yt).val = y
      simp [yt]
    have hzt : T'.includePoint zt = z := by
      change (T'.pointEquiv zt).val = z
      simp [zt]
    change T'.includePoint zt * T'.includePoint yt =
      T'.includePoint yt * T'.includePoint zt at h
    rw [hyt, hzt] at h
    exact h

private theorem projectiveSymplecticRootWeight_pullback
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : TypeCRootIndex m) :
    letI := C.group
    let T := symplecticDiagonalTorus (k := k) m
    letI := T.carrierAlgebraicGroup
    let T' := projectiveSymplecticTorus (k := k) m C
    letI := T'.carrierAlgebraicGroup
    TorusCharacter.pullback (projectiveSymplecticTorusMorphism (k := k) m C)
        (projectiveSymplecticRootWeight (k := k) m C r) =
      symplecticRootWeight (k := k) m r := by
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  letI := T.carrierAlgebraicGroup
  let T' := projectiveSymplecticTorus (k := k) m C
  letI := T'.carrierAlgebraicGroup
  let X := symplecticRootSubgroup (k := k) m r
  letI := X.carrierAlgebraicGroup
  let Y := projectiveSymplecticRootSubgroup (k := k) m C r
  letI := Y.carrierAlgebraicGroup
  have h :=
    (projectiveSymplecticRootImageWitness (k := k) m C r).weight_pullback_eq_pow_natDegree
      (projectiveSymplecticTorusMorphism (k := k) m C)
      (projectiveSymplecticTorusMorphism_include_apply (k := k) m C)
      (symplecticRootWeight (k := k) m r)
      (projectiveSymplecticRootWeight (k := k) m C r)
      (symplecticRootWeight_equation (k := k) m r)
      (projectiveSymplecticRootWeight_equation (k := k) m C r)
  simpa [projectiveSymplecticRootImageWitness] using h

omit [IsAlgClosed k] in
private theorem projectiveSymplecticDifferential_conjugation_naturality
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (g : Variety.Point G) :
    (identityTangentMorphismLinearMap f).comp
        (identityTangentConjugationLinearMap G g) =
      (identityTangentConjugationLinearMap H (f.onPoints g)).comp
        (identityTangentMorphismLinearMap f) := by
  ext D a
  change D ((AlgebraicGroup.conjugationByMorphism G g).pullbackAlgHom
      (f.toVariety.pullbackAlgHom a)) =
    D (f.toVariety.pullbackAlgHom
      ((AlgebraicGroup.conjugationByMorphism H (f.onPoints g)).pullbackAlgHom a))
  apply congrArg D
  apply Variety.PolynomialFunction.ext
  intro x
  change a (f.onPoints (g * x * g⁻¹)) =
    a (f.onPoints g * f.onPoints x * (f.onPoints g)⁻¹)
  simp only [f.onPoints.map_mul, f.onPoints.map_inv]

omit [IsAlgClosed k] in
private theorem projectiveSymplecticIdentityTangentRepresentation_action
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G)
    (D : IdentityPointDerivation G) :
    ((identityTangentRepresentation G).action g).1 D =
      identityTangentConjugationLinearMap G g D := by
  apply Derivation.ext
  intro a
  rw [identityTangentRepresentation_action_apply,
    identityTangentConjugationLinearMap_apply]

private theorem projectiveSymplecticRootWeight_range
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    letI := C.group
    Set.range (projectiveSymplecticRootWeight (k := k) m C) =
      TorusRootSet (projectiveSymplecticTorus (k := k) m C) := by
  let S := standardSymplecticClosedSubgroup (k := k) m
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let T' := projectiveSymplecticTorus (k := k) m C
  letI : AlgebraicGroup T'.carrierVariety := T'.carrierAlgebraicGroup
  let tau := projectiveSymplecticTorusMorphism (k := k) m C
  have htauSurjective : Function.Surjective tau.onPoints :=
    projectiveSymplecticTorusMorphism_surjective (k := k) m C
  have htauInjective : Function.Injective (TorusCharacter.pullback tau) :=
    torusCharacter_pullback_injective_of_surjective tau htauSurjective
  apply Set.Subset.antisymm
  · rintro chi ⟨r, rfl⟩
    exact ⟨projectiveSymplecticRootSubgroup (k := k) m C r,
      projectiveSymplecticRootSubgroup_isTorusRootSubgroup (k := k) m C r,
      projectiveSymplecticRootWeight_equation (k := k) m C r⟩
  · intro chi hchi
    rcases hchi with ⟨Y, hY, hEq⟩
    letI : AlgebraicGroup Y.carrierVariety := Y.carrierAlgebraicGroup
    have hchiNe : chi ≠ 1 :=
      hY.rootWeight_ne_one_of_centralizer_eq
        (projectiveSymplecticTorus_isMaximalTorus (k := k) m C).1
        (projectiveSymplecticTorus_centralizer_eq (k := k) m C)
        chi hEq
    let y : OneParameterParametrization Y.carrierVariety := Classical.choice hY.2
    let DY : IdentityPointDerivation C.projective := oneParameterTangent Y y
    obtain ⟨DS, hDS⟩ := C.differential_bijective.2 DY
    have hYweight : IsWeightVector (identityTangentRepresentation C.projective)
        T' DY chi⁻¹ := oneParameterTangent_isWeightVector T' Y y hEq
    have hDSweight : IsWeightVector
        (identityTangentRepresentation S.carrierVariety) T DS
        (TorusCharacter.pullback tau chi)⁻¹ := by
      constructor
      · intro hDSzero
        apply hYweight.1
        rw [← hDS, hDSzero, map_zero]
      · intro s
        rw [projectiveSymplecticIdentityTangentRepresentation_action]
        apply C.differential_bijective.1
        have hnatural := LinearMap.congr_fun
          (projectiveSymplecticDifferential_conjugation_naturality
            C.quotient (T.includePoint s)) DS
        calc
          identityTangentMorphismLinearMap C.quotient
              (identityTangentConjugationLinearMap S.carrierVariety
                (T.includePoint s) DS) =
              identityTangentConjugationLinearMap C.projective
                (C.quotient.onPoints (T.includePoint s))
                (identityTangentMorphismLinearMap C.quotient DS) := hnatural
          _ = identityTangentConjugationLinearMap C.projective
                (T'.includePoint (tau.onPoints s)) DY := by
              rw [projectiveSymplecticTorusMorphism_include_apply (k := k) m C,
                hDS]
          _ = (chi⁻¹).pointCharacter (tau.onPoints s) • DY := by
              rw [← projectiveSymplecticIdentityTangentRepresentation_action]
              exact hYweight.2 _
          _ = ((TorusCharacter.pullback tau chi)⁻¹).pointCharacter s •
                identityTangentMorphismLinearMap C.quotient DS := by
              rw [hDS]
              rfl
          _ = identityTangentMorphismLinearMap C.quotient
                (((TorusCharacter.pullback tau chi)⁻¹).pointCharacter s • DS) := by
              rw [map_smul]
    have hpullbackNe : TorusCharacter.pullback tau chi ≠ 1 := by
      intro hpullback
      apply hchiNe
      apply htauInjective
      simpa using hpullback
    obtain ⟨r, hr⟩ :=
      symplecticTangentWeight_eq_rootWeight m hpullbackNe hDSweight
    refine ⟨r, ?_⟩
    apply htauInjective
    calc
      TorusCharacter.pullback tau
          (projectiveSymplecticRootWeight (k := k) m C r) =
          symplecticRootWeight (k := k) m r :=
        projectiveSymplecticRootWeight_pullback (k := k) m C r
      _ = TorusCharacter.pullback tau chi := hr.symm

private noncomputable def projectiveSymplecticRootCocharacter
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m)
    (r : SymplecticRootIndex.{u} m) :
    letI := C.group
    let T' := projectiveSymplecticTorus (k := k) m C
    letI := T'.carrierAlgebraicGroup
    ClosedSubgroupTorusCocharacter T' := by
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let T' := projectiveSymplecticTorus (k := k) m C
  letI : AlgebraicGroup T'.carrierVariety := T'.carrierAlgebraicGroup
  exact (projectiveSymplecticTorusMorphism (k := k) m C).comp
    (symplecticRootCocharacter (k := k) m r)

private noncomputable def projectiveSymplecticRootData
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    letI := C.group
    RootGroupData C.projective
      (projectiveSymplecticTorus (k := k) m C) := by
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let T' := projectiveSymplecticTorus (k := k) m C
  letI : AlgebraicGroup T'.carrierVariety := T'.carrierAlgebraicGroup
  let tau := projectiveSymplecticTorusMorphism (k := k) m C
  let D := symplecticRootData (k := k) m
  exact {
    Root := SymplecticRootIndex.{u} m
    rootWeight := fun r => projectiveSymplecticRootWeight (k := k) m C r.down
    rootSubgroup := fun r => projectiveSymplecticRootSubgroup (k := k) m C r.down
    neg := D.neg
    add := D.add
    pairing := D.pairing
    weightPairing := fun chi r => D.weightPairing
      (TorusCharacter.pullback tau chi) r
    rootCocharacter := projectiveSymplecticRootCocharacter (k := k) m C
    reflect := D.reflect
    positive := D.positive
    simple := D.simple
    height := D.height
  }

private theorem projectiveSymplecticRootData_isRealization
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    letI := C.group
    (projectiveSymplecticRootData (k := k) m C).IsRealization := by
  letI := C.group
  let T := symplecticDiagonalTorus (k := k) m
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let T' := projectiveSymplecticTorus (k := k) m C
  letI : AlgebraicGroup T'.carrierVariety := T'.carrierAlgebraicGroup
  let tau := projectiveSymplecticTorusMorphism (k := k) m C
  let D := symplecticRootData (k := k) m
  let D' := projectiveSymplecticRootData (k := k) m C
  have htauInjective : Function.Injective (TorusCharacter.pullback tau) :=
    torusCharacter_pullback_injective_of_surjective tau
      (projectiveSymplecticTorusMorphism_surjective (k := k) m C)
  rcases symplecticRootData_isRealization (k := k) m with
    ⟨hinjective, _hrange, hroot, hneg, hadd, hreflect, hself, hpairing,
      hheightNeg, hheightAdd, hpositive, hsimple, hcocharacter⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r s hrs
    apply hinjective
    have hpull := congrArg (TorusCharacter.pullback tau) hrs
    change TorusCharacter.pullback tau
        (projectiveSymplecticRootWeight (k := k) m C r.down) =
      TorusCharacter.pullback tau
        (projectiveSymplecticRootWeight (k := k) m C s.down) at hpull
    rw [projectiveSymplecticRootWeight_pullback,
      projectiveSymplecticRootWeight_pullback] at hpull
    exact hpull
  · apply Set.Subset.antisymm
    · rintro chi ⟨r, rfl⟩
      exact ⟨projectiveSymplecticRootSubgroup (k := k) m C r.down,
        projectiveSymplecticRootSubgroup_isTorusRootSubgroup (k := k) m C r.down,
        projectiveSymplecticRootWeight_equation (k := k) m C r.down⟩
    · intro chi hchi
      rw [← projectiveSymplecticRootWeight_range (k := k) m C] at hchi
      rcases hchi with ⟨r, rfl⟩
      exact ⟨ULift.up r, rfl⟩
  · intro r
    exact ⟨projectiveSymplecticRootSubgroup_isTorusRootSubgroup
        (k := k) m C r.down,
      projectiveSymplecticRootWeight_equation (k := k) m C r.down⟩
  · intro r
    apply htauInjective
    change TorusCharacter.pullback tau
        (projectiveSymplecticRootWeight (k := k) m C (D.neg r).down) =
      TorusCharacter.pullback tau
        (projectiveSymplecticRootWeight (k := k) m C r.down)⁻¹
    rw [map_inv, projectiveSymplecticRootWeight_pullback,
      projectiveSymplecticRootWeight_pullback]
    exact hneg r
  · intro r s t h
    apply htauInjective
    change TorusCharacter.pullback tau
        (projectiveSymplecticRootWeight (k := k) m C t.down) =
      TorusCharacter.pullback tau
        (projectiveSymplecticRootWeight (k := k) m C r.down *
          projectiveSymplecticRootWeight (k := k) m C s.down)
    rw [map_mul, projectiveSymplecticRootWeight_pullback,
      projectiveSymplecticRootWeight_pullback,
      projectiveSymplecticRootWeight_pullback]
    exact hadd r s t h
  · intro r s
    apply htauInjective
    change TorusCharacter.pullback tau
        (projectiveSymplecticRootWeight (k := k) m C (D.reflect r s).down) =
      TorusCharacter.pullback tau
        (projectiveSymplecticRootWeight (k := k) m C s.down *
          projectiveSymplecticRootWeight (k := k) m C r.down ^
            (-D.pairing s r))
    rw [map_mul, map_zpow, projectiveSymplecticRootWeight_pullback,
      projectiveSymplecticRootWeight_pullback,
      projectiveSymplecticRootWeight_pullback]
    exact hreflect r s
  · exact hself
  · intro r s
    change D.weightPairing
        (TorusCharacter.pullback tau
          (projectiveSymplecticRootWeight (k := k) m C r.down)) s =
      D.pairing r s
    rw [projectiveSymplecticRootWeight_pullback]
    exact hpairing r s
  · exact hheightNeg
  · exact hheightAdd
  · exact hpositive
  · exact hsimple
  · intro chi r
    have h := hcocharacter (TorusCharacter.pullback tau chi) r
    intro t
    exact h t

private theorem projectiveSymplecticRootData_isActualBasedRootPairing
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    letI := C.group
    IsActualBasedRootPairing
      (projectiveSymplecticRootData (k := k) m C)
      (typeCRootPairingULift m :
        RootPairing (SymplecticRootIndex.{u} m) ℝ
          (TypeCRootSpaceULift.{u} m)
          (TypeCCorootSpaceULift.{u} m))
      (typeCRootPairingULiftBase m)
      (Equiv.refl (SymplecticRootIndex.{u} m)) := by
  letI := C.group
  rcases symplecticRootData_isActualBasedRootPairingULift (k := k) m with
    ⟨hpairing, hreflect, hneg, hsimple⟩
  exact ⟨hpairing, hreflect, hneg, hsimple⟩

private noncomputable def projectiveSymplecticModel
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    SymplecticModel (standardSymplecticBilinForm (k := k) m) where
  basis := symplecticStandardBasis (k := k) m
  symplectic := standardSymplecticClosedSubgroup (k := k) m
  symplectic_carrier := fun g => standardSymplecticClosedSubgroup_carrier m g
  projectiveSymplectic := C.projective
  projectiveSymplecticAlgebraicGroup := C.group
  symplecticPoints := standardSymplecticClosedSubgroupPoints (k := k) m
  symplecticLinear_points := by
    intro x
    exact standardSymplecticClosedSubgroup_linear_points (k := k) m x
  quotient := C.quotient
  quotientIsogeny := C.quotient_isogeny
  quotientKernel := C.quotient_kernel
  quotientUniversal := C.quotient_universal
  projectiveSymplecticPoints := C.point_equiv
  projectiveSymplecticQuotient := C.point_equiv_quotient

private noncomputable def projectiveSymplecticRootSystemModel
    (m : ℕ) (C : ProjectiveSymplecticQuotientData (k := k) m) :
    let M := projectiveSymplecticModel (k := k) m C
    letI := M.projectiveSymplecticAlgebraicGroup
    RootSystemModel
      (typeCRootPairingULift m :
        RootPairing (SymplecticRootIndex.{u} m) ℝ
          (TypeCRootSpaceULift.{u} m)
          (TypeCCorootSpaceULift.{u} m))
      M.projectiveSymplectic := by
  let M := projectiveSymplecticModel (k := k) m C
  letI := M.projectiveSymplecticAlgebraicGroup
  exact {
    torus := projectiveSymplecticTorus (k := k) m C
    maximalTorus := projectiveSymplecticTorus_isMaximalTorus (k := k) m C
    rootData := projectiveSymplecticRootData (k := k) m C
    realization := projectiveSymplecticRootData_isRealization (k := k) m C
    base := typeCRootPairingULiftBase m
    rootEquiv := Equiv.refl (SymplecticRootIndex.{u} m)
    actual := projectiveSymplecticRootData_isActualBasedRootPairing (k := k) m C
  }

/-- The standard projective symplectic quotient realizes the lifted type-C
root pairing in every rank. -/
public theorem exists_standard_projective_symplectic_version (m : ℕ) :
    Nonempty (SemisimpleVersion (k := k) (typeCRootPairingULift m)) := by
  obtain ⟨C⟩ := projectiveSymplecticQuotientData_exists (k := k) m
  let M := projectiveSymplecticModel (k := k) m C
  letI : AlgebraicGroup M.projectiveSymplectic :=
    M.projectiveSymplecticAlgebraicGroup
  refine ⟨{
    carrier := M.projectiveSymplectic
    group := M.projectiveSymplecticAlgebraicGroup
    semisimple := standardSymplectic_isogenyTarget_isSemisimple
      (k := k) m M.quotient M.quotientIsogeny
    rootModel := projectiveSymplecticRootSystemModel (k := k) m C
  }⟩

end

end Theory.AlgebraicGroup
