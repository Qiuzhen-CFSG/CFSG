module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalRootRealization
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalOmegaModel
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.IsogenyRootDataTransportCore
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.RootSystemModelTransport

/-!
# The projective even-orthogonal Omega root model

This module constructs the type-D root model on the actual central quotient of
the standard even-orthogonal carrier.  The quotient is built from its finite center
with a bijective identity differential and surjective invariant-coordinate
pullback.  These properties let each explicit even-orthogonal root curve descend to
a closed one-parameter subgroup of the quotient.

The quotient image of the diagonal torus is maximal and self-centralizing.
Every quotient torus root lifts through the bijective differential to a
nontrivial source tangent weight, so the explicit projected root curves exhaust
the quotient roots.  Their parameter functions descend without a Frobenius
power, giving exact character pullback.  The source type-D combinatorics and
cocharacters then assemble an actual based root-pairing realization on the
projective carrier.  Semisimplicity is inherited directly along the quotient
isogeny.

The construction follows the standard even-orthogonal central quotient and root
subgroups used in GLS, Part I, Chapter A, Sections 1.9--1.10.
-/

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

public instance projective_typeDRootPairingULift_isRootSystem (m : ℕ) :
    (typeDRootPairingULift m : RootPairing
      (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
      (TypeDRootSpaceULift.{u} (m + 2))
      (TypeDCorootSpaceULift.{u} (m + 2))).IsRootSystem := by
  constructor
  · change Submodule.span ℝ (Set.range
      (fun i : EvenOrthogonalRootIndex.{u} (m + 2) =>
        (⟨(typeDRootPairing m).root i.down⟩ :
          TypeDRootSpaceULift.{u} (m + 2)))) = ⊤
    let e : TypeDRootSpaceULift.{u} (m + 2) ≃ₗ[ℝ]
        typeDRootSpan (m + 2) := ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : EvenOrthogonalRootIndex.{u} (m + 2) =>
          (⟨(typeDRootPairing m).root i.down⟩ :
            TypeDRootSpaceULift.{u} (m + 2))) =
        Set.range (typeDRootPairing m).root := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(typeDRootPairing m).root i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_root_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm

  · change Submodule.span ℝ (Set.range
      (fun i : EvenOrthogonalRootIndex.{u} (m + 2) =>
        (⟨(typeDRootPairing m).coroot i.down⟩ :
          TypeDCorootSpaceULift.{u} (m + 2)))) = ⊤
    let e : TypeDCorootSpaceULift.{u} (m + 2) ≃ₗ[ℝ]
        Module.Dual ℝ (typeDRootSpan (m + 2)) := ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : EvenOrthogonalRootIndex.{u} (m + 2) =>
          (⟨(typeDRootPairing m).coroot i.down⟩ :
            TypeDCorootSpaceULift.{u} (m + 2))) =
        Set.range (typeDRootPairing m).coroot := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(typeDRootPairing m).coroot i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_coroot_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm

public instance projective_typeDRootPairingULift_isCrystallographic (m : ℕ) :
    (typeDRootPairingULift m : RootPairing
      (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
      (TypeDRootSpaceULift.{u} (m + 2))
      (TypeDCorootSpaceULift.{u} (m + 2))).IsCrystallographic := by
  constructor
  intro i j
  change ∃ z : ℤ, (z : ℝ) = (typeDRootPairing m).pairing i.down j.down
  exact (typeDRootPairing m).exists_value i.down j.down

public instance projective_typeDRootPairingULift_isReduced (m : ℕ) :
    (typeDRootPairingULift m : RootPairing
      (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
      (TypeDRootSpaceULift.{u} (m + 2))
      (TypeDCorootSpaceULift.{u} (m + 2))).IsReduced := by
  constructor
  intro i j h
  change ¬ LinearIndependent ℝ
      ![(⟨(typeDRootPairing m).root i.down⟩ : TypeDRootSpaceULift.{u} (m + 2)),
        (⟨(typeDRootPairing m).root j.down⟩ : TypeDRootSpaceULift.{u} (m + 2))] at h
  have hdown : ¬ LinearIndependent ℝ
      ![(typeDRootPairing m).root i.down, (typeDRootPairing m).root j.down] := by
    intro hli
    apply h
    have hmapped := hli.map'
      (ULift.moduleEquiv.symm : typeDRootSpan (m + 2) ≃ₗ[ℝ]
        TypeDRootSpaceULift.{u} (m + 2)).toLinearMap
      (LinearMap.ker_eq_bot.mpr
        (ULift.moduleEquiv.symm : typeDRootSpan (m + 2) ≃ₗ[ℝ]
          TypeDRootSpaceULift.{u} (m + 2)).injective)
    have hvectors :
        (![(⟨(typeDRootPairing m).root i.down⟩ : TypeDRootSpaceULift.{u} (m + 2)),
            (⟨(typeDRootPairing m).root j.down⟩ : TypeDRootSpaceULift.{u} (m + 2))] :
            Fin 2 → TypeDRootSpaceULift.{u} (m + 2)) =
          (ULift.moduleEquiv.symm : typeDRootSpan (m + 2) ≃ₗ[ℝ]
            TypeDRootSpaceULift.{u} (m + 2)) ∘
            ![(typeDRootPairing m).root i.down, (typeDRootPairing m).root j.down] := by
      funext x
      fin_cases x <;> rfl
    rw [hvectors]
    exact hmapped
  letI : (typeDRootPairing m).IsReduced := typeDRootPairing_isReduced m
  rcases RootPairing.IsReduced.eq_or_eq_neg i.down j.down hdown with hij | hij
  · left
    apply ULift.ext
    exact hij
  · right
    apply ULift.ext
    exact hij

noncomputable section

public noncomputable abbrev projectiveEvenOrthogonalOmegaCarrier (m : ℕ) (_hm : 2 ≤ m) :=
  evenSpinActionImageClosedSubgroup
    (hyperbolicForm (k := k) (m + 2))
    (standardHyperbolicSplit (m + 2))

private noncomputable abbrev projectiveEvenOrthogonalSourceTorus (m : ℕ) (hm : 2 ≤ m) :=
  evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega)

private noncomputable abbrev projectiveEvenOrthogonalSourceRootSubgroup
    (m : ℕ) (hm : 2 ≤ m) (r : EvenOrthogonalRootIndex (m + 2)) :=
  evenOrthogonalRootSubgroup (k := k) (m + 2) (by omega) r.down

private noncomputable abbrev projectiveEvenOrthogonalSourceRootMorphism
    (m : ℕ) (hm : 2 ≤ m) (r : EvenOrthogonalRootIndex (m + 2)) :=
  evenOrthogonalRootMorphism (k := k) (m + 2) (by omega) r.down

private noncomputable abbrev projectiveEvenOrthogonalSourceRootParametrization
    (m : ℕ) (hm : 2 ≤ m) (r : EvenOrthogonalRootIndex (m + 2)) :=
  evenOrthogonalRootParametrization (k := k) (m + 2) (by omega) r.down

private noncomputable abbrev projectiveEvenOrthogonalSourceRootWeight
    (m : ℕ) (hm : 2 ≤ m) (r : EvenOrthogonalRootIndex (m + 2)) :=
  evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r.down

private noncomputable abbrev projectiveEvenOrthogonalSourceRootCocharacter
    (m : ℕ) (hm : 2 ≤ m) (r : EvenOrthogonalRootIndex (m + 2)) :=
  evenOrthogonalRootCocharacter (k := k) (m + 2) (by omega) r

private noncomputable abbrev projectiveEvenOrthogonalSourceRootData
    (m : ℕ) (hm : 2 ≤ m) :=
  evenOrthogonalRootData (k := k) m hm

private theorem projectiveEvenOrthogonalSourceTorus_isSubtorus
    (m : ℕ) (hm : 2 ≤ m) :
    IsSubtorus (projectiveEvenOrthogonalSourceTorus (k := k) m hm) := by
  exact evenOrthogonalDiagonalTorus_isSubtorus (k := k) (m + 2) (by omega)

private theorem projectiveEvenOrthogonalSourceTorus_centralizer_eq
    (m : ℕ) (hm : 2 ≤ m) :
    (projectiveEvenOrthogonalSourceTorus (k := k) m hm).centralizer.toSubgroup =
      (projectiveEvenOrthogonalSourceTorus (k := k) m hm).toSubgroup := by
  exact evenOrthogonalDiagonalTorus_centralizer_eq (k := k) (m + 2) (by omega)

private theorem projectiveEvenOrthogonalSourceTorus_isMaximalTorus
    (m : ℕ) (hm : 2 ≤ m) :
    IsMaximalTorus (projectiveEvenOrthogonalSourceTorus (k := k) m hm) := by
  exact evenOrthogonalDiagonalTorus_isMaximalTorus (k := k) (m + 2) (by omega)

private theorem projectiveEvenOrthogonalSourceRootWeight_equation
    (m : ℕ) (hm : 2 ≤ m) (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := (projectiveEvenOrthogonalSourceTorus (k := k) m hm).carrierAlgebraicGroup
    letI := (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierAlgebraicGroup
    RootWeightEquation
      (projectiveEvenOrthogonalSourceTorus (k := k) m hm)
      (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r)
      (projectiveEvenOrthogonalSourceRootWeight (k := k) m hm r) := by
  letI := (projectiveEvenOrthogonalSourceTorus (k := k) m hm).carrierAlgebraicGroup
  letI := (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierAlgebraicGroup
  exact evenOrthogonalRootWeight_equation (k := k) (m + 2) (by omega) r.down

private theorem projectiveEvenOrthogonalSourceRootParametrization_include_value
    (m : ℕ) (hm : 2 ≤ m) (r : EvenOrthogonalRootIndex (m + 2)) (a : k) :
    letI := (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierAlgebraicGroup
    (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).includePoint
        (@OneParameterParametrization.value k _
          (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierVariety
          (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierAlgebraicGroup
          (projectiveEvenOrthogonalSourceRootParametrization (k := k) m hm r) a) =
      (projectiveEvenOrthogonalSourceRootMorphism (k := k) m hm r).onPoints
      (kPlusPoint a) := by
  let X := projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r
  let _ : AlgebraicGroup X.carrierVariety := X.carrierAlgebraicGroup
  change (evenOrthogonalRootSubgroup (k := k) (m + 2) (by omega) r.down).includePoint
      (@OneParameterParametrization.value k _
        (evenOrthogonalRootSubgroup (k := k) (m + 2) (by omega) r.down).carrierVariety
        (evenOrthogonalRootSubgroup (k := k) (m + 2) (by omega) r.down).carrierAlgebraicGroup
        (evenOrthogonalRootParametrization (k := k) (m + 2) (by omega) r.down) a) =
      (evenOrthogonalRootMorphism (k := k) (m + 2) (by omega) r.down).onPoints
        (kPlusPoint a)
  exact evenOrthogonalRootParametrization_include_value
    (k := k) (m + 2) (by omega) r.down a

private theorem projectiveEvenOrthogonalSourceRootParametrization_hom
    (m : ℕ) (hm : 2 ≤ m) (r : EvenOrthogonalRootIndex (m + 2)) :
    let X := projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r
    letI := X.carrierAlgebraicGroup
    (projectiveEvenOrthogonalSourceRootParametrization (k := k) m hm r).hom =
      (projectiveEvenOrthogonalSourceRootMorphism (k := k) m hm r).codRestrictClosedSubgroup
        X (fun y => ⟨y, rfl⟩) := by
  let X := projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r
  let _ : AlgebraicGroup X.carrierVariety := X.carrierAlgebraicGroup
  simpa using
    (evenOrthogonalRootParametrization_hom (k := k) (m + 2) (by omega) r.down)

private theorem projectiveEvenOrthogonalSourceRootSubgroup_invariant
    (m : ℕ) (hm : 2 ≤ m) (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := (projectiveEvenOrthogonalSourceTorus (k := k) m hm).carrierAlgebraicGroup
    letI := (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierAlgebraicGroup
    IsClosedSubgroupInvariant
      (projectiveEvenOrthogonalSourceTorus (k := k) m hm)
      (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r) := by
  letI := (projectiveEvenOrthogonalSourceTorus (k := k) m hm).carrierAlgebraicGroup
  letI := (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierAlgebraicGroup
  exact evenOrthogonalRootSubgroup_invariant (k := k) (m + 2) (by omega) r.down

private theorem projectiveEvenOrthogonalSourceRootSubgroup_isOneParameter
    (m : ℕ) (hm : 2 ≤ m) (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := (projectiveEvenOrthogonalSourceTorus (k := k) m hm).carrierAlgebraicGroup
    letI := (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierAlgebraicGroup
    IsOneParameterGroup
      (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierVariety := by
  letI := (projectiveEvenOrthogonalSourceTorus (k := k) m hm).carrierAlgebraicGroup
  letI := (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierAlgebraicGroup
  exact evenOrthogonalRootSubgroup_isOneParameter (k := k) (m + 2) (by omega) r.down

private theorem projectiveEvenOrthogonalSourceRootWeight_range
    (m : ℕ) (hm : 2 ≤ m) :
    Set.range (projectiveEvenOrthogonalSourceRootWeight (k := k) m hm) =
      TorusRootSet (projectiveEvenOrthogonalSourceTorus (k := k) m hm) := by
  change Set.range (fun r : EvenOrthogonalRootIndex (m + 2) =>
      evenOrthogonalRootWeight (k := k) (m + 2) (by omega) r.down) =
    TorusRootSet (evenOrthogonalDiagonalTorus (k := k) (m + 2) (by omega))
  rw [← evenOrthogonalRootWeight_range (k := k) (m + 2) (by omega)]
  apply Set.Subset.antisymm
  · rintro chi ⟨r, rfl⟩
    exact ⟨r.down, rfl⟩
  · rintro chi ⟨r, rfl⟩
    exact ⟨ULift.up r, rfl⟩

private theorem projectiveEvenOrthogonalSourceTangentWeight_eq_rootWeight
    (m : ℕ) (hm : 2 ≤ m)
    {chi : TorusWeight (projectiveEvenOrthogonalSourceTorus (k := k) m hm)}
    {D : IdentityPointDerivation
      (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety}
    (hchi : chi ≠ 1)
    (hD : IsWeightVector
      (identityTangentRepresentation
        (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety)
      (projectiveEvenOrthogonalSourceTorus (k := k) m hm) D chi⁻¹) :
    ∃ r : EvenOrthogonalRootIndex (m + 2),
      chi = projectiveEvenOrthogonalSourceRootWeight (k := k) m hm r := by
  simpa [projectiveEvenOrthogonalSourceTorus,
    projectiveEvenOrthogonalOmegaCarrier,
    projectiveEvenOrthogonalSourceRootWeight] using
    (evenOrthogonalTangentWeight_eq_rootWeight (k := k) (m + 2) (by omega)
      hchi hD)

public structure ProjectiveEvenOrthogonalQuotientData (m : ℕ) (hm : 2 ≤ m) where
  projective : Variety k
  group : AlgebraicGroup projective
  quotient :
    letI := (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierAlgebraicGroup
    letI := group
    AlgebraicGroup.Morphism
      (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety projective
  quotient_isogeny :
    letI := (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierAlgebraicGroup
    letI := group
    IsIsogeny quotient
  quotient_kernel :
    letI := (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierAlgebraicGroup
    letI := group
    quotient.kernel = Subgroup.center
      (Variety.Point
        (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety)
  quotient_universal :
    letI := (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierAlgebraicGroup
    letI := group
    ∀ {H : Variety k} [AlgebraicGroup H]
      (f : AlgebraicGroup.Morphism
        (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety H),
      Subgroup.center
          (Variety.Point
            (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety) ≤
        f.kernel →
      ∃! r : AlgebraicGroup.Morphism projective H, r.comp quotient = f
  point_equiv :
    letI := (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierAlgebraicGroup
    letI := group
    Variety.Point projective ≃*
      Variety.Point
          (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety ⧸
        Subgroup.center
          (Variety.Point
            (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety)
  point_equiv_quotient :
    letI := (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierAlgebraicGroup
    letI := group
    ∀ x, point_equiv (quotient.onPoints x) =
      QuotientGroup.mk'
        (Subgroup.center
          (Variety.Point
            (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety)) x
  differential_bijective :
    letI := (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierAlgebraicGroup
    letI := group
    Function.Bijective (identityTangentMorphismLinearMap quotient)
  invariant_coordinate_descends :
    letI := (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierAlgebraicGroup
    letI := group
    ∀ F : Variety.PolynomialFunction
        (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety,
      F ∈ AlgebraicGroup.rightInvariantCoordinateRing
        ((ClosedSubgroup.top (G :=
          (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety)).centralizer) →
      ∃ A : Variety.PolynomialFunction projective,
        Variety.PolynomialFunction.pullback quotient.toVariety A = F

public theorem projectiveEvenOrthogonalQuotientData_exists (m : ℕ) (hm : 2 ≤ m) :
    Nonempty (ProjectiveEvenOrthogonalQuotientData (k := k) m hm) := by
  let S := projectiveEvenOrthogonalOmegaCarrier (k := k) m hm
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  have hsemisimple : IsSemisimpleAlgebraicGroup S.carrierVariety := by
    exact evenSpinActionImageClosedSubgroup_isSemisimple
      (standardHyperbolicSplit (k := k) (m + 2)) (by simpa using (show 4 ≤ m + 2 by omega))
  letI : Finite (Subgroup.center (Variety.Point S.carrierVariety)) :=
    connectedSemisimple_center_finite hsemisimple
  let Z : ClosedSubgroup S.carrierVariety :=
    ClosedSubgroup.ofSubgroup
      (Subgroup.center (Variety.Point S.carrierVariety))
      (isZariskiClosed_of_finite
        (Set.toFinite (Subgroup.center (Variety.Point S.carrierVariety) :
          Set (Variety.Point S.carrierVariety))))
  letI : AlgebraicGroup Z.carrierVariety := Z.carrierAlgebraicGroup
  letI : Finite Z.toSubgroup := by
    change Finite (Subgroup.center (Variety.Point S.carrierVariety))
    infer_instance
  have hZnormal : Z.toSubgroup.Normal := by
    change (Subgroup.center (Variety.Point S.carrierVariety)).Normal
    infer_instance
  let D := Bor1.theorem_1_1_2_b_quotientData Z hZnormal
  letI : AlgebraicGroup D.quotient := D.quotientAlgebraicGroup
  have hkernelCenter : D.projection.kernel =
      Subgroup.center (Variety.Point S.carrierVariety) := by
    rw [D.kernel_eq]
    rfl
  have hqiso : IsIsogeny D.projection :=
    ⟨D.pointSurjective, by rw [hkernelCenter]; infer_instance⟩
  have hZcenter : Z =
      (ClosedSubgroup.top (G := S.carrierVariety)).centralizer := by
    apply SetLike.coe_injective
    change (Subgroup.center (Variety.Point S.carrierVariety) :
      Set (Variety.Point S.carrierVariety)) =
      Subgroup.centralizer
        ((⊤ : Subgroup (Variety.Point S.carrierVariety)) :
          Set (Variety.Point S.carrierVariety))
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
  have hqdfinj : Function.Injective
      (identityTangentMorphismLinearMap D.projection) := by
    have hZpoints : Finite (Variety.Point Z.carrierVariety) :=
      (Equiv.finite_iff Z.pointEquiv).mpr inferInstance
    have hZdim : Variety.dimension Z.carrierVariety = 0 :=
      (dimension_zero_iff_finite_points Z.carrierVariety).2 hZpoints
    have hZfinrank : Module.finrank k
        (IdentityPointDerivation Z.carrierVariety) = 0 := by
      rw [Bor1.identityPointDerivation_finrank_eq_dimension, hZdim]
      simp
    have hZzero : ∀ E : IdentityPointDerivation Z.carrierVariety, E = 0 :=
      finrank_zero_iff_forall_zero.mp hZfinrank
    have hker :
        LinearMap.ker (identityTangentMorphismLinearMap D.projection) =
          LinearMap.range (identityTangentMorphismLinearMap Z.inclusion) := by
      simpa only [Bor1.identityTangentMorphismLinearMap,
        Theory.AlgebraicGroup.identityTangentMorphismLinearMap] using D.tangentKernel_eq
    intro E F hEF
    have hzero : identityTangentMorphismLinearMap D.projection (E - F) = 0 := by
      simpa [map_sub] using sub_eq_zero.mpr hEF
    have hmem : E - F ∈ LinearMap.ker
        (identityTangentMorphismLinearMap D.projection) := hzero
    rw [hker] at hmem
    rcases hmem with ⟨G, hG⟩
    have hG0 : G = 0 := hZzero G
    rw [hG0, map_zero] at hG
    exact sub_eq_zero.mp hG.symm
  have hfactor :
      ∀ {H : Variety k} [AlgebraicGroup H]
        (f : AlgebraicGroup.Morphism S.carrierVariety H),
        Subgroup.center (Variety.Point S.carrierVariety) ≤ f.kernel →
          ∃! r : AlgebraicGroup.Morphism D.quotient H, r.comp D.projection = f := by
    intro H hH f hf
    simpa using D.algebraicUniversal f hf
  letI : AlgebraicGroup D.quotient := D.quotientAlgebraicGroup
  let eQ0 : (Variety.Point S.carrierVariety ⧸ D.projection.onPoints.ker) ≃*
      Variety.Point D.quotient :=
    QuotientGroup.quotientKerEquivOfSurjective D.projection.onPoints D.pointSurjective
  let eQ1 : (Variety.Point S.carrierVariety ⧸
      Subgroup.center (Variety.Point S.carrierVariety)) ≃*
      (Variety.Point S.carrierVariety ⧸ D.projection.onPoints.ker) :=
    QuotientGroup.quotientMulEquivOfEq hkernelCenter.symm
  let eQ : Variety.Point D.quotient ≃*
      Variety.Point S.carrierVariety ⧸
        Subgroup.center (Variety.Point S.carrierVariety) := (eQ1.trans eQ0).symm
  have heQ (x : Variety.Point S.carrierVariety) :
      eQ (D.projection.onPoints x) =
        QuotientGroup.mk' (Subgroup.center (Variety.Point S.carrierVariety)) x :=
    by
      change eQ1.symm (eQ0.symm (D.projection.onPoints x)) = _
      apply eQ1.injective
      rw [eQ1.apply_symm_apply]
      apply eQ0.injective
      rw [eQ0.apply_symm_apply]
      change eQ0 (QuotientGroup.mk' D.projection.onPoints.ker x) =
        D.projection.onPoints x
      exact QuotientGroup.kerLift_mk D.projection.onPoints x
  refine ⟨{
    projective := D.quotient
    group := D.quotientAlgebraicGroup
    quotient := D.projection
    quotient_isogeny := hqiso
    quotient_kernel := hkernelCenter
    quotient_universal := hfactor
    point_equiv := eQ
    point_equiv_quotient := heQ
    differential_bijective := ⟨hqdfinj, D.tangentSurjective⟩
    invariant_coordinate_descends := ?_
  }⟩
  intro F hF
  have hFZ : F ∈ AlgebraicGroup.rightInvariantCoordinateRing Z := by
    rw [hZcenter]
    exact hF
  obtain ⟨A, hA⟩ := D.invariantPullbackSurjective ⟨F, hFZ⟩
  exact ⟨A, congrArg Subtype.val hA⟩

private noncomputable def projectiveEvenOrthogonalTorus
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    ClosedSubgroup C.projective := by
  letI := C.group
  letI := (projectiveEvenOrthogonalSourceTorus (k := k) m hm).carrierAlgebraicGroup
  exact (C.quotient.comp
    (projectiveEvenOrthogonalSourceTorus (k := k) m hm).inclusion).imageClosedSubgroup

private noncomputable def projectiveEvenOrthogonalRootMorphism
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    AlgebraicGroup.Morphism (KPlus k) C.projective := by
  letI := C.group
  exact C.quotient.comp (projectiveEvenOrthogonalSourceRootMorphism (k := k) m hm r)

private noncomputable def projectiveEvenOrthogonalRootSubgroup
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    ClosedSubgroup C.projective := by
  letI := C.group
  exact (projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).imageClosedSubgroup

private theorem projectiveEvenOrthogonalRoot_parameter_exists
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    ∃ A : Variety.PolynomialFunction C.projective,
      ∀ x : Variety.Point (KPlus k),
        A ((projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).onPoints x) =
          x.val PUnit.unit := by
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  let X := projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r
  letI := T.carrierAlgebraicGroup
  letI := X.carrierAlgebraicGroup
  have hX : IsTorusRootSubgroup T X :=
    ⟨projectiveEvenOrthogonalSourceRootSubgroup_invariant (k := k) m hm r,
      projectiveEvenOrthogonalSourceRootSubgroup_isOneParameter (k := k) m hm r⟩
  have hchi : projectiveEvenOrthogonalSourceRootWeight (k := k) m hm r ≠ 1 :=
    hX.rootWeight_ne_one_of_centralizer_eq
      (projectiveEvenOrthogonalSourceTorus_isSubtorus (k := k) m hm)
      (projectiveEvenOrthogonalSourceTorus_centralizer_eq (k := k) m hm)
      (projectiveEvenOrthogonalSourceRootWeight (k := k) m hm r)
      (projectiveEvenOrthogonalSourceRootWeight_equation (k := k) m hm r)
  obtain ⟨F, hFinv, hF⟩ := rootParameter_exists_centerInvariantPolynomial
    T X (projectiveEvenOrthogonalSourceRootWeight (k := k) m hm r)
    (projectiveEvenOrthogonalSourceRootWeight_equation (k := k) m hm r) hchi
    (projectiveEvenOrthogonalSourceRootParametrization (k := k) m hm r)
  obtain ⟨A, hA⟩ := C.invariant_coordinate_descends F hFinv
  refine ⟨A, ?_⟩
  intro x
  let a : k := x.val PUnit.unit
  have hx : x = kPlusPoint a := (kPlusPoint_coordinate x).symm
  change A ((projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).onPoints x) = a
  calc
    A ((projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).onPoints x) =
        A ((projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).onPoints
          (kPlusPoint a)) := congrArg
            (fun z => A ((projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).onPoints z)) hx
    _ = a := by
      let z := (projectiveEvenOrthogonalSourceRootMorphism (k := k) m hm r).onPoints (kPlusPoint a)
      calc
        A (C.quotient.onPoints z) = F z := by
          exact congrArg (fun G : Variety.PolynomialFunction
            (projectiveEvenOrthogonalOmegaCarrier (k := k) m hm).carrierVariety => G z) hA
        _ = a := by
          dsimp only [z]
          have hparam := projectiveEvenOrthogonalSourceRootParametrization_include_value
            (k := k) m hm r a
          rw [← hparam]
          exact hF a

private theorem projectiveEvenOrthogonalRootMorphism_injective
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    Function.Injective
      (projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).onPoints := by
  letI := C.group
  obtain ⟨A, hA⟩ := projectiveEvenOrthogonalRoot_parameter_exists
    (k := k) m hm C r
  intro x y hxy
  apply Variety.Point.ext
  funext i
  rw [show i = PUnit.unit by rfl]
  rw [← hA x, ← hA y, hxy]

private theorem projectiveEvenOrthogonalRootMorphism_coordinate_preimage
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    ∀ c : (KPlus k).Coordinates,
      ∃ A : Variety.PolynomialFunction C.projective,
        Variety.PolynomialFunction.pullback
            (projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).toVariety A =
          Variety.PolynomialFunction.ofPolynomial (KPlus k)
            (MvPolynomial.X c) := by
  letI := C.group
  intro c
  obtain ⟨A, hA⟩ := projectiveEvenOrthogonalRoot_parameter_exists
    (k := k) m hm C r
  refine ⟨A, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  change A ((projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).onPoints x) =
    evalPolynomial x.val (MvPolynomial.X c)
  rw [hA]
  rw [evalPolynomial_X]

private theorem projectiveEvenOrthogonalRootMorphism_mem_rootSubgroup
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) (x : Variety.Point (KPlus k)) :
    letI := C.group
    (projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).onPoints x ∈
      projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r := by
  letI := C.group
  exact ⟨x, rfl⟩

private noncomputable def projectiveEvenOrthogonalRootParametrization
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    let Y := projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r
    letI := Y.carrierAlgebraicGroup
    OneParameterParametrization Y.carrierVariety := by
  letI := C.group
  let Y := projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r
  letI := Y.carrierAlgebraicGroup
  exact Classical.choose
    (AlgebraicGroup.Morphism.iso_imageClosedSubgroup_of_coordinate_preimage
      (projectiveEvenOrthogonalRootMorphism (k := k) m hm C r)
      (projectiveEvenOrthogonalRootMorphism_injective (k := k) m hm C r)
      (projectiveEvenOrthogonalRootMorphism_coordinate_preimage (k := k) m hm C r))

private theorem projectiveEvenOrthogonalRootParametrization_hom
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    let Y := projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r
    letI := Y.carrierAlgebraicGroup
    (projectiveEvenOrthogonalRootParametrization (k := k) m hm C r).hom =
      AlgebraicGroup.Morphism.codRestrictClosedSubgroup
        (projectiveEvenOrthogonalRootMorphism (k := k) m hm C r)
        Y (projectiveEvenOrthogonalRootMorphism_mem_rootSubgroup
          (k := k) m hm C r) := by
  letI := C.group
  let Y := projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r
  letI := Y.carrierAlgebraicGroup
  exact Classical.choose_spec
    (AlgebraicGroup.Morphism.iso_imageClosedSubgroup_of_coordinate_preimage
      (projectiveEvenOrthogonalRootMorphism (k := k) m hm C r)
      (projectiveEvenOrthogonalRootMorphism_injective (k := k) m hm C r)
      (projectiveEvenOrthogonalRootMorphism_coordinate_preimage (k := k) m hm C r))

private theorem projectiveEvenOrthogonalRootParametrization_include_value
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) (a : k) :
    letI := C.group
    let Y := projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r
    letI := Y.carrierAlgebraicGroup
    Y.includePoint
        ((projectiveEvenOrthogonalRootParametrization (k := k) m hm C r).value a) =
      C.quotient.onPoints
        ((projectiveEvenOrthogonalSourceRootMorphism (k := k) m hm r).onPoints
          (kPlusPoint a)) := by
  letI := C.group
  let Y := projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r
  letI := Y.carrierAlgebraicGroup
  change Y.inclusion.onPoints
      ((projectiveEvenOrthogonalRootParametrization (k := k) m hm C r).hom.onPoints
        (kPlusPoint a)) = _
  rw [projectiveEvenOrthogonalRootParametrization_hom]
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  rfl

private theorem projectiveEvenOrthogonalRootSubgroup_eq_source_image
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    let X := projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r
    letI := X.carrierAlgebraicGroup
    (C.quotient.comp
      X.inclusion).imageClosedSubgroup =
        projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r := by
  letI := C.group
  let X := projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r
  letI := X.carrierAlgebraicGroup
  let x := projectiveEvenOrthogonalSourceRootParametrization (k := k) m hm r
  apply SetLike.coe_injective
  ext y
  change y ∈ (C.quotient.comp X.inclusion).image ↔
    y ∈ (projectiveEvenOrthogonalRootMorphism (k := k) m hm C r).image
  constructor
  · rintro ⟨z, rfl⟩
    let w := x.inv.onPoints z
    refine ⟨w, ?_⟩
    change C.quotient.onPoints ((projectiveEvenOrthogonalSourceRootMorphism (k := k) m hm r).onPoints w) =
      C.quotient.onPoints (X.inclusion.onPoints z)
    congr 1
    have hx := congrArg X.inclusion.onPoints (x.inv_hom_id z)
    change X.inclusion.onPoints (x.hom.onPoints w) = X.inclusion.onPoints z at hx
    rw [projectiveEvenOrthogonalSourceRootParametrization_hom] at hx
    have hinclude :=
      (projectiveEvenOrthogonalSourceRootMorphism (k := k) m hm r).codRestrictClosedSubgroup_inclusion_apply
        X (fun y => ⟨y, rfl⟩) w
    exact hinclude.symm.trans hx
  · rintro ⟨z, rfl⟩
    refine ⟨x.hom.onPoints z, ?_⟩
    change C.quotient.onPoints (X.inclusion.onPoints (x.hom.onPoints z)) =
      C.quotient.onPoints ((projectiveEvenOrthogonalSourceRootMorphism (k := k) m hm r).onPoints z)
    congr 1
    rw [projectiveEvenOrthogonalSourceRootParametrization_hom]
    exact
      (projectiveEvenOrthogonalSourceRootMorphism (k := k) m hm r).codRestrictClosedSubgroup_inclusion_apply
        X (fun y => ⟨y, rfl⟩) z

private theorem projectiveEvenOrthogonalRootSubgroup_isTorusRootSubgroup
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    IsTorusRootSubgroup
      (projectiveEvenOrthogonalTorus (k := k) m hm C)
      (projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r) := by
  letI := C.group
  constructor
  · rw [← projectiveEvenOrthogonalRootSubgroup_eq_source_image]
    exact morphism_image_rootSubgroup_invariant C.quotient
      (projectiveEvenOrthogonalSourceTorus (k := k) m hm)
      (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r)
      (projectiveEvenOrthogonalSourceRootSubgroup_invariant (k := k) m hm r)
  · exact ⟨projectiveEvenOrthogonalRootParametrization (k := k) m hm C r⟩

private noncomputable def projectiveEvenOrthogonalRootWeight
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    TorusWeight (projectiveEvenOrthogonalTorus (k := k) m hm C) := by
  letI := C.group
  exact Classical.choose (existsUnique_rootWeight_of_isTorusRootSubgroup
    (projectiveEvenOrthogonalTorus (k := k) m hm C)
    (projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r)
    (projectiveEvenOrthogonalRootSubgroup_isTorusRootSubgroup (k := k) m hm C r))

private theorem projectiveEvenOrthogonalRootWeight_equation
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    RootWeightEquation
      (projectiveEvenOrthogonalTorus (k := k) m hm C)
      (projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r)
      (projectiveEvenOrthogonalRootWeight (k := k) m hm C r) := by
  letI := C.group
  exact (Classical.choose_spec (existsUnique_rootWeight_of_isTorusRootSubgroup
    (projectiveEvenOrthogonalTorus (k := k) m hm C)
    (projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r)
    (projectiveEvenOrthogonalRootSubgroup_isTorusRootSubgroup (k := k) m hm C r))).1

private noncomputable abbrev projectiveEvenOrthogonalRootImageWitness
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    let X := projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r
    letI := X.carrierAlgebraicGroup
    IsogenyRootImageWitness C.quotient
      X
      (projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r) := by
  letI := C.group
  let X := projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r
  letI := X.carrierAlgebraicGroup
  let Y := projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r
  letI := Y.carrierAlgebraicGroup
  exact {
    image_eq := projectiveEvenOrthogonalRootSubgroup_eq_source_image (k := k) m hm C r
    source := projectiveEvenOrthogonalSourceRootParametrization (k := k) m hm r
    target := projectiveEvenOrthogonalRootParametrization (k := k) m hm C r
    polynomial := Polynomial.X
    polynomial_ne_zero := by simp
    parameter_eq := by
      intro a
      rw [Polynomial.eval_X]
      change C.quotient.onPoints
          ((projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).includePoint
            (@OneParameterParametrization.value k _
              (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierVariety
              (projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r).carrierAlgebraicGroup
              (projectiveEvenOrthogonalSourceRootParametrization (k := k) m hm r) a)) =
        (projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r).includePoint
          (@OneParameterParametrization.value k _
            (projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r).carrierVariety
            (projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r).carrierAlgebraicGroup
            (projectiveEvenOrthogonalRootParametrization (k := k) m hm C r) a)
      rw [projectiveEvenOrthogonalSourceRootParametrization_include_value]
      rw [projectiveEvenOrthogonalRootParametrization_include_value]
  }

private theorem projectiveEvenOrthogonalTorusMorphism_mem_image
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (x : Variety.Point (projectiveEvenOrthogonalSourceTorus (k := k) m hm).carrierVariety) :
    letI := C.group
    let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
    letI := T.carrierAlgebraicGroup
    (C.quotient.comp
      (projectiveEvenOrthogonalSourceTorus (k := k) m hm).inclusion).onPoints x ∈
        projectiveEvenOrthogonalTorus (k := k) m hm C := by
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  letI := T.carrierAlgebraicGroup
  exact ⟨x, rfl⟩

private noncomputable def projectiveEvenOrthogonalTorusMorphism
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
    letI := T.carrierAlgebraicGroup
    let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
    letI := T'.carrierAlgebraicGroup
    AlgebraicGroup.Morphism
      T.carrierVariety T'.carrierVariety := by
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  letI := T.carrierAlgebraicGroup
  let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
  letI := T'.carrierAlgebraicGroup
  exact (C.quotient.comp T.inclusion).codRestrictClosedSubgroup T'
    (projectiveEvenOrthogonalTorusMorphism_mem_image (k := k) m hm C)

private theorem projectiveEvenOrthogonalTorusMorphism_surjective
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
    letI := T.carrierAlgebraicGroup
    let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
    letI := T'.carrierAlgebraicGroup
    Function.Surjective
      (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C).onPoints := by
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  letI := T.carrierAlgebraicGroup
  let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
  letI := T'.carrierAlgebraicGroup
  exact (C.quotient.comp T.inclusion).codRestrictImageClosedSubgroup_surjective
    (projectiveEvenOrthogonalTorusMorphism_mem_image (k := k) m hm C)

private theorem projectiveEvenOrthogonalTorusMorphism_include_apply
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (s : Variety.Point (projectiveEvenOrthogonalSourceTorus (k := k) m hm).carrierVariety) :
    letI := C.group
    let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
    letI := T.carrierAlgebraicGroup
    let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
    letI := T'.carrierAlgebraicGroup
    (projectiveEvenOrthogonalTorus (k := k) m hm C).includePoint
        ((projectiveEvenOrthogonalTorusMorphism (k := k) m hm C).onPoints s) =
      C.quotient.onPoints
        ((projectiveEvenOrthogonalSourceTorus (k := k) m hm).includePoint s) := by
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  letI := T.carrierAlgebraicGroup
  let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
  letI := T'.carrierAlgebraicGroup
  exact
    (C.quotient.comp
      (projectiveEvenOrthogonalSourceTorus (k := k) m hm).inclusion).codRestrictClosedSubgroup_inclusion_apply
        (projectiveEvenOrthogonalTorus (k := k) m hm C)
        (projectiveEvenOrthogonalTorusMorphism_mem_image (k := k) m hm C) s

private theorem projectiveEvenOrthogonalTorus_isMaximalTorus
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    IsMaximalTorus (projectiveEvenOrthogonalTorus (k := k) m hm C) := by
  letI := C.group
  exact isogenyImageTorus_isMaximalTorus C.quotient C.quotient_isogeny
    (projectiveEvenOrthogonalSourceTorus (k := k) m hm)
    (projectiveEvenOrthogonalSourceTorus_isMaximalTorus (k := k) m hm)

private theorem projectiveEvenOrthogonalTorus_centralizer_eq
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    (projectiveEvenOrthogonalTorus (k := k) m hm C).centralizer.toSubgroup =
      (projectiveEvenOrthogonalTorus (k := k) m hm C).toSubgroup := by
  let S := projectiveEvenOrthogonalOmegaCarrier (k := k) m hm
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
  letI : AlgebraicGroup T'.carrierVariety := T'.carrierAlgebraicGroup
  letI : Finite (Subgroup.center (Variety.Point S.carrierVariety)) :=
    connectedSemisimple_center_finite
      (evenSpinActionImageClosedSubgroup_isSemisimple
        (standardHyperbolicSplit (k := k) (m + 2)) (by
          rw [standardHyperbolicSplit_rank]
          omega))
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
      (projectiveEvenOrthogonalSourceTorus_isSubtorus (k := k) m hm).isConnected
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
      rw [← projectiveEvenOrthogonalSourceTorus_centralizer_eq (k := k) m hm]
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
      (projectiveEvenOrthogonalTorus_isMaximalTorus (k := k) m hm C).1.isMulCommutative
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

private theorem projectiveEvenOrthogonalRootWeight_pullback
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex (m + 2)) :
    letI := C.group
    let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
    letI := T.carrierAlgebraicGroup
    let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
    letI := T'.carrierAlgebraicGroup
    TorusCharacter.pullback (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
        (projectiveEvenOrthogonalRootWeight (k := k) m hm C r) =
      projectiveEvenOrthogonalSourceRootWeight (k := k) m hm r := by
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  letI := T.carrierAlgebraicGroup
  let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
  letI := T'.carrierAlgebraicGroup
  let X := projectiveEvenOrthogonalSourceRootSubgroup (k := k) m hm r
  letI := X.carrierAlgebraicGroup
  let Y := projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r
  letI := Y.carrierAlgebraicGroup
  have h :=
    (projectiveEvenOrthogonalRootImageWitness (k := k) m hm C r).weight_pullback_eq_pow_natDegree
      (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
      (projectiveEvenOrthogonalTorusMorphism_include_apply (k := k) m hm C)
      (projectiveEvenOrthogonalSourceRootWeight (k := k) m hm r)
      (projectiveEvenOrthogonalRootWeight (k := k) m hm C r)
      (projectiveEvenOrthogonalSourceRootWeight_equation (k := k) m hm r)
      (projectiveEvenOrthogonalRootWeight_equation (k := k) m hm C r)
  simpa [projectiveEvenOrthogonalRootImageWitness, Polynomial.natDegree_X] using h

omit [IsAlgClosed k] in
private theorem projectiveEvenOrthogonalDifferential_conjugation_naturality
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
private theorem projectiveEvenOrthogonalIdentityTangentRepresentation_action
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G)
    (D : IdentityPointDerivation G) :
    ((identityTangentRepresentation G).action g).1 D =
      identityTangentConjugationLinearMap G g D := by
  apply Derivation.ext
  intro a
  rw [identityTangentRepresentation_action_apply,
    identityTangentConjugationLinearMap_apply]

private theorem projectiveEvenOrthogonalRootWeight_range
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    Set.range (projectiveEvenOrthogonalRootWeight (k := k) m hm C) =
      TorusRootSet (projectiveEvenOrthogonalTorus (k := k) m hm C) := by
  let S := projectiveEvenOrthogonalOmegaCarrier (k := k) m hm
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
  letI : AlgebraicGroup T'.carrierVariety := T'.carrierAlgebraicGroup
  let tau := projectiveEvenOrthogonalTorusMorphism (k := k) m hm C
  have htauSurjective : Function.Surjective tau.onPoints :=
    projectiveEvenOrthogonalTorusMorphism_surjective (k := k) m hm C
  have htauInjective : Function.Injective (TorusCharacter.pullback tau) :=
    torusCharacter_pullback_injective_of_surjective tau htauSurjective
  apply Set.Subset.antisymm
  · rintro chi ⟨r, rfl⟩
    exact ⟨projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r,
      projectiveEvenOrthogonalRootSubgroup_isTorusRootSubgroup (k := k) m hm C r,
      projectiveEvenOrthogonalRootWeight_equation (k := k) m hm C r⟩
  · intro chi hchi
    rcases hchi with ⟨Y, hY, hEq⟩
    letI : AlgebraicGroup Y.carrierVariety := Y.carrierAlgebraicGroup
    have hchiNe : chi ≠ 1 :=
      hY.rootWeight_ne_one_of_centralizer_eq
        (projectiveEvenOrthogonalTorus_isMaximalTorus (k := k) m hm C).1
        (projectiveEvenOrthogonalTorus_centralizer_eq (k := k) m hm C)
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
        rw [projectiveEvenOrthogonalIdentityTangentRepresentation_action]
        apply C.differential_bijective.1
        have hnatural := LinearMap.congr_fun
          (projectiveEvenOrthogonalDifferential_conjugation_naturality
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
              rw [projectiveEvenOrthogonalTorusMorphism_include_apply (k := k) m hm C,
                hDS]
          _ = (chi⁻¹).pointCharacter (tau.onPoints s) • DY := by
              rw [← projectiveEvenOrthogonalIdentityTangentRepresentation_action]
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
      projectiveEvenOrthogonalSourceTangentWeight_eq_rootWeight m hm hpullbackNe hDSweight
    refine ⟨r, ?_⟩
    apply htauInjective
    rw [projectiveEvenOrthogonalRootWeight_pullback (k := k) m hm C r]
    exact hr.symm

private noncomputable def projectiveEvenOrthogonalRootCocharacter
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm)
    (r : EvenOrthogonalRootIndex.{u} (m + 2)) :
    letI := C.group
    let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
    letI := T'.carrierAlgebraicGroup
    ClosedSubgroupTorusCocharacter T' := by
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
  letI : AlgebraicGroup T'.carrierVariety := T'.carrierAlgebraicGroup
  exact (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C).comp
    (projectiveEvenOrthogonalSourceRootCocharacter (k := k) m hm r)

private noncomputable def projectiveEvenOrthogonalRootData
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    RootGroupData C.projective
      (projectiveEvenOrthogonalTorus (k := k) m hm C) := by
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
  letI : AlgebraicGroup T'.carrierVariety := T'.carrierAlgebraicGroup
  let tau := projectiveEvenOrthogonalTorusMorphism (k := k) m hm C
  exact {
    Root := EvenOrthogonalRootIndex.{u} (m + 2)
    rootWeight := fun r => projectiveEvenOrthogonalRootWeight (k := k) m hm C r
    rootSubgroup := fun r => projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r
    neg := fun r => ⟨(evenOrthogonalSeed m).neg r.down⟩
    add := fun r s => Option.map ULift.up ((evenOrthogonalSeed m).add r.down s.down)
    pairing := fun r s => evenOrthogonalRootPairingInt m r.down s.down
    weightPairing := fun chi r =>
      (evenOrthogonalRootData (k := k) m hm).weightPairing
        (TorusCharacter.pullback tau chi) r
    rootCocharacter := projectiveEvenOrthogonalRootCocharacter (k := k) m hm C
    reflect := fun r s => ⟨((evenOrthogonalSeed m).reflectionPerm r.down) s.down⟩
    positive := (evenOrthogonalSeed m).positive ∘ ULift.down
    simple := (evenOrthogonalSeed m).simple ∘ ULift.down
    height := fun r => (evenOrthogonalSeed m).height r.down
  }

private theorem projectiveEvenOrthogonalRootData_isRealization
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    (projectiveEvenOrthogonalRootData (k := k) m hm C).IsRealization := by
  letI := C.group
  let T := projectiveEvenOrthogonalSourceTorus (k := k) m hm
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let T' := projectiveEvenOrthogonalTorus (k := k) m hm C
  letI : AlgebraicGroup T'.carrierVariety := T'.carrierAlgebraicGroup
  let tau := projectiveEvenOrthogonalTorusMorphism (k := k) m hm C
  let D := evenOrthogonalRootData (k := k) m hm
  dsimp [projectiveEvenOrthogonalRootData]
  have htauInjective : Function.Injective
      (TorusCharacter.pullback (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)) :=
    torusCharacter_pullback_injective_of_surjective
      (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
      (projectiveEvenOrthogonalTorusMorphism_surjective (k := k) m hm C)
  rcases evenOrthogonalRootData_isRealization (k := k) m hm with
    ⟨hinjective, _hrange, hroot, hneg, hadd, hreflect, hself, hpairing,
      hheightNeg, hheightAdd, hpositive, hsimple, hcocharacter⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r s hrs
    apply hinjective
    have hpull := congrArg
      (TorusCharacter.pullback (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)) hrs
    change TorusCharacter.pullback
        (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
        (projectiveEvenOrthogonalRootWeight (k := k) m hm C r) =
      TorusCharacter.pullback
        (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
        (projectiveEvenOrthogonalRootWeight (k := k) m hm C s) at hpull
    rw [projectiveEvenOrthogonalRootWeight_pullback,
      projectiveEvenOrthogonalRootWeight_pullback] at hpull
    exact hpull
  · apply Set.Subset.antisymm
    · rintro chi ⟨r, rfl⟩
      exact ⟨projectiveEvenOrthogonalRootSubgroup (k := k) m hm C r,
        projectiveEvenOrthogonalRootSubgroup_isTorusRootSubgroup (k := k) m hm C r,
        projectiveEvenOrthogonalRootWeight_equation (k := k) m hm C r⟩
    · intro chi hchi
      rw [← projectiveEvenOrthogonalRootWeight_range (k := k) m hm C] at hchi
      rcases hchi with ⟨r, rfl⟩
      exact ⟨r, rfl⟩
  · intro r
    exact ⟨projectiveEvenOrthogonalRootSubgroup_isTorusRootSubgroup
        (k := k) m hm C r,
      projectiveEvenOrthogonalRootWeight_equation (k := k) m hm C r⟩
  · intro r
    apply htauInjective
    change TorusCharacter.pullback
        (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
        (projectiveEvenOrthogonalRootWeight (k := k) m hm C
          ⟨(evenOrthogonalSeed m).neg r.down⟩) =
      TorusCharacter.pullback
        (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
        (projectiveEvenOrthogonalRootWeight (k := k) m hm C r)⁻¹
    rw [map_inv, projectiveEvenOrthogonalRootWeight_pullback,
      projectiveEvenOrthogonalRootWeight_pullback]
    exact hneg ⟨r.down⟩
  · intro r s t h
    apply htauInjective
    change TorusCharacter.pullback
        (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
        (projectiveEvenOrthogonalRootWeight (k := k) m hm C t) =
      TorusCharacter.pullback
        (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
        (projectiveEvenOrthogonalRootWeight (k := k) m hm C r *
          projectiveEvenOrthogonalRootWeight (k := k) m hm C s)
    rw [map_mul, projectiveEvenOrthogonalRootWeight_pullback,
      projectiveEvenOrthogonalRootWeight_pullback,
      projectiveEvenOrthogonalRootWeight_pullback]
    exact hadd ⟨r.down⟩ ⟨s.down⟩ ⟨t.down⟩ h
  · intro r s
    apply htauInjective
    change TorusCharacter.pullback
        (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
        (projectiveEvenOrthogonalRootWeight (k := k) m hm C
          ⟨((evenOrthogonalSeed m).reflectionPerm r.down) s.down⟩) =
      TorusCharacter.pullback
        (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
        (projectiveEvenOrthogonalRootWeight (k := k) m hm C s *
          projectiveEvenOrthogonalRootWeight (k := k) m hm C r ^
            (-evenOrthogonalRootPairingInt m s.down r.down))
    rw [map_mul, map_zpow, projectiveEvenOrthogonalRootWeight_pullback,
      projectiveEvenOrthogonalRootWeight_pullback,
      projectiveEvenOrthogonalRootWeight_pullback]
    exact hreflect ⟨r.down⟩ ⟨s.down⟩
  · intro r
    exact hself ⟨r.down⟩
  · intro r s
    change D.weightPairing
        (TorusCharacter.pullback
          (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C)
          (projectiveEvenOrthogonalRootWeight (k := k) m hm C r)) s =
      evenOrthogonalRootPairingInt m r.down s.down
    rw [projectiveEvenOrthogonalRootWeight_pullback]
    exact hpairing ⟨r.down⟩ ⟨s.down⟩
  · exact hheightNeg
  · exact hheightAdd
  · exact hpositive
  · exact hsimple
  · intro chi r
    have h := hcocharacter
      (TorusCharacter.pullback (projectiveEvenOrthogonalTorusMorphism (k := k) m hm C) chi) r
    intro t
    exact h t

private theorem projectiveEvenOrthogonalRootData_isActualBasedRootPairing
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    IsActualBasedRootPairing
      (projectiveEvenOrthogonalRootData (k := k) m hm C)
      (typeDRootPairingULift m :
        RootPairing (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
          (TypeDRootSpaceULift.{u} (m + 2))
          (TypeDCorootSpaceULift.{u} (m + 2)))
      (typeDRootPairingULiftBase m)
      (Equiv.refl (EvenOrthogonalRootIndex.{u} (m + 2))) := by
  letI := C.group
  rcases evenOrthogonalRootData_isActualBasedRootPairingULift (k := k) m hm with
    ⟨hpairing, hreflect, hneg, hsimple⟩
  exact ⟨hpairing, hreflect, hneg, hsimple⟩

public noncomputable def projectiveEvenOrthogonalRootSystemModel
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    RootSystemModel
      (typeDRootPairingULift m :
        RootPairing (EvenOrthogonalRootIndex.{u} (m + 2)) ℝ
          (TypeDRootSpaceULift.{u} (m + 2))
          (TypeDCorootSpaceULift.{u} (m + 2)))
      C.projective := by
  letI := C.group
  exact {
    torus := projectiveEvenOrthogonalTorus (k := k) m hm C
    maximalTorus := projectiveEvenOrthogonalTorus_isMaximalTorus (k := k) m hm C
    rootData := projectiveEvenOrthogonalRootData (k := k) m hm C
    realization := projectiveEvenOrthogonalRootData_isRealization (k := k) m hm C
    base := typeDRootPairingULiftBase m
    rootEquiv := Equiv.refl (EvenOrthogonalRootIndex.{u} (m + 2))
    actual := projectiveEvenOrthogonalRootData_isActualBasedRootPairing (k := k) m hm C
  }

private theorem projectiveEvenOrthogonal_isogenyTarget_isSemisimple
    (m : ℕ) (hm : 2 ≤ m) (C : ProjectiveEvenOrthogonalQuotientData (k := k) m hm) :
    letI := C.group
    IsSemisimpleAlgebraicGroup C.projective := by
  letI := C.group
  let S := projectiveEvenOrthogonalOmegaCarrier (k := k) m hm
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  have hSconn : Variety.IsConnected S.carrierVariety := by
    exact evenSpinActionImageClosedSubgroup_isConnected
      (standardHyperbolicSplit (k := k) (m + 2)) (by
        rw [standardHyperbolicSplit_rank]
        omega)
  have hQconn : Variety.IsConnected C.projective :=
    connected_of_surjective_morphism C.quotient hSconn C.quotient_isogeny.1
  exact isogeny_radical_image C.quotient C.quotient_isogeny hSconn hQconn
    (evenSpinActionImageClosedSubgroup_isSemisimple
      (standardHyperbolicSplit (k := k) (m + 2)) (by
        rw [standardHyperbolicSplit_rank]
        omega))

/-- The standard projective even-orthogonal quotient realizes the lifted type-D
root pairing in every rank. -/
public theorem exists_standard_projective_even_orthogonal_version
    {k : Type u} [Field k] [IsAlgClosed k] (m : ℕ) (hm : 2 ≤ m) :
    Nonempty (SemisimpleVersion (k := k)
      (typeDRootPairingULift m)) := by
  obtain ⟨C⟩ := projectiveEvenOrthogonalQuotientData_exists (k := k) m hm
  letI : AlgebraicGroup C.projective := C.group
  refine ⟨{
    carrier := C.projective
    group := C.group
    semisimple := projectiveEvenOrthogonal_isogenyTarget_isSemisimple
      (k := k) m hm C
    rootModel := projectiveEvenOrthogonalRootSystemModel (k := k) m hm C
  }⟩

/-- The chosen projective-Omega quotient root model for the lifted type-D pairing. -/
public noncomputable def standardEvenOrthogonalProjectiveOmegaCarrierRootSystemModelULift
    {k : Type u} [Field k] [IsAlgClosed k]
    (m : ℕ) (hm : 2 ≤ m) :
    let C := Classical.choice (projectiveEvenOrthogonalQuotientData_exists (k := k) m hm)
    letI := C.group
    RootSystemModel
      (typeDRootPairingULift m) C.projective := by
  let C := Classical.choice (projectiveEvenOrthogonalQuotientData_exists (k := k) m hm)
  letI := C.group
  exact projectiveEvenOrthogonalRootSystemModel (k := k) m hm C

/-- The chosen projective-Omega semisimple version for the lifted type-D pairing. -/
public noncomputable def standardEvenOrthogonalProjectiveOmegaVersionULift
    {k : Type u} [Field k] [IsAlgClosed k]
    (m : ℕ) (hm : 2 ≤ m) :
    SemisimpleVersion (k := k)
      (typeDRootPairingULift m) := by
  let C := Classical.choice (projectiveEvenOrthogonalQuotientData_exists (k := k) m hm)
  letI := C.group
  exact {
    carrier := C.projective
    group := C.group
    semisimple := projectiveEvenOrthogonal_isogenyTarget_isSemisimple
      (k := k) m hm C
    rootModel := projectiveEvenOrthogonalRootSystemModel (k := k) m hm C
  }

/-- The chosen projective-Omega root model over a universe-zero field. -/
public noncomputable def standardEvenOrthogonalProjectiveOmegaCarrierRootSystemModel
    {k₀ : Type} [Field k₀] [IsAlgClosed k₀]
    (m : ℕ) (hm : 2 ≤ m) :
    let C := Classical.choice (projectiveEvenOrthogonalQuotientData_exists (k := k₀) m hm)
    letI := C.group
    RootSystemModel (k := k₀) (typeDRootPairing m) C.projective := by
  let C := Classical.choice (projectiveEvenOrthogonalQuotientData_exists (k := k₀) m hm)
  letI := C.group
  exact RootSystemModel.transport
    (RootPairing.Equiv.symm _ _ (typeDRootPairingULiftEquiv m))
    (standardEvenOrthogonalProjectiveOmegaCarrierRootSystemModelULift
      (k := k₀) m hm)

/-- The chosen projective-Omega semisimple version over a universe-zero field. -/
public noncomputable def standardEvenOrthogonalProjectiveOmegaVersion
    {k₀ : Type} [Field k₀] [IsAlgClosed k₀]
    (m : ℕ) (hm : 2 ≤ m) :
    SemisimpleVersion (k := k₀) (typeDRootPairing m) := by
  let V := standardEvenOrthogonalProjectiveOmegaVersionULift
    (k := k₀) m hm
  exact SemisimpleVersion.transport
    (RootPairing.Equiv.symm _ _ (typeDRootPairingULiftEquiv m)) V

end

end Theory.AlgebraicGroup
