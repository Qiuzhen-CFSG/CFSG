module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_4_b
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ClassicalPointGroups

/-!
This module isolates `theorem_1_10_4_c` from `Theory.AlgebraicGroup.RootSystems.AlgebraicGroups`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.

The odd Spin model below is explicitly scoped to `[Invertible (2 : k)]`.
Mathlib's characteristic-free definition of `spinGroup` is accompanied only
by a conjugation-range theorem requiring this characteristic-not-two instance,
namely `spinGroup.conjAct_smul_ι_mem_range_ι`.  The strengthened scope is
therefore part of the public model contract rather than a proof-local
assumption.
-/

universe u v w

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable local instance pslCarrierAlgebraicGroup (m : ℕ) :
    AlgebraicGroup
      (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierVariety :=
  (pslClosedSubgroupOf k (Fin (m + 1) → k)).carrierAlgebraicGroup

local instance torusNormalInNormalizer
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) :
    (T.toSubgroup.subgroupOf T.normalizer.toSubgroup).Normal :=
  T.toSubgroup.normal_in_normalizer

public theorem theorem_1_10_4_c
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] :
    ∃ n : ℕ, ∃ reps : Fin n → SemisimpleVersion (k := k) P,
      ∀ G : SemisimpleVersion (k := k) P,
        ∃ i, SemisimpleVersion.Isomorphic (P := P) G (reps i) := by sorry

public structure OddOrthogonalModel
    {V : Type u} [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) [Invertible (2 : k)] where
  basis : Module.Basis (Fin (Module.finrank k V)) k V
  cliffordBasis : Module.Basis
    (Fin (Module.finrank k (CliffordAlgebra Q))) k (CliffordAlgebra Q)
  spin : ClosedSubgroup (glVarietyOf k (CliffordAlgebra Q))
  spin_carrier : ∀ g, g ∈ spin.toSubgroup ↔
      ∃ x : spinGroup Q,
        LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
            (glPointEquivOf k (CliffordAlgebra Q) cliffordBasis g) =
          (spinGroup.toUnits x).mulLeftLinearEquiv k (CliffordAlgebra Q)
  specialOrthogonal : ClosedSubgroup (glVarietyOf k V)
  specialOrthogonal_carrier : ∀ g, g ∈ specialOrthogonal.toSubgroup ↔
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V basis g) ∈ specialOrthogonalPointGroup Q
  spinPoints : let := spin.carrierAlgebraicGroup
    Variety.Point spin.carrierVariety ≃* spinGroup Q
  specialOrthogonalPoints : let := specialOrthogonal.carrierAlgebraicGroup
    Variety.Point specialOrthogonal.carrierVariety ≃*
      specialOrthogonalPointGroup Q
  specialOrthogonalLinear_points :
    letI := specialOrthogonal.carrierAlgebraicGroup
    ∀ x,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V basis
            (specialOrthogonal.inclusion.onPoints x)) =
        (specialOrthogonalPoints x).1
  spinAction : spinGroup Q →* specialOrthogonalPointGroup Q
  spinAction_clifford : ∀ x v,
    CliffordAlgebra.ι Q ((spinAction x).1 v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q)
  spinCover : let := spin.carrierAlgebraicGroup
    letI := specialOrthogonal.carrierAlgebraicGroup
    AlgebraicGroup.Morphism spin.carrierVariety specialOrthogonal.carrierVariety
  spinCoverIsogeny : let := spin.carrierAlgebraicGroup
    letI := specialOrthogonal.carrierAlgebraicGroup
    IsIsogeny spinCover
  spinCover_points :
    letI := spin.carrierAlgebraicGroup
    letI := specialOrthogonal.carrierAlgebraicGroup
    ∀ x, specialOrthogonalPoints
        (spinCover.onPoints (spinPoints.symm x)) = spinAction x

public structure SymplecticModel
    {V : Type u} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) where
  basis : Module.Basis (Fin (Module.finrank k V)) k V
  symplectic : ClosedSubgroup (glVarietyOf k V)
  symplectic_carrier : ∀ g, g ∈ symplectic.toSubgroup ↔
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V basis g) ∈ bilinearIsometrySubgroup B
  projectiveSymplectic : Variety k
  projectiveSymplecticAlgebraicGroup : AlgebraicGroup projectiveSymplectic
  symplecticPoints : let := symplectic.carrierAlgebraicGroup
    Variety.Point symplectic.carrierVariety ≃*
      bilinearIsometrySubgroup B
  symplecticLinear_points :
    letI := symplectic.carrierAlgebraicGroup
    ∀ x,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V basis (symplectic.inclusion.onPoints x)) =
        (symplecticPoints x).1
  quotient : let := symplectic.carrierAlgebraicGroup
    letI := projectiveSymplecticAlgebraicGroup
    AlgebraicGroup.Morphism symplectic.carrierVariety projectiveSymplectic
  quotientIsogeny : let := symplectic.carrierAlgebraicGroup
    letI := projectiveSymplecticAlgebraicGroup
    IsIsogeny quotient
  quotientKernel : let := symplectic.carrierAlgebraicGroup
    letI := projectiveSymplecticAlgebraicGroup
    quotient.kernel = Subgroup.center (Variety.Point symplectic.carrierVariety)
  quotientUniversal : let := symplectic.carrierAlgebraicGroup
    letI := projectiveSymplecticAlgebraicGroup
    ∀ {H : Variety k} [AlgebraicGroup H]
      (f : AlgebraicGroup.Morphism symplectic.carrierVariety H),
      Subgroup.center (Variety.Point symplectic.carrierVariety) ≤ f.kernel →
        ∃! q : AlgebraicGroup.Morphism projectiveSymplectic H,
          q.comp quotient = f
  projectiveSymplecticPoints :
    letI := symplectic.carrierAlgebraicGroup
    letI := projectiveSymplecticAlgebraicGroup
    Variety.Point projectiveSymplectic ≃*
      Variety.Point symplectic.carrierVariety ⧸
        Subgroup.center (Variety.Point symplectic.carrierVariety)
  projectiveSymplecticQuotient :
    letI := symplectic.carrierAlgebraicGroup
    letI := projectiveSymplecticAlgebraicGroup
    ∀ x, projectiveSymplecticPoints (quotient.onPoints x) =
      QuotientGroup.mk'
        (Subgroup.center (Variety.Point symplectic.carrierVariety)) x

public structure EvenOrthogonalModel
    {V : Type u} [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) where
  basis : Module.Basis (Fin (Module.finrank k V)) k V
  cliffordBasis : Module.Basis
    (Fin (Module.finrank k (CliffordAlgebra Q))) k (CliffordAlgebra Q)
  spin : ClosedSubgroup (glVarietyOf k (CliffordAlgebra Q))
  spin_carrier : ∀ g, g ∈ spin.toSubgroup ↔
      ∃ x : spinGroup Q,
        LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
            (glPointEquivOf k (CliffordAlgebra Q) cliffordBasis g) =
          (spinGroup.toUnits x).mulLeftLinearEquiv k (CliffordAlgebra Q)
  omega : ClosedSubgroup (glVarietyOf k V)
  omega_carrier : ∀ g, g ∈ omega.toSubgroup ↔
      ∃ x : commutator (quadraticIsometrySubgroup Q),
        x.1.1 = LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V basis g)
  projectiveOmega : Variety k
  projectiveOmegaAlgebraicGroup : AlgebraicGroup projectiveOmega
  spinPoints : let := spin.carrierAlgebraicGroup
    Variety.Point spin.carrierVariety ≃* spinGroup Q
  omegaPoints : let := omega.carrierAlgebraicGroup
    Variety.Point omega.carrierVariety ≃*
      commutator (quadraticIsometrySubgroup Q)
  omegaLinear_points :
    letI := omega.carrierAlgebraicGroup
    ∀ x,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V basis (omega.inclusion.onPoints x)) =
        (omegaPoints x).1.1
  spinAction : spinGroup Q →* quadraticIsometrySubgroup Q
  spinAction_clifford : ∀ x v,
    CliffordAlgebra.ι Q ((spinAction x).1 v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q)
  spinCover : let := spin.carrierAlgebraicGroup
    letI := omega.carrierAlgebraicGroup
    AlgebraicGroup.Morphism spin.carrierVariety omega.carrierVariety
  spinCoverIsogeny : let := spin.carrierAlgebraicGroup
    letI := omega.carrierAlgebraicGroup
    IsIsogeny spinCover
  spinCover_points :
    letI := spin.carrierAlgebraicGroup
    letI := omega.carrierAlgebraicGroup
    ∀ x, (omegaPoints (spinCover.onPoints (spinPoints.symm x))).1 =
      spinAction x
  quotient : let := omega.carrierAlgebraicGroup
    letI := projectiveOmegaAlgebraicGroup
    AlgebraicGroup.Morphism omega.carrierVariety projectiveOmega
  quotientIsogeny : let := omega.carrierAlgebraicGroup
    letI := projectiveOmegaAlgebraicGroup
    IsIsogeny quotient
  quotientKernel : let := omega.carrierAlgebraicGroup
    letI := projectiveOmegaAlgebraicGroup
    quotient.kernel = Subgroup.center (Variety.Point omega.carrierVariety)
  quotientUniversal : let := omega.carrierAlgebraicGroup
    letI := projectiveOmegaAlgebraicGroup
    ∀ {H : Variety k} [AlgebraicGroup H]
      (f : AlgebraicGroup.Morphism omega.carrierVariety H),
      Subgroup.center (Variety.Point omega.carrierVariety) ≤ f.kernel →
        ∃! q : AlgebraicGroup.Morphism projectiveOmega H,
          q.comp quotient = f
  projectiveOmegaPoints :
    letI := omega.carrierAlgebraicGroup
    letI := projectiveOmegaAlgebraicGroup
    Variety.Point projectiveOmega ≃*
      Variety.Point omega.carrierVariety ⧸
        Subgroup.center (Variety.Point omega.carrierVariety)
  projectiveOmegaQuotient :
    letI := omega.carrierAlgebraicGroup
    letI := projectiveOmegaAlgebraicGroup
    ∀ x, projectiveOmegaPoints (quotient.onPoints x) =
      QuotientGroup.mk' (Subgroup.center (Variety.Point omega.carrierVariety)) x

end Theory.AlgebraicGroup
