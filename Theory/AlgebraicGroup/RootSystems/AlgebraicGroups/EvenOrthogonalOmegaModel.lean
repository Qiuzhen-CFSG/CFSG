module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalSpinModel
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalOmegaSemisimple
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ProjectiveOmegaQuotient
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_4_c

/-!
# The algebraic split even-orthogonal Omega model

The split Clifford carrier and the characteristic-free Spin action provide a
closed image in the general-linear variety of the quadratic space.  In split
rank at least four, the image has exactly the points of the commutator subgroup
of the quadratic-isometry group, and the Spin cover is an isogeny with finite
kernel.  This module packages those interfaces into the `EvenOrthogonalModel`
structure.  The projective target is obtained from the center quotient using
the characteristic-free semisimplicity theorem for the Omega carrier, so the
constructor needs no separate structural hypothesis and does not use the
type-D root classification.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

/-- Package the split Spin carrier, its exact Omega image, and the projective
central quotient into the concrete even-orthogonal model interface. -/
public noncomputable def evenOrthogonalOmegaModel
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    EvenOrthogonalModel Q := by
  let M := splitEvenOrthogonalSpinModel s hrank
  let S := M.spin
  let I := M.omega
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  have hsemisimple : IsSemisimpleAlgebraicGroup I.carrierVariety := by
    change IsSemisimpleAlgebraicGroup
      (evenSpinActionImageClosedSubgroup Q s).carrierVariety
    exact evenSpinActionImageClosedSubgroup_isSemisimple s hrank
  let hExists := projectiveOmegaQuotient_exists I hsemisimple
  let P : Variety k := Classical.choose hExists
  have hExistsP : ∃ (_ : AlgebraicGroup P) (q :
      AlgebraicGroup.Morphism I.carrierVariety P),
      IsIsogeny q ∧
        q.kernel = Subgroup.center (Variety.Point I.carrierVariety) ∧
        (∀ {H : Variety k} [AlgebraicGroup H]
          (f : AlgebraicGroup.Morphism I.carrierVariety H),
          Subgroup.center (Variety.Point I.carrierVariety) ≤ f.kernel →
            ∃! r : AlgebraicGroup.Morphism P H, r.comp q = f) ∧
        ∃ eP : Variety.Point P ≃*
            Variety.Point I.carrierVariety ⧸
              Subgroup.center (Variety.Point I.carrierVariety),
          ∀ x, eP (q.onPoints x) =
            QuotientGroup.mk' (Subgroup.center (Variety.Point I.carrierVariety)) x :=
    Classical.choose_spec hExists
  let hP : AlgebraicGroup P := Classical.choose hExistsP
  let hExistsQ : ∃ (q : AlgebraicGroup.Morphism I.carrierVariety P),
      IsIsogeny q ∧
        q.kernel = Subgroup.center (Variety.Point I.carrierVariety) ∧
        (∀ {H : Variety k} [AlgebraicGroup H]
          (f : AlgebraicGroup.Morphism I.carrierVariety H),
          Subgroup.center (Variety.Point I.carrierVariety) ≤ f.kernel →
            ∃! r : AlgebraicGroup.Morphism P H, r.comp q = f) ∧
        ∃ eP : Variety.Point P ≃*
            Variety.Point I.carrierVariety ⧸
              Subgroup.center (Variety.Point I.carrierVariety),
          ∀ x, eP (q.onPoints x) =
            QuotientGroup.mk' (Subgroup.center (Variety.Point I.carrierVariety)) x :=
    Classical.choose_spec hExistsP
  let q : AlgebraicGroup.Morphism I.carrierVariety P := Classical.choose hExistsQ
  have hqData := Classical.choose_spec hExistsQ
  let hq : IsIsogeny q := hqData.1
  let hker : q.kernel = Subgroup.center (Variety.Point I.carrierVariety) := hqData.2.1
  let hfactor :
      ∀ {H : Variety k} [AlgebraicGroup H]
        (f : AlgebraicGroup.Morphism I.carrierVariety H),
        Subgroup.center (Variety.Point I.carrierVariety) ≤ f.kernel →
          ∃! r : AlgebraicGroup.Morphism P H, r.comp q = f := hqData.2.2.1
  let eData : ∃ eP : Variety.Point P ≃*
      Variety.Point I.carrierVariety ⧸
        Subgroup.center (Variety.Point I.carrierVariety),
      ∀ x, eP (q.onPoints x) =
        QuotientGroup.mk' (Subgroup.center (Variety.Point I.carrierVariety)) x :=
    hqData.2.2.2
  let eP : Variety.Point P ≃*
      Variety.Point I.carrierVariety ⧸
        Subgroup.center (Variety.Point I.carrierVariety) := Classical.choose eData
  have heP := Classical.choose_spec eData
  letI : AlgebraicGroup P := hP
  exact {
    basis := M.basis
    cliffordBasis := M.cliffordBasis
    spin := M.spin
    spin_carrier := M.spin_carrier
    omega := M.omega
    omega_carrier := M.omega_carrier
    projectiveOmega := P
    projectiveOmegaAlgebraicGroup := hP
    spinPoints := M.spinPoints
    omegaPoints := M.omegaPoints
    omegaLinear_points := M.omegaLinear_points
    spinAction := M.spinAction
    spinAction_clifford := M.spinAction_clifford
    spinCover := M.spinCover
    spinCoverIsogeny := M.spinCoverIsogeny
    spinCover_points := M.spinCover_points
    quotient := q
    quotientIsogeny := hq
    quotientKernel := hker
    quotientUniversal := hfactor
    projectiveOmegaPoints := eP
    projectiveOmegaQuotient := heP
  }

end Theory.AlgebraicGroup
