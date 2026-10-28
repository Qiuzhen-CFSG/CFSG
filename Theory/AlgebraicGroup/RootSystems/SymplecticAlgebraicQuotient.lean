module

public import Theory.AlgebraicGroup.Foundations
public import Theory.AlgebraicGroup.RootSystems.SymplecticClosedSubgroup
public import Theory.AlgebraicGroup.RootSystems.SymplecticCenter
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_4_c

/-!
# The standard symplectic algebraic-group quotient

For `V = (Fin m ⊕ Fin m) → k`, this module packages the closed matrix
subgroup preserving `Matrix.J` and the quotient by its point-group center in
every rank, including the trivial rank-zero carrier.
The polynomial carrier and its point-group equivalence come from
`SymplecticClosedSubgroup`; the center is finite by the scalar calculation in
`SymplecticCenter`.  Applying the general normal-closed-subgroup quotient
theorem then supplies a surjective morphism, its finite kernel, the universal
factorization property, and the quotient point-group equivalence.  These data
are assembled into the `SymplecticModel` interface used by the root-system
classification.
-/

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

/-- The quotient of the standard symplectic carrier by its center. -/
public theorem standardSymplecticQuotient_exists
    (m : ℕ) :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
      (q : AlgebraicGroup.Morphism
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety Q),
      IsIsogeny q ∧
      q.kernel = Subgroup.center
        (Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) ∧
      (∀ {H : Variety k} [AlgebraicGroup H]
        (f : AlgebraicGroup.Morphism
          (standardSymplecticClosedSubgroup (k := k) m).carrierVariety H),
        Subgroup.center
            (Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
          ≤ f.kernel →
          ∃! r : AlgebraicGroup.Morphism Q H, r.comp q = f) ∧
      (∃ e : Variety.Point Q ≃*
          Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety ⧸
            Subgroup.center
              (Variety.Point
                (standardSymplecticClosedSubgroup (k := k) m).carrierVariety),
        ∀ x, e (q.onPoints x) =
          QuotientGroup.mk'
            (Subgroup.center
              (Variety.Point
                (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)) x) := by
  let S := standardSymplecticClosedSubgroup (k := k) m
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  let e : Variety.Point S.carrierVariety ≃*
      bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m) :=
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
  obtain ⟨Q, hQ, q, hqsurj, hqker, hfactor⟩ :=
    theorem_1_1_2_b Z hZnormal
  letI : AlgebraicGroup Q := hQ
  have hkernelCenter : q.kernel =
      Subgroup.center (Variety.Point S.carrierVariety) := by
    rw [hqker]
    rfl
  have hqfinite : Finite q.kernel := by
    rw [hkernelCenter]
    infer_instance
  let e0 : (Variety.Point S.carrierVariety ⧸ q.kernel) ≃*
      Variety.Point Q :=
    QuotientGroup.quotientKerEquivOfSurjective q.onPoints hqsurj
  let e1 : (Variety.Point S.carrierVariety ⧸
      Subgroup.center (Variety.Point S.carrierVariety)) ≃*
      (Variety.Point S.carrierVariety ⧸ q.kernel) :=
    QuotientGroup.quotientMulEquivOfEq hkernelCenter.symm
  let eQ : Variety.Point Q ≃*
      Variety.Point S.carrierVariety ⧸
        Subgroup.center (Variety.Point S.carrierVariety) :=
    (e1.trans e0).symm
  have hfactor' :
      ∀ {H : Variety k} [AlgebraicGroup H]
        (f : AlgebraicGroup.Morphism S.carrierVariety H),
        Subgroup.center (Variety.Point S.carrierVariety) ≤ f.kernel →
          ∃! r : AlgebraicGroup.Morphism Q H, r.comp q = f := by
    intro H _ f hf
    apply hfactor (inferInstance : AlgebraicGroup H) f
    change Subgroup.center (Variety.Point S.carrierVariety) ≤ f.kernel
    exact hf
  refine ⟨Q, hQ, q, ⟨hqsurj, hqfinite⟩, hkernelCenter, hfactor', eQ, ?_⟩
  intro x
  change e1.symm (e0.symm (q.onPoints x)) = _
  apply e1.injective
  rw [e1.apply_symm_apply]
  apply e0.injective
  rw [e0.apply_symm_apply]
  change e0 (QuotientGroup.mk' q.kernel x) = q.onPoints x
  exact QuotientGroup.kerLift_mk q.onPoints x

/-- A concrete `SymplecticModel` for the standard alternating form. -/
public theorem standardSymplecticModel_exists
    (m : ℕ) :
    Nonempty (SymplecticModel
      (standardSymplecticBilinForm (k := k) m)) := by
  let S := standardSymplecticClosedSubgroup (k := k) m
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  let B := standardSymplecticBilinForm (k := k) m
  obtain ⟨Q, hQ, q, hqiso, hqker, hfactor, ⟨eQ, heQ⟩⟩ :=
    standardSymplecticQuotient_exists (k := k) m
  letI : AlgebraicGroup Q := hQ
  let eS : Variety.Point S.carrierVariety ≃* bilinearIsometrySubgroup B :=
    standardSymplecticClosedSubgroupPoints (k := k) m
  refine ⟨{
    basis := symplecticStandardBasis (k := k) m
    symplectic := S
    symplectic_carrier := fun g => standardSymplecticClosedSubgroup_carrier m g
    projectiveSymplectic := Q
    projectiveSymplecticAlgebraicGroup := hQ
    symplecticPoints := eS
    symplecticLinear_points := by
      intro x
      exact standardSymplecticClosedSubgroup_linear_points (k := k) m x
    quotient := q
    quotientIsogeny := hqiso
    quotientKernel := hqker
    quotientUniversal := hfactor
    projectiveSymplecticPoints := eQ
    projectiveSymplecticQuotient := heQ
  }⟩

end Theory.AlgebraicGroup
