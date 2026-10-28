module

public import Theory.AlgebraicGroup.Foundations
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_4_c

universe u

set_option linter.style.haveILetI false

/-!
The projective Omega target is the geometric quotient of the Omega carrier by
its full point-group center.  For a connected semisimple Omega carrier, the
center is the top centralizer, hence normal and finite.  The proved closed-
subgroup quotient theorem supplies the quotient morphism and its categorical
factorization property; the standard quotient-group equivalence then records
the point-level model and its compatibility with `QuotientGroup.mk'`.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem projectiveOmegaQuotient_exists
    {G : Variety k} [AlgebraicGroup G] (omega : ClosedSubgroup G)
    (hOmega : IsSemisimpleAlgebraicGroup omega.carrierVariety) :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
      (q : AlgebraicGroup.Morphism omega.carrierVariety Q),
      IsIsogeny q ∧
      q.kernel = Subgroup.center (Variety.Point omega.carrierVariety) ∧
      (∀ {H : Variety k} [AlgebraicGroup H]
        (f : AlgebraicGroup.Morphism omega.carrierVariety H),
        Subgroup.center (Variety.Point omega.carrierVariety) ≤ f.kernel →
          ∃! r : AlgebraicGroup.Morphism Q H, r.comp q = f) ∧
      (∃ e : Variety.Point Q ≃*
          Variety.Point omega.carrierVariety ⧸
            Subgroup.center (Variety.Point omega.carrierVariety),
        ∀ x, e (q.onPoints x) =
          QuotientGroup.mk' (Subgroup.center (Variety.Point omega.carrierVariety)) x) := by
  let Z : ClosedSubgroup omega.carrierVariety :=
    (ClosedSubgroup.top (G := omega.carrierVariety)).centralizer
  have hZ : Z.toSubgroup =
      Subgroup.center (Variety.Point omega.carrierVariety) := by
    change Subgroup.centralizer
      ((ClosedSubgroup.top (G := omega.carrierVariety)).toSubgroup :
        Set (Variety.Point omega.carrierVariety)) = _
    rw [show (ClosedSubgroup.top (G := omega.carrierVariety)).toSubgroup = ⊤ by rfl,
      Subgroup.coe_top, Subgroup.centralizer_univ]
  have hZnormal : Z.toSubgroup.Normal := by
    constructor
    intro z hz g
    have hzCenter := Subgroup.mem_center_iff.mp (hZ ▸ hz) g
    rw [hzCenter]
    simpa using hz
  obtain ⟨Q, hQ, q, hqsurj, hqker, hfactor⟩ :=
    theorem_1_1_2_b Z hZnormal
  letI : AlgebraicGroup Q := hQ
  letI : Finite (Subgroup.center (Variety.Point omega.carrierVariety)) :=
    connectedSemisimple_center_finite hOmega
  have hkernelCenter : q.kernel =
      Subgroup.center (Variety.Point omega.carrierVariety) := hqker.trans hZ
  have hqfinite : Finite q.kernel := by
    rw [hkernelCenter]
    infer_instance
  let e0 : (Variety.Point omega.carrierVariety ⧸ q.kernel) ≃*
      Variety.Point Q :=
    QuotientGroup.quotientKerEquivOfSurjective q.onPoints hqsurj
  let e1 : (Variety.Point omega.carrierVariety ⧸
      Subgroup.center (Variety.Point omega.carrierVariety)) ≃*
      (Variety.Point omega.carrierVariety ⧸ q.kernel) :=
    QuotientGroup.quotientMulEquivOfEq hkernelCenter.symm
  let e : Variety.Point Q ≃*
      Variety.Point omega.carrierVariety ⧸
        Subgroup.center (Variety.Point omega.carrierVariety) :=
    (e1.trans e0).symm
  have hfactor' :
      ∀ {H : Variety k} [AlgebraicGroup H]
        (f : AlgebraicGroup.Morphism omega.carrierVariety H),
        Subgroup.center (Variety.Point omega.carrierVariety) ≤ f.kernel →
          ∃! r : AlgebraicGroup.Morphism Q H, r.comp q = f := by
    intro H _ f hf
    apply hfactor (inferInstance : AlgebraicGroup H) f
    change Z.toSubgroup ≤ f.kernel
    simpa only [hZ] using hf
  refine ⟨Q, hQ, q, ⟨hqsurj, hqfinite⟩, hkernelCenter, hfactor', e, ?_⟩
  intro x
  change e1.symm (e0.symm (q.onPoints x)) = _
  apply e1.injective
  rw [e1.apply_symm_apply]
  apply e0.injective
  rw [e0.apply_symm_apply]
  change e0 (QuotientGroup.mk' q.kernel x) = q.onPoints x
  exact QuotientGroup.kerLift_mk q.onPoints x

end Theory.AlgebraicGroup
