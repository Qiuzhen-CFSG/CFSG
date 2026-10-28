module

public import Theory.SpecificGroups.SU3.TernaryPerfectCover
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# The binary derived G₂ central-core quotient

A finite perfect group with central-core quotient G₂(2)′ has the same
quotient after dividing out only O₂. The induced map on L/O₂(L) is a
perfect central cover. Its kernel is a two-group by the actual ternary
unitary covering calculation, hence lies in the trivial two-core of that
quotient. The resulting isomorphism retains the original quotient map.

Source: Aschbacher--Smith C.1.31--32, printed pp.135--136, and the
perfect-cover consequence of I.1.3, printed p.407. This establishes the
quotient identification only; it makes no assertion about the commutator
module required in the G₂ block classification.
-/

public section
open Subgroup
namespace Atlas.G2.BinaryCentralCore
variable {L : Type*} [Group L]
private noncomputable def coreProjection
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Model (ZMod 2))) :
    (L ⧸ pCore 2 L) →* commutator (Model (ZMod 2)) :=
  QuotientGroup.lift (pCore 2 L)
    (e.toMonoidHom.comp (QuotientGroup.mk' (centralPreimage (pCore 2 L)))) (by
      intro x hx
      change e (QuotientGroup.mk' _ x) = 1
      apply e.map_eq_one_iff.mpr
      exact (QuotientGroup.eq_one_iff x).mpr (le_centralPreimage _ hx))

private theorem coreProjection_surjective
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Model (ZMod 2))) :
    Function.Surjective (coreProjection e) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) _

private theorem coreProjection_ker
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Model (ZMod 2))) :
    (coreProjection e).ker = center (L ⧸ pCore 2 L) := by
  ext x
  induction x using Quotient.inductionOn with
  | h x =>
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ centralPreimage (pCore 2 L)
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x

variable [Finite L] [Group.IsPerfect L]

private theorem coreProjection_injective
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Model (ZMod 2))) :
    Function.Injective (coreProjection e) := by
  let f : PerfectCentralCovering.Cover (L ⧸ pCore 2 L)
      (commutator (Model (ZMod 2))) := {
    toMonoidHom := coreProjection e
    surjective := coreProjection_surjective e
    isPerfect := inferInstance
    ker_le_center := (coreProjection_ker e).le }
  have hk := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup f
  apply (coreProjection e).ker_eq_bot_iff.mp
  apply bot_unique
  exact (show f.toMonoidHom.ker ≤ pCore 2 (L ⧸ pCore 2 L) from
    le_sSup ⟨inferInstance, hk⟩).trans_eq (pCore_quotient_pCore_eq_bot 2)

/-- The literal central-core projection is an isomorphism after dividing out
only O₂(L); no block-module assumption is required. -/
noncomputable def coreQuotientEquiv
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Model (ZMod 2))) :
    (L ⧸ pCore 2 L) ≃* commutator (Model (ZMod 2)) :=
  MulEquiv.ofBijective (coreProjection e)
    ⟨coreProjection_injective e, coreProjection_surjective e⟩

/-- The lifted marking agrees with the original projection on every element. -/
theorem coreQuotientEquiv_apply
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Model (ZMod 2))) (l : L) :
    coreQuotientEquiv e (QuotientGroup.mk' (pCore 2 L) l) =
      e (QuotientGroup.mk' (centralPreimage (pCore 2 L)) l) := by
  rfl

/-- There is no central extension left above the intrinsic two-core. -/
theorem centralPreimage_eq
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Model (ZMod 2))) :
    centralPreimage (pCore 2 L) = pCore 2 L := by
  have hc : center (L ⧸ pCore 2 L) = ⊥ :=
    (coreProjection_ker e).symm.trans
      ((coreProjection e).ker_eq_bot_iff.mpr (coreProjection_injective e))
  change (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' _) = _
  rw [hc]
  exact QuotientGroup.ker_mk' _

end Atlas.G2.BinaryCentralCore
