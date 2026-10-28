module

public import Theory.SpecificGroups.PSL3.ProjectionKernel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The actual degree-three linear covering

Elementary generation makes SL₃ perfect, and the projective transvection
action makes PSL₃ simple. Thus the scalar quotient is a covering in the
finite quasisimple covering API. Perfectness also proves uniqueness of any
lift through a central extension, independently of the existence of lifts.

This is preparation for the linear cases of Aschbacher–Smith I.1.3–I.1.4,
printed pp.407–408, and GLS98 §6.1. No universality is asserted here: the
construction also exists at the exceptional field orders two and four.
-/

@[expose] public section

namespace Matrix.PSL3

open Theory.GroupTheory
open scoped MatrixGroups

variable (F : Type*) [Field F]

instance sl3_isQuasisimple : IsQuasisimple SL(3, F) where
  toIsPerfect := Atlas.sl_perfect 3 (by decide)
  simple := Atlas.psl_simple_high_rank 3 (by decide)

instance psl3_isQuasisimple : IsQuasisimple PSL(3, F) where
  toIsPerfect := Atlas.psl_perfect 3 (by decide)
  simple := by
    let : IsSimpleGroup PSL(3, F) := Atlas.psl_simple_high_rank 3 (by decide)
    have hz : Subgroup.center PSL(3, F) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot SL(3, F)
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).isSimpleGroup

/-- The scalar projection with its finite quasisimple covering structure. -/
def projectionCovering [Finite F] : Covering SL(3, F) PSL(3, F) where
  toMonoidHom := projection F
  surjective := projection_surjective F

@[simp] theorem projectionCovering_toMonoidHom [Finite F] :
    (projectionCovering F).toMonoidHom = projection F := rfl

@[simp] theorem projectionCovering_apply [Finite F] (x : SL(3, F)) :
    projectionCovering F x = projection F x := rfl

/-- Lifts from SL₃ through a central kernel are unique, even when the
extension is not finite or perfect. This does not assert existence. -/
theorem projection_lift_unique {E : Type*} [Group E]
    (f : E →* PSL(3, F)) (hc : f.ker ≤ Subgroup.center E)
    {s t : SL(3, F) →* E}
    (hs : f.comp s = projection F) (ht : f.comp t = projection F) : s = t :=
  PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq f hc s t (hs.trans ht.symm)

/-- A compatible lift onto a perfect central extension is automatically onto. -/
theorem projection_lift_surjective {E : Type*} [Group E] [Group.IsPerfect E]
    (f : E →* PSL(3, F)) (hc : f.ker ≤ Subgroup.center E)
    (s : SL(3, F) →* E) (hs : f.comp s = projection F) : Function.Surjective s :=
  PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    f s (hs ▸ projection_surjective F) hc

end Matrix.PSL3
