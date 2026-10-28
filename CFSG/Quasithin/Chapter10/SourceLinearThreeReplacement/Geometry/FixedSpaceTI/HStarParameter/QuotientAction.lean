module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Preparation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Transport

/-!
# The faithful action of the actual H-star centralizer quotient

The conjugation map onto Aut_H(U) has the literal kernel C_H(U). The first
isomorphism theorem therefore identifies the original quotient with this
actual induced automizer, and the binary representation acts on U itself.
Source: Aschbacher--Smith 10.3.1, printed pp.755--756.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)

include D hH

/-- The conjugation kernel on the ambient omega module agrees with the relative one. -/
theorem omega_actionMap_ker :
    (actionMap (omegaModule T H) H (le_normalizer_conjugateSpanBy _ _)).ker = omegaKernel T H := by
  rw [omegaKernel_eq D hH]
  ext h
  exact actionMap_eq_one_iff _ _ _ h

/-- The actual first isomorphism theorem, retaining the original quotient map. -/
def omegaActionEquiv : OmegaQuotient T H ≃* inducedAutomizer (omegaModule T H) H :=
  (QuotientGroup.quotientMulEquivOfEq (omega_actionMap_ker D hH).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (actionMap_surjective _ _ _))

theorem omegaActionEquiv_mk (h : H) :
    omegaActionEquiv D hH (QuotientGroup.mk' (omegaKernel T H) h) =
      actionMap (omegaModule T H) H (le_normalizer_conjugateSpanBy _ _) h := rfl

variable [IsElementaryAbelian 2 (omegaModule T H)]

/-- The faithful quotient action on the original ambient omega subgroup. -/
def omegaRepresentation : Representation (ZMod 2) (OmegaQuotient T H) (Additive (omegaModule T H)) :=
  ((automizerRepresentation (omegaModule T H)).comp (inducedAutomizer (omegaModule T H) H).subtype).comp
    (omegaActionEquiv D hH).toMonoidHom

theorem omegaRepresentation_injective : Function.Injective (omegaRepresentation D hH) :=
  (automizerRepresentation_injective _).comp
    (Subtype.val_injective.comp (omegaActionEquiv D hH).injective)

/-- Literal equivariance with conjugation, before changing any module coordinates. -/
theorem omegaRepresentation_apply (h : H) (v : Additive (omegaModule T H)) :
    ((omegaRepresentation D hH (QuotientGroup.mk' (omegaKernel T H) h) v).toMul : G) =
      h * (v.toMul : G) * (h : G)⁻¹ := rfl

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
