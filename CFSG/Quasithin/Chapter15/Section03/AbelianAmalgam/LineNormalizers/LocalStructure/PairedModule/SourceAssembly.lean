module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.SourceAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.PairedConsumer

/-!
# The paired module from the original local inputs

This assembles the module calculation before the temporary replacement in
15.3.67. The inputs are the preceding natural-action and local group facts;
the cubic norm, fixed lifts, and paired coordinates are all constructed.
The two summands are images of the original centralizers, and right
conjugation by the selected cubic element identifies the first with the
second, compatibly with the action of `C_E`.

The binary section is also identified with the actual image of `U` in
`G_E/E`. The offender section uses the genuine faithful quotient
`G_E/C_{G_E}(U)`, with normality relative to `G_E`. The representation on
the first summand factors through the actual centralizer-image coordinate;
no isomorphism type for that factor is required.

The parent of this conditional module calculation supplies the preceding
local inputs and retains assembly of the full 15.3.67.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1153,
PDF p.1170, the decomposition before the temporary replacement.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
open Descent.QuotientIdentification GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G]

/-- Preceding local facts on the original groups. In particular this contains
no fixed-lifting, norm, direct-sum, or paired-map assumption. -/
structure SourceInputs (V M Y T E : Subgroup G) (d : MarkedDecomposition Y T E) where
  natural : OrthogonalFourBinary.NaturalAction V M
  sylow_le : T ≤ M
  line_le : E ≤ V
  line_card : Nat.card E = 4
  singular : ∀ e : E, natural.singular ⟨e, line_le e.property⟩
  sylow_image : IsKleinFour (actionImage natural (lineT T E))
  span_eq : lineV V E = conjugateSpanBy V (lineC E)
  core_le : lineQ E ≤ T ⊓ centralizer (E : Set G)
  seed_commutator : ⁅V, T ⊓ centralizer (E : Set G)⁆ = E
  moved : lineV V E = ⁅lineV V E, lineY Y E⁆
  residual_image : ((lineY Y E).subgroupOf (lineNormalizer E)).map
    (d.equiv.toMonoidHom.comp (quotientMap E)) = (alternatingGroup (Fin 3)).prod ⊥
  tau_outside : d.tau ∉ T ⊓ centralizer (E : Set G)

namespace SourceInputs
variable {V M Y T E : Subgroup G} {d : MarkedDecomposition Y T E}
variable [IsMulCommutative V]
variable (s : SourceInputs V M Y T E d)

include s in
/-- The commutator bound is derived from the original centralizer span. -/
theorem core_commutator : ⁅lineV V E, lineQ E⁆ ≤ E :=
  core_commutator_le_line T V E s.line_le s.span_eq s.core_le s.seed_commutator.le

include s in
/-- Centralization takes place in the genuine relative quotient `G_E/E`. -/
theorem core_centralizes : lineQ E ≤ Descent.sectionKernel V E :=
  core_le_sectionKernel T V E s.line_le s.span_eq s.core_le s.seed_commutator.le

variable [IsElementaryAbelian 2 (lineV V E)]

/-- The chosen cubic actor, norm identity, and original fixed-point lifts. -/
noncomputable def actionData : ActionData V E d :=
  SourceAction.actionData s.natural d s.sylow_le s.line_le s.line_card s.singular
    s.sylow_image s.span_eq s.core_le s.seed_commutator s.moved s.residual_image s.tau_outside

/-- The selected original residual element has a nonidentity cubic quotient image. -/
theorem cubic_actor :
    (s.actionData.y : G) ∈ lineY Y E ∧
      orderOf (d.equiv (quotientMap E s.actionData.y)).1 = 3 ∧
      (d.equiv (quotientMap E s.actionData.y)).2 = 1 :=
  ⟨s.actionData.y_mem, s.actionData.y_order, s.actionData.y_second⟩

/-- The images of the original fixed subgroups are complementary. -/
theorem fixedImages :
    fixedImage V E d.tau ⊔
        fixedImage V E ((s.actionData.y : G)⁻¹ * d.tau * s.actionData.y) = ⊤ ∧
    fixedImage V E d.tau ⊓
        fixedImage V E ((s.actionData.y : G)⁻¹ * d.tau * s.actionData.y) = ⊥ :=
  ⟨fixedImages_sup V E d s.core_commutator s.actionData,
    fixedImages_inf V E d s.core_commutator s.actionData⟩

/-- Both actual fixed-subgroup images are invariant under the original centralizer. -/
theorem fixedImages_invariant (c : centralizer (E : Set G)) :
    (fixedImage V E d.tau).map
        (sectionRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c)) =
      fixedImage V E d.tau ∧
    (fixedImage V E ((s.actionData.y : G)⁻¹ * d.tau * s.actionData.y)).map
        (sectionRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c)) =
      fixedImage V E ((s.actionData.y : G)⁻¹ * d.tau * s.actionData.y) :=
  fixedImages_centralizer_invariant V E d s.core_commutator s.actionData c

/-- The source's right conjugation identifies the first image with the second. -/
noncomputable def fixedImageEquiv :
    fixedImage V E d.tau ≃ₗ[ZMod 2]
      fixedImage V E ((s.actionData.y : G)⁻¹ * d.tau * s.actionData.y) :=
  PairedModule.fixedImageEquiv V E d s.actionData

/-- The binary paired coordinates, with every action premise discharged. -/
noncomputable def pairedEquiv :
    SectionSpace V E ≃ₗ[ZMod 2] fixedImage V E d.tau × fixedImage V E d.tau :=
  PairedModule.pairedEquiv V E d s.core_commutator s.actionData

/-- The same coordinates on the actual image of `U` in `G_E/E`. -/
noncomputable def ambientPairedEquiv :
    Additive (ambientProjection V E s.line_le).range ≃ₗ[ZMod 2]
      fixedImage V E d.tau × fixedImage V E d.tau :=
  (sectionEquivAmbient V E s.line_le).symm.trans s.pairedEquiv

/-- The first-summand action uses only the actual centralizer-image coordinate. -/
noncomputable def sigma :
    Representation (ZMod 2) (lineNormalizer E ⧸ pCore 2 (lineNormalizer E))
      (fixedImage V E d.tau) :=
  PairedModule.sigma V E d s.core_commutator s.actionData

theorem sigma_first_factor (r : Equiv.Perm (Fin 3)) :
    s.sigma (d.equiv.symm (r, 1)) = 1 :=
  PairedModule.sigma_first_factor V E d s.core_commutator s.actionData r

/-- The two centralizer actions agree after right conjugation. -/
theorem fixedImageEquiv_centralizer (c : centralizer (E : Set G))
    (w : fixedImage V E d.tau) :
    (s.fixedImageEquiv
      (s.sigma (quotientMap E (inclusion (centralizer_le_normalizer (E : Set G)) c)) w) :
        SectionSpace V E) =
      sectionRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c)
        (s.fixedImageEquiv w : SectionSpace V E) :=
  PairedModule.fixedImageEquiv_centralizer V E d s.core_commutator s.actionData c w

/-- The original centralizer acts diagonally in the constructed coordinates. -/
theorem pairedEquiv_centralizer (c : centralizer (E : Set G)) (x : SectionSpace V E) :
    s.pairedEquiv
      (sectionRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c) x) =
      (s.sigma (quotientMap E (inclusion (centralizer_le_normalizer (E : Set G)) c))
        (s.pairedEquiv x).1,
       s.sigma (quotientMap E (inclusion (centralizer_le_normalizer (E : Set G)) c))
        (s.pairedEquiv x).2) :=
  PairedModule.pairedEquiv_centralizer V E d s.core_commutator s.actionData c x

/-- The paired map on the original elementary abelian group. -/
noncomputable def projection :
    Additive (lineV V E) →ₗ[ZMod 2] fixedImage V E d.tau × fixedImage V E d.tau :=
  pairedProjection V E d s.core_commutator s.actionData

/-- The actual quotient comparison preserves the marked projection. -/
theorem ambientPairedEquiv_projection (v : Additive (lineV V E)) :
    s.ambientPairedEquiv (ambientLinearProjection V E s.line_le v) = s.projection v := by
  change s.pairedEquiv ((sectionEquivAmbient V E s.line_le).symm
    (ambientLinearProjection V E s.line_le v)) = s.pairedEquiv (sectionProjection V E v)
  rw [← sectionEquivAmbient_projection V E s.line_le, LinearEquiv.symm_apply_apply]

theorem projection_surjective : Function.Surjective s.projection :=
  pairedProjection_surjective V E d s.core_commutator s.actionData

/-- The kernel is exactly the original line, not an unspecified subspace. -/
theorem projection_eq_zero_iff (v : Additive (lineV V E)) :
    s.projection v = 0 ↔ (v.toMul : G) ∈ E :=
  pairedProjection_eq_zero_iff V E d s.core_commutator s.actionData v

/-- The offender section for the genuine faithful conjugation quotient
`G_E/C_{G_E}(U)`. Its projection, kernel and equivariance are constructed. -/
noncomputable def pairedSection :
    letI := relativeSpan_normal V E s.line_le
    letI := relativeSpan_elementary V E s.line_le
    Offenders.PairedSection
      ((lineV V E).subgroupOf (lineNormalizer E)) (E.subgroupOf (lineNormalizer E))
      ((lineC E).subgroupOf (lineNormalizer E)) (pCore 2 (lineNormalizer E))
      (QuotientGroup.mk' (centralizer
        (((lineV V E).subgroupOf (lineNormalizer E)) : Set (lineNormalizer E))))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) s.sigma := by
  letI := relativeSpan_normal V E s.line_le
  letI := relativeSpan_elementary V E s.line_le
  exact PairedModule.pairedSection V E s.line_le d s.core_commutator s.actionData
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

end SourceInputs
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
