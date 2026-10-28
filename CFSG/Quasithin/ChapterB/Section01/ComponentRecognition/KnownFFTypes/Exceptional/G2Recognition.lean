module

public import Theory.Representation.BinaryOffender.NormalizerExtension
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.Representation.BinaryOffender.QuasisimpleImage
public import Theory.GroupTheory.PerfectCentralCoverPGroupKernel

/-!
# Faithful-image and covering steps for the split G₂ branch of B.1.13

The original irreducible action may have a central kernel. Its faithful
image has the same central quotient, the same full linear normalizer, and
trivial two-core. The first theorem retains the supplied split-octonion
model and field when making that reduction.

For the covering step, compose L → L/Z(L) with the specified G₂ model
equivalence. A universal cover with two-group kernel makes this projection
injective when O₂(L) = 1. This allows the exceptional two-multiplier at
field order four; it does not assume that all universal kernels vanish.
Both project covering conventions are supported, and the resulting
equivalence agrees with the original quotient map on every element.

These are conditional covering deductions, not the full G₂ recognition
theorem. The odd-field FF exclusion and the even-field universal-kernel
calculation remain to be supplied. The latter belongs to the I.1.3–I.1.4
multiplier calculation, rather than to the representation image reduction.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74 (PDF pp.84–85), and
I.1.3–I.1.4, printed pp.407–408. B.1.13 cites Guralnick–Malle,
*Classification of 2F-modules, II*, Table 2, DOI 10.1515/9783110198126.117.
No classification statement from that paper is assumed or used here.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional
universe u v w
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
  {F : Type v} [Field F] [Finite F]

omit [Finite F] in
/-- The nonfaithful source action gives a faithful quasisimple FF image over the
same vector space, with the exact same G₂ central quotient and field. -/
theorem g2_faithful_image_input
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) L W)
    (hi : Representation.IsIrreducible σ) (hk : σ.ker ≤ center L)
    (hff : IsFFModule (normalizerRepresentation σ))
    (e : L ⧸ center L ≃* Atlas.G2.Model F) :
    IsQuasisimple (actionImage σ) ∧
      Representation.IsIrreducible (imageRepresentation σ) ∧
      Function.Injective (imageRepresentation σ) ∧
      pCore 2 (actionImage σ) = ⊥ ∧
      IsFFModule (normalizerRepresentation (imageRepresentation σ)) ∧
      Nonempty (actionImage σ ⧸ center (actionImage σ) ≃* Atlas.G2.Model F) := by
  exact ⟨actionImage_isQuasisimple σ hk, imageRepresentation_irreducible σ hi,
    imageRepresentation_injective σ, actionImage_twoCore_eq_bot σ hi,
    (normalizer_isFF_imageRepresentation_iff σ).mpr hff,
    ⟨(actionImageQuotientCenterEquiv σ hk).symm.trans e⟩⟩

/-- The covering map is the literal central projection followed by the given model map. -/
def g2Cover (e : L ⧸ center L ≃* Atlas.G2.Model F) :
    PerfectCentralCovering.Cover L (Atlas.G2.Model F) where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    exact (show e (QuotientGroup.mk x) = 1 from hx).trans (map_one e).symm

omit [Finite L] [Finite F] in
/-- The entire center, including any kernel invisible on W, is this cover's kernel. -/
@[simp] theorem g2Cover_ker (e : L ⧸ center L ≃* Atlas.G2.Model F) :
    (g2Cover e).toMonoidHom.ker = center L := by
  apply le_antisymm (g2Cover e).ker_le_center
  intro x hx
  change e (QuotientGroup.mk x) = 1
  rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]

variable {U : Type w} [Group U]

/-- Remove all central covering ambiguity from the two-primary multiplier input. -/
noncomputable def g2EquivOfUniversalTwoKernel
    (hc : pCore 2 L = ⊥) (e : L ⧸ center L ≃* Atlas.G2.Model F)
    (g : PerfectCentralCovering.Cover U (Atlas.G2.Model F))
    (hg : PerfectCentralCovering.IsUniversal.{w, v, u} g)
    (hp : IsPGroup 2 g.toMonoidHom.ker) : L ≃* Atlas.G2.Model F :=
  (g2Cover e).equivOfPCoreEqBotOfUniversalPGroup g hg hp hc

@[simp] theorem g2EquivOfUniversalTwoKernel_apply
    (hc : pCore 2 L = ⊥) (e : L ⧸ center L ≃* Atlas.G2.Model F)
    (g : PerfectCentralCovering.Cover U (Atlas.G2.Model F))
    (hg : PerfectCentralCovering.IsUniversal.{w, v, u} g)
    (hp : IsPGroup 2 g.toMonoidHom.ker) (x : L) :
    g2EquivOfUniversalTwoKernel hc e g hg hp x = e (QuotientGroup.mk x) := by
  unfold g2EquivOfUniversalTwoKernel
  rw [PerfectCentralCovering.Cover.equivOfPCoreEqBotOfUniversalPGroup_apply]
  rfl

/-- The original covering group is centerless once its two-primary multiplier is known. -/
theorem g2_center_eq_bot_of_universal_two_kernel
    (hc : pCore 2 L = ⊥) (e : L ⧸ center L ≃* Atlas.G2.Model F)
    (g : PerfectCentralCovering.Cover U (Atlas.G2.Model F))
    (hg : PerfectCentralCovering.IsUniversal.{w, v, u} g)
    (hp : IsPGroup 2 g.toMonoidHom.ker) : center L = ⊥ := by
  rw [← g2Cover_ker e]
  exact (MonoidHom.ker_eq_bot_iff _).mpr
    ((g2Cover e).injective_of_pCore_eq_bot_of_universal_pGroup g hg hp hc)

/-- The covering calculation also proves faithfulness of the original selected action. -/
theorem g2_action_faithful_of_universal_two_kernel
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) L W) (hk : σ.ker ≤ center L)
    (hc : pCore 2 L = ⊥) (e : L ⧸ center L ≃* Atlas.G2.Model F)
    (g : PerfectCentralCovering.Cover U (Atlas.G2.Model F))
    (hg : PerfectCentralCovering.IsUniversal.{w, v, u} g)
    (hp : IsPGroup 2 g.toMonoidHom.ker) : Function.Injective σ := by
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  exact bot_unique (hk.trans
    (g2_center_eq_bot_of_universal_two_kernel hc e g hg hp).le)

/-- The I.1 multiplier producer uses finite quasisimple universal covers.
This consumer takes precisely that convention and identifies L itself. -/
noncomputable def g2EquivOfQuasisimpleUniversalTwoKernel
    [Finite U] [IsQuasisimple U] [IsQuasisimple (Atlas.G2.Model F)]
    (hc : pCore 2 L = ⊥) (e : L ⧸ center L ≃* Atlas.G2.Model F)
    (g : Covering U (Atlas.G2.Model F))
    (hg : Covering.IsUniversal.{v, w, u} g)
    (hp : IsPGroup 2 g.toMonoidHom.ker) : L ≃* Atlas.G2.Model F :=
  Covering.equivOfPCoreEqBotOfUniversalPGroup
    (g2Cover e).toCovering g hg hp hc

@[simp] theorem g2EquivOfQuasisimpleUniversalTwoKernel_apply
    [Finite U] [IsQuasisimple U] [IsQuasisimple (Atlas.G2.Model F)]
    (hc : pCore 2 L = ⊥) (e : L ⧸ center L ≃* Atlas.G2.Model F)
    (g : Covering U (Atlas.G2.Model F))
    (hg : Covering.IsUniversal.{v, w, u} g)
    (hp : IsPGroup 2 g.toMonoidHom.ker) (x : L) :
    g2EquivOfQuasisimpleUniversalTwoKernel hc e g hg hp x =
      e (QuotientGroup.mk x) := by
  unfold g2EquivOfQuasisimpleUniversalTwoKernel
  rw [Covering.equivOfPCoreEqBotOfUniversalPGroup_apply]
  rfl

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional
