module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Inheritance
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.FixedSpaces
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.PairingData
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Pairing
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Thompson

/-!
# Marked geometry in the temporary line normalizer

The genuine original orthogonal action supplies `Y_E ∩ K ≤ Q_E`.
The marked elements, literal centralizer product and original conjugate span
then descend to the temporary normalizer. The binary quotient is the actual
`V_E/E`, with exact action kernel and fixed-space images retaining their
original representatives and right-conjugacy convention.

The original local inputs in `Geometry.OriginalData` now construct the marked
quotient factors and complementary images of the actual fixed subgroups.
Their paired coordinates give `OriginalData.pairedSection`, with kernel exactly
`E` and the actual centralizer acting diagonally. The first-summand action has
the original section kernel restricted to `C_H(E)`. Its actual action image is
identified with the centralizer action image on the whole section, and that
image acts faithfully on the first summand.

The paired fixed-codimension bound is connected to the existing offender
calculation. Raw fixed-space conjugacy, generation, intersections and the
denominator fixed line are re-exported for the independent transvection proof.
Only the quotient fixed images are asserted to be centralizer-invariant.
This is the conditional marked-geometry step; the original local inputs and
the separate transvection and terminal conclusions remain with source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry.OriginalData
variable {G D : Type*} [Group G] [Group D] [Finite G]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
attribute [local instance] temporaryCore_normal

local notation "H" => temporaryLineNormalizer T V E
local notation "U" => Subgroup.subgroupOf (lineV V E) H
local notation "E₀" => Subgroup.subgroupOf E H
local notation "C" => Subgroup.subgroupOf (temporaryCentralizer T V E) H
local notation "Q" => Subgroup.subgroupOf (temporaryCore T V E) H

/-- The original marked action supplies the residual section-kernel bound. -/
theorem residual_section_kernel_le_core (d : OriginalData Y T V M E Pc) :
    lineY Y E ⊓ Descent.sectionKernel V E ≤ lineQ E :=
  lineY_inf_sectionKernel_le_lineQ d.action Y E d.Y_le d.line_le d.line_card
    d.singular d.residual_image d.residual_kernel d.residual_normal

/-- The temporary core is the original centralizer of the section in T. -/
theorem temporaryCore_eq_sectionCentralizer (d : OriginalData Y T V M E Pc) :
    temporaryCore T V E = lineQuotientCentralizer T V E :=
  temporaryCore_eq_of_original_action d.action Y T E d.Y_le d.line_le d.line_card
    d.singular d.residual_image d.residual_kernel d.residual_normal d.module_le_sylow
    d.sylow d.sylow_image d.core_le_kernel d.local_core d.seed_commutator

variable (d : OriginalData Y T V M E Pc)
  (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
  (hker : f.ker = centralizer
    ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))

/-- Extend the actual centralizer action on the first fixed image through the marked
product. The residual marking is chosen from the original nontrivial image. -/
noncomputable def pairedRepresentation :
    let := d.module_elementary
    Representation (ZMod 2) (H ⧸ Q) (MarkedSection.fixedImage U E₀ d.tau) := by
  let := d.module_normal
  let := d.module_elementary
  let := d.line_normal
  exact (d.chosenPairedGeometry f hf hker).representation

/-- The constructed paired quotient in H, from original local inputs alone.
Its map is onto the two actual fixed-image coordinates and has kernel exactly E. -/
noncomputable def pairedSection :
    let := d.module_normal
    let := d.module_elementary
    PairedSection U E₀ C Q f hf hker (d.pairedRepresentation f hf hker) := by
  let := d.module_normal
  let := d.module_elementary
  let := d.line_normal
  exact (d.chosenPairedGeometry f hf hker).pairedSection

/-- Restriction of the extension is the action of the actual centralizer on the
literal first fixed image in U/E. -/
theorem pairedRepresentation_centralizer :
    let := d.module_normal
    let := d.module_elementary
    let := d.line_normal
    (d.pairedRepresentation f hf hker).comp
      ((QuotientGroup.mk' Q).comp (C).subtype) =
        (d.chosenPairedGeometry f hf hker).centralizerAction := by
  let := d.module_normal
  let := d.module_elementary
  let := d.line_normal
  apply MonoidHom.ext
  intro c
  exact (d.chosenPairedGeometry f hf hker).representation_mk c

/-- On the actual centralizer, the constructed representation has precisely the
original section kernel K restricted first to H and then to C_H(E). -/
theorem pairedRepresentation_centralizer_ker :
    let := d.module_elementary
    ((d.pairedRepresentation f hf hker).comp
      ((QuotientGroup.mk' Q).comp (C).subtype)).ker =
        ((Descent.sectionKernel V E).subgroupOf H).subgroupOf C := by
  let := d.module_normal
  let := d.module_elementary
  let := d.line_normal
  rw [d.pairedRepresentation_centralizer, PairedGeometry.centralizerAction_ker,
    temporary_section_action_ker T V E d.span_le_temporary f hf hker]

/-- The actual centralizer image on U/E is identified with its image on the first
fixed image, using the same original centralizer elements on both sides. -/
noncomputable def pairedActionImageEquiv :
    let := d.module_normal
    let := d.module_elementary
    let := d.line_normal
    Representation.BinaryOffender.actionSubgroup (MarkedSection.action U E₀ f hf hker) C ≃*
      Representation.BinaryOffender.actionImage
        ((d.pairedRepresentation f hf hker).comp
          ((QuotientGroup.mk' Q).comp (C).subtype)) := by
  let := d.module_normal
  let := d.module_elementary
  let := d.line_normal
  rw [d.pairedRepresentation_centralizer]
  exact (d.chosenPairedGeometry f hf hker).actionImageEquiv

/-- Faithfulness on the actual centralizer action image, without an unsupported
faithfulness assertion for the extension on all of H/Q. -/
theorem pairedActionImage_faithful :
    let := d.module_normal
    let := d.module_elementary
    let := d.line_normal
    Function.Injective (d.chosenPairedGeometry f hf hker).faithfulRepresentation := by
  let := d.module_normal
  let := d.module_elementary
  let := d.line_normal
  exact (d.chosenPairedGeometry f hf hker).faithfulRepresentation_injective

/-- The marked pairing gives the fixed-codimension comparison for every actual
centralizer subgroup used in the subsequent offender calculation. -/
theorem paired_fixedCodim_bound (A : Subgroup H) (hAC : A ≤ C) :
    let := d.module_elementary
    2 * Representation.BinaryOffender.fixedCodim
        (d.pairedRepresentation f hf hker) (A.map (QuotientGroup.mk' Q)) ≤
      quotientRank U (U ⊓ centralizer (A : Set H)) := by
  let := d.module_normal
  let := d.module_elementary
  exact (d.pairedSection f hf hker).fixedCodim_bound A hAC

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry.OriginalData
