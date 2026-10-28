module

public import Theory.SpecificGroups.AlternatingSix.M10.IndexTwoExtension
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Cubic

/-!
# The marked normalizer alternatives from the original type-Ru setup

The source cubic quotient supplies the actual M₁₀ identification, and the
H-conjugate of the chosen involution supplies index two. Applying restriction
to the characteristic A₆ gives the two marked alternatives for the original
N_G(B)/B. Exclusion of the direct product is the following fusion argument.

Source: Aschbacher–Smith J.2.7(3), printed p.436 (PDF p.447).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The normalizer alternatives require only the original source setup and choices. -/
public theorem normalizer_marked_dichotomy_source :
    (∃ e : c.NormalizerQuotient ≃* AlternatingSix.ShadowLocal.AutA6,
      c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension) ∨
    (∃ e : c.NormalizerQuotient ≃*
        (Multiplicative (ZMod 2) × AlternatingSix.M10.extension),
      c.centralizerImage.map e.toMonoidHom =
        (⊥ : Subgroup (Multiplicative (ZMod 2))).prod ⊤) := by
  obtain ⟨eB, _⟩ := SourceCompletion.cubic_quotient c
  let eM := c.cubicEquivCentralizerImage.symm.trans eB
  obtain ⟨h, _, hv, hv2⟩ := SourceCompletion.exists_inverter c
  have hi := (c.normalizer_extension_of_inverter
    (SourceCompletion.B_card c) _ hv hv2).2.1
  exact AlternatingSix.M10.IndexTwoExtension.marked_dichotomy c.centralizerImage eM hi

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
