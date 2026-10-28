module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.CoreStructure
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Placement

/-!
# Assembly of the local L₄(2) extension from octad geometry

Common-octad placement and the intrinsic perfect/elementary-core structure
give B equal to an octad stabilizer. Its proved order and the supplied
L₄(2) quotient identify O₂(B) with E16. The normal kernel and quotient are
the actual intrinsic ones; no splitting is used.

The proved native octad placement and core structure discharge both geometric
contracts in `mathieuLocalFourExtension`. This establishes the L₄(2) section
case of A.3.12(14) from the source-local hypotheses alone.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.12(14),
printed pp.47–48; GLS, volume 3, Table 5.3e.
-/

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer

open Sporadic.Mathieu.M24LocalGeometry

/-- The exact local extension follows once the two independent geometric
obligations have been established. -/
public theorem mathieuLocalFourExtension_of_octad_geometry
    (hplacement : MathieuLocalSections.OctadPlacement)
    (hstructure : MathieuLocalSections.OctadCoreStructure) :
    MathieuLocalFourExtensionTheorem := by
  intro B S hB hlocal
  obtain ⟨O, hO⟩ := hplacement B S hB hlocal
  obtain ⟨hperfect, helementary⟩ := hstructure O
  have he := MathieuLocalSections.eq_of_local_of_join_le B (octadStabilizer O) S
    hB hlocal hO (octadStabilizer_card O) hperfect
  subst B
  exact MathieuLocalSections.extension_of_card_and_elementary_core _ hB
    (octadStabilizer_card O) helementary

/-- A source-local L₄(2) section in the native M₂₄ is an extension of E₁₆
by its specified L₄(2) quotient. The normal kernel is the intrinsic O₂(B). -/
public theorem mathieuLocalFourExtension : MathieuLocalFourExtensionTheorem :=
  mathieuLocalFourExtension_of_octad_geometry
    MathieuLocalSections.octadPlacement MathieuLocalSections.octadCoreStructure

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
