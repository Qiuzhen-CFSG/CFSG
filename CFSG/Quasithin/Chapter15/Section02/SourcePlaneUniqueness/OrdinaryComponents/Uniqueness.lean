module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels.PartnerExclusion

/-!
# Original distinguished-plane centralizer uniqueness

Failure of uniqueness selects a minimal escaping overgroup. Original
15.2.23 rules out characteristic two. The ordinary component model
exclusions leave J₄, whose literal fixed-subgroup two-residual supplies
a triple-Mathieu section of the original Kc. Original 15.2.12 makes Kc
solvable or gives it abelian Sylow three-subgroups; both forbid that section.
Thus every branch is discharged under the exact preceding source inputs.

The explicit premises are PlaneUniquenessPreceding, the full HStar wreath
quotients, the original Kc orbit and structural alternatives, the restricted
Suzuki-zero/Omega action alternative, and the plane inverter on the same
hsource and ZS. Their producers remain qt-e-152-plane-geometry and
qt-e-152-small-parabolic (including its quintic recognition input); their
final discharge remains with qt-e-152-chosen-action-contradiction. This
module does not assert that those preceding inputs have been constructed.

Source: Aschbacher--Smith, 15.2.15--24 and the final paragraph of the proof
of 15.2.15, printed pp.1112--1118, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- Original 15.2.15 under its exact preceding source packet, with both escaping branches proved. -/
theorem source_15_2_15 (d : PlaneUniquenessPreceding hsource H ZS)
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hstructural : ChosenGeometry.StructuralAlternatives T H Mc)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) :
    maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc} := by
  by_contra hne
  obtain ⟨R,hR,⟨e⟩⟩ := OrdinaryComponents.exists_mathieu_section_of_nonunique
    d hquotient horbit ha hi hne
  exact OrdinaryComponents.no_mathieu_section_in_partner d hstructural R hR e
end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
