module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.Source
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels

/-!
# The actual ordinary component after original15.2.23

Failure of distinguished-plane uniqueness selects a minimal escaping I.
The proved characteristic-two exclusion supplies F*(I) ≠ O₂(I), so the
ordinary extraction gives its actual component, faithful marked action,
central two-group and normal Sylow orbit. No characteristic-two exclusion
or component-existence premise remains in this source application.

The exact earlier HStar quotient, Kc orbit, restricted-action and plane
inverter inputs stay explicit. Their producers are the plane-geometry and
small-parabolic owners, with final discharge at the chosen-action assembly.
The even-model and sporadic eliminations remain with the plane-uniqueness
owner. This module does not assert uniqueness or construct15.2.24.

Source: Aschbacher--Smith, paragraph following15.2.23,
printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original ordinary component is constructed directly from failure of
uniqueness and the preceding source packet, using the completed15.2.23. -/
theorem exists_component_data_of_nonunique
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS)
    (hne : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) ≠ {Mc}) :
    ∃ (I : Subgroup G) (P : Sylow 2 I) (z : G),
      MinimalPlaneEscape Mc ZS I ∧
      (P : Subgroup I).map I.subtype = planeSylow T ZS ∧
      z ∈ centralInvolutions T ∧ z ≠ 1 ∧
      Nonempty (ComponentData (T := T) (Mc := Mc) I P z) := by
  obtain ⟨I,hI⟩ := d.exists_minimal_escape hne
  obtain ⟨P,z,hP,hz,hzne,hc⟩ := exists_component_data d hI
    (d.source_15_2_23 hquotient horbit hI.1 ha hi)
  exact ⟨I,P,z,hI,hP,hz,hzne,hc⟩

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
