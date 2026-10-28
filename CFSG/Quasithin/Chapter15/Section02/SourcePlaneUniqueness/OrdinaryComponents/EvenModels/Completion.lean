module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Remaining
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Bender
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels.JankoResidual

/-!
# Completion of the ordinary characteristic-two model exclusions

The actual minimal escaping component has only its J₄ row left after
the Bender and nonbinary PSL₃ exclusions. This constructs the terminal
model/action conclusion of 15.2.24, rather than assuming it. Failure of
plane uniqueness therefore produces the literal triple-Mathieu section
inside the original Kc. Its final incompatibility with 15.2.12 remains
a separate mathematical step.

All earlier HStar quotient, Kc orbit, restricted-action and plane-inverter
premises retain their original geometry/small-parabolic producers and
final discharge by the chosen-action assembly.
Source: Aschbacher--Smith 15.2.24 and proof of 15.2.15, pp.1117--1118.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
open ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The actual minimal escaping component has only the J₄ row left. -/
theorem janko_four_of_reduced_model_action {P : Sylow 2 I} {z : G}
    (c : ComponentData (T := T) (Mc := Mc) I P z)
    (hI : MinimalPlaneEscape Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : ReducedModelAction115 c.component a) :
    Nonempty ((c.component ⧸ pCore 2 c.component) ≃* Janko4.Model) ∧
      TwoCentralInner a := by
  cases hm with
  | bender hs hm hi => exact (not_bender_component d c hI hP hz hzne a ha hs hm hi).elim
  | linear hs n hn hm hi =>
    exact (not_even_linear_three_component d c hI hP hz hzne a ha hs hn hm hi).elim
  | two_cover hn hc hm hi =>
    exact (not_linear_three_quotient_component d c hI hP hz hzne a ha
      (n := 2) (by decide) hm hi).elim
  | janko_four hm hi => exact ⟨hm,hi⟩

/-- Construct the original terminal model/action conclusion on the selected component. -/
theorem terminal_model_action {P : Sylow 2 I} {z : G}
    (c : ComponentData (T := T) (Mc := Mc) I P z)
    (hI : MinimalPlaneEscape Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1) :
    HasTerminalModelAction115 c.component z := by
  obtain ⟨a,ha,hm⟩ := component_refined_model_remainder d c hI.1 hP hz hzne
  have hr := reduced_model_action d c hI.1 hP hz hzne a ha hm
  obtain ⟨he,hi⟩ := janko_four_of_reduced_model_action d c hI hP hz hzne a ha hr
  exact ⟨a,ha,.sporadic .j4 (by intro he; cases he) he hi⟩

/-- Failure of distinguished-plane uniqueness forces the genuine triple-Mathieu section in Kc. -/
theorem exists_mathieu_section_of_nonunique
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
    ∃ R : Subgroup G, R ≤ smallActionKc H Mc ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* M22TripleCover) := by
  obtain ⟨I,P,z,hI,hP,hz,hzne,c,a,ha,hm⟩ :=
    exists_reduced_component_of_nonunique d hquotient horbit ha hi hne
  obtain ⟨⟨e⟩,hai⟩ := janko_four_of_reduced_model_action d c hI hP hz hzne a ha hm
  exact ⟨markedFixedResidual c a,
    janko_four_residual_section_in_Kc d c hI.1 hz hzne a ha e hai⟩
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
