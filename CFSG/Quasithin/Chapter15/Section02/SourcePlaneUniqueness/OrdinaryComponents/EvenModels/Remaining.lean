module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Source
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.G2
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Symplectic
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Ree
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Triality

/-!
# The remaining marked component after the general-field exclusions

Apply the intrinsic fixed-centralizer and solvable-Sylow bounds to the same
component selected from failure of original plane uniqueness. They exclude
all remaining G2, symplectic, triality and Ree parameters, including the
permitted central two-covers of G2(4). The Bender, nonbinary PSL3, central
PSL3(4)-cover and J4 rows remain, with their actual quotient and action.

This is checked progress toward 15.2.15, not its final contradiction.
The original HStar quotients, Kc orbit, restricted action and plane inverter
retain their existing geometry/small-parabolic producers and final discharge
by the chosen-action assembly.
Source: Aschbacher--Smith 15.2.24 and 15.2.15, pp.1117--1118, refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
open ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding

/-- The exact model/action rows still requiring exclusion on the selected component. -/
inductive ReducedModelAction115 (L : Type*) [Group L] (a : MulAut L) : Prop
  | bender (simple : IsSimpleGroup L) (model : IsBenderModel L)
      (inner : a ∈ (MulAut.conj (G := L)).range)
  | linear (simple : IsSimpleGroup L) (f : ℕ) (large : 2 ≤ f)
      (model : ClassicalGroup.IsPSL L 3 (2 ^ f))
      (inner : a ∈ (MulAut.conj (G := L)).range)
  | two_cover (nontrivial_center : center L ≠ ⊥) (center_eq : center L = pCore 2 L)
      (model : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4)
      (inner : a ∈ (MulAut.conj (G := L)).range)
  | janko_four (model : Nonempty ((L ⧸ pCore 2 L) ≃* Janko4.Model))
      (action : TwoCentralInner a)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Remove the general-field rows without changing the selected component or its action. -/
theorem reduced_model_action {P : Sylow 2 I} {z : G}
    (c : ComponentData (T := T) (Mc := Mc) I P z)
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : RefinedModelAction115 c.component a) : ReducedModelAction115 c.component a := by
  cases hm with
  | lie hs hm hi =>
    cases hm with
    | bender hm => exact .bender hs hm hi
    | linear f hf hm => exact .linear hs f hf hm hi
    | symplectic f hf hm =>
      exact (not_symplectic_component d c hI hP hz hzne a ha hs hf hm hi).elim
    | g2 f hf hm =>
      exact (not_g2_component d c hI hP hz hzne a ha hs hf hm hi).elim
    | triality f hf hm =>
      exact (not_triality_component d c hI hP hz hzne a ha hs hf hm hi).elim
    | ree m hm he => exact (not_ree_component d c hI hP hs hm he).elim
  | two_cover hn hc hm hi =>
    rcases hm with hm | hm
    · exact .two_cover hn hc hm hi
    · exact (not_g2_four_cover_component d c hI hP hz hzne a ha hm hi).elim
  | janko_four hm hi => exact .janko_four hm hi

/-- Failure of original plane uniqueness has only the remaining Bender, PSL3 and J4 rows. -/
theorem exists_reduced_component_of_nonunique
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
      ∃ (c : ComponentData (T := T) (Mc := Mc) I P z) (a : MulAut c.component),
        (∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) ∧
        ReducedModelAction115 c.component a := by
  obtain ⟨I,P,z,hI,hP,hz,hzne,c,a,ha,hm⟩ :=
    exists_refined_component_of_nonunique d hquotient horbit ha hi hne
  exact ⟨I,P,z,hI,hP,hz,hzne,c,a,ha,reduced_model_action d c hI.1 hP hz hzne a ha hm⟩

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
