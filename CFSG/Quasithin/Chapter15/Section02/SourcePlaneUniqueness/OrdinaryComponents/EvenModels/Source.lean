module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Remainder
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.SmallDerived
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.BinaryThree

/-!
# Remaining even components after the binary and small-derived exclusions

The binary PSL3, PSL4 and PSL5 rows and all three small-derived rows are
excluded on the same ordinary component selected from failure of plane
uniqueness. Each surviving row retains a full model isomorphism, its field
parameter, and the original marked action. The general-field, triality and
central-cover branches, and the final J4 residual section, remain obligations.

The original preceding HStar quotients, Kc orbit, restricted action and plane
inverter retain their plane-geometry and small-parabolic producers and final
discharge by the chosen-action assembly. This is a reduction of15.2.15,
not a proof of its remaining branches.
Source: Aschbacher--Smith,15.2.24, printed pp.1117--1118, refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
open ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding

/-- The genuine characteristic-two model rows still requiring exclusion. -/
inductive RemainingEvenModel (L : Type*) [Group L] : Prop
  | bender (model : IsBenderModel L)
  | linear (f : ℕ) (hf : 2 ≤ f) (model : ClassicalGroup.IsPSL L 3 (2 ^ f))
  | symplectic (f : ℕ) (hf : 2 ≤ f) (model : ClassicalGroup.IsPSp L 2 (2 ^ f))
  | g2 (f : ℕ) (hf : 2 ≤ f) (model : IsG2At L (2 ^ f))
  | triality (f : ℕ) (hf : 1 ≤ f)
      (model : Triality.Standard.IsTrialityGroupAt (2 ^ f) L)
  | ree (m : ℕ) (hm : 1 ≤ m) (model : Chapter1.Section02.LocalModels.IsReeF4At L m)

/-- The remaining actual action rows after the proved part of15.2.24. -/
inductive RefinedModelAction115 (L : Type*) [Group L] (a : MulAut L) : Prop
  | lie (simple : IsSimpleGroup L) (model : RemainingEvenModel L)
      (inner : a ∈ (MulAut.conj (G := L)).range)
  | two_cover (nontrivial_center : center L ≠ ⊥) (center_eq : center L = pCore 2 L)
      (model : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 ∨ IsG2At (L ⧸ pCore 2 L) 4)
      (inner : a ∈ (MulAut.conj (G := L)).range)
  | janko_four (model : Nonempty ((L ⧸ pCore 2 L) ≃* Janko4.Model))
      (action : TwoCentralInner a)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Apply the binary and small-derived exclusions to the actual Lie model. -/
theorem remaining_even_model {P : Sylow 2 I} {z : G}
    (c : ComponentData (T := T) (Mc := Mc) I P z)
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : LieTypeTwoModel c.component)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) :
    RemainingEvenModel c.component := by
  rcases hm with hm | hm | ⟨n,hn,hm⟩
  · exact .bender hm
  · cases hm with
    | linear f hf hm =>
      by_cases h : f = 1
      · subst f
        exact (not_binary_linear_three_component d c hI hz hzne a ha
          (by simpa using hm) hi).elim
      · exact .linear f (by omega) hm
    | symplectic f hf hm => exact .symplectic f hf hm
    | g2 f hf hm => exact .g2 f hf hm
    | triality f hf hm => exact .triality f hf hm
    | ree m hm he => exact .ree m hm he
    | symplectic_derived hm =>
      exact (not_symplectic_derived_component d c hI hP hz hzne a ha hm hi).elim
    | g2_derived hm =>
      exact (not_g2_derived_component d c hI hP hz hzne a ha hm hi).elim
    | tits hm => exact (not_tits_component d c hI hP hz hzne a ha hm hi).elim
  · exact (not_binary_linear_component d c hI hP hz hzne a ha hn hm hi).elim

/-- The same marked component satisfies the sharpened remaining alternatives. -/
theorem component_refined_model_remainder {P : Sylow 2 I} {z : G}
    (c : ComponentData (T := T) (Mc := Mc) I P z)
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1) :
    ∃ a : MulAut c.component,
      (∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) ∧
      RefinedModelAction115 c.component a := by
  obtain ⟨a,ha,hm⟩ := component_model_remainder d c hI hP hz hzne
  refine ⟨a,ha,?_⟩
  cases hm with
  | lie hs hm hi =>
    exact .lie hs (remaining_even_model d c hI hP hz hzne a ha hm hi) hi
  | two_cover hn hc hm hi => exact .two_cover hn hc hm hi
  | janko_four hm hi => exact .janko_four hm hi

/-- Failure of original plane uniqueness produces a remaining actual model,
with all six completed binary/small-derived rows removed. -/
theorem exists_refined_component_of_nonunique
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
        RefinedModelAction115 c.component a := by
  obtain ⟨I,P,z,hI,hP,hz,hzne,⟨c⟩⟩ :=
    exists_component_data_of_nonunique d hquotient horbit ha hi hne
  obtain ⟨a,ha,hm⟩ := component_refined_model_remainder d c hI.1 hP hz hzne
  exact ⟨I,P,z,hI,hP,hz,hzne,c,a,ha,hm⟩
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
