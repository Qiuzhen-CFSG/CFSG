module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.BinaryLinear
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.BinaryThree
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.SmallDerived
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.G2
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Symplectic
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Triality
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Ree
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Bender
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.TerminalRank
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Remainder
import all CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Remainder

/-!
# Direct ordinary even-model reduction in the chosen source configuration

The genuine 1.1.5 marking of the selected component supplies the model cases.
The even-model exclusions use only the actual residual input, minimal escape,
Sylow marking and central seed. The small odd PSL₂ aliases are transported to
their characteristic-two models; all surviving cases retain their marked
ordinary action. No partner residual identity or model-exclusion callback is used.

The private Remainder import reuses only its intrinsic small-parameter
PSL₂ comparison, keeping that existing internal mathematical API unchanged.
Source: Aschbacher--Smith 15.2.24, printed pp.1117--1118, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Candidates.ComponentStructure ClassificationModels OrdinaryComponents
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}
variable (r : ResidualInput h H B)
include r
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)

private theorem not_lie_type_two_component_direct
    (hc : Nat.card (centralInvolutions T) = 2)
    (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hs : IsSimpleGroup c.component)
    (hm : LieTypeTwoModel c.component)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  rcases hm with hm | hm | ⟨n,hn,hm⟩
  · exact EqualityRowEvenModels.not_bender_component r hc c hI hP hz hzne a ha hs hm hi
  · cases hm with
    | linear f hf hm =>
      by_cases h : f = 1
      · subst f
        exact EqualityRowEvenModels.not_binary_linear_three_component r hc c hI.1 hz hzne a ha
          (by simpa using hm) hi
      · exact EqualityRowEvenModels.not_even_linear_three_component r hc c hI hP hz hzne a ha hs
          (by omega) hm hi
    | symplectic f hf hm =>
      exact EqualityRowEvenModels.not_symplectic_component r hc c hI.1 hP hz hzne a ha hs hf hm hi
    | g2 f hf hm =>
      exact EqualityRowEvenModels.not_g2_component r hc c hI.1 hP hz hzne a ha hs hf hm hi
    | triality f hf hm =>
      exact EqualityRowEvenModels.not_triality_component r hc c hI.1 hP hz hzne a ha hs hf hm hi
    | ree m hm he =>
      exact EqualityRowEvenModels.not_ree_component r c hI.1 hP hs hm he
    | symplectic_derived hm =>
      exact EqualityRowEvenModels.not_symplectic_derived_component r hc c hI.1 hP hz hzne a ha hm hi
    | g2_derived hm =>
      exact EqualityRowEvenModels.not_g2_derived_component r hc c hI.1 hP hz hzne a ha hm hi
    | tits hm =>
      exact EqualityRowEvenModels.not_tits_component r hc c hI.1 hP hz hzne a ha hm hi
  · exact EqualityRowEvenModels.not_binary_linear_component r hc c hI.1 hP hz hzne a ha hn hm hi

/-- The original marked ordinary component satisfies the terminal source
model/action alternatives, with all even and central-two-cover rows excluded. -/
theorem ResidualInput.ordinary_terminal_model_direct
    (hc : Nat.card (centralInvolutions T) = 2)
    (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1) :
    HasTerminalModelAction115 c.component z := by
  obtain ⟨a,ha,hm⟩ := c.model
  refine ⟨a,ha,?_⟩
  cases hm with
  | lie hs hm hi =>
    exact (not_lie_type_two_component_direct r c hc hI hP hz hzne a ha hs hm hi).elim
  | two_cover _ _ hm hi =>
    rcases hm with hm | hm
    · exact (EqualityRowEvenModels.not_linear_three_quotient_component r hc c hI hP hz hzne a ha
        (n := 2) (by decide) hm hi).elim
    · exact (EqualityRowEvenModels.not_g2_four_cover_component r hc c hI.1 hP hz hzne a ha hm hi).elim
  | six s hs hm =>
    exact (r.ordinary_six_false c hc hI.1 hz hzne a ha s hs hm).elim
  | seven s hs hm => exact .seven s hs hm
  | odd hm hi =>
    rcases hm with hm | ⟨p,hp,hm⟩
    · exact .linear_three hm hi
    · by_cases hs : p ≤ 7
      · let : IsQuasisimple c.component := c.isComponent.2
        obtain ⟨hsm,hlie⟩ := small_linear_two_is_lie hp hs hm
        exact (not_lie_type_two_component_direct r c hc hI hP hz hzne a ha hsm hlie hi).elim
      · exact .linear_two p hp (by omega) hm hi
  | sporadic name hn hm hi => exact .sporadic name hn hm hi

/-- The original global wreath condition supplies the central seed cardinality
needed by the direct even-model reduction. -/
theorem ResidualInput.ordinary_terminal_model
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* Wreath))
    (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1) :
    HasTerminalModelAction115 c.component z := by
  obtain ⟨_,_,hc,_⟩ := source_chosen_index_two_equality_row h r hquotient
  exact r.ordinary_terminal_model_direct c hc hI hP hz hzne

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
