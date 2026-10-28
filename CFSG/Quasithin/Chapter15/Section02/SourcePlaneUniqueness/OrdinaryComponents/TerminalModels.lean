module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels.LinearTwo
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Alternating

/-!
# The surviving terminal ordinary component

The PSL₂(p), PSL₃(3), and marked A₇ cases are now excluded on the actual
source component. Given the15.2.24 terminal reduction, its remaining quotient
is a sporadic carrier and the same z induces the specified two-central inner
action. The remaining even-model reduction and sporadic exclusions are still
required; this is not the final plane uniqueness theorem.

Source: Aschbacher--Smith, proof of15.2.15, printed p.1118,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include d

/-- The proved terminal linear and alternating exclusions leave a literal
sporadic quotient with the same marked action. The15.2.24 input remains explicit. -/
theorem sporadic_of_terminal_model (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (ht : HasTerminalModelAction115 c.component z) :
    ∃ (name : SporadicName) (a : MulAut c.component), name ≠ .j3 ∧
      Nonempty ((c.component ⧸ pCore 2 c.component) ≃* name.Carrier) ∧
      (∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) ∧
      TwoCentralInner a := by
  obtain ⟨a,ha,ht⟩ := ht
  cases ht with
  | seven σ hσ hm => exact (not_seven_component d c hI hz hzne a ha σ hσ hm).elim
  | linear_three hm hi => exact (not_linear_three_component d c hI hz hzne a ha hm hi).elim
  | linear_two p hp hl hm _ => exact (not_linear_two_component d c hI hP hz hzne hp hl hm).elim
  | sporadic name hn hm hi => exact ⟨name,a,hn,hm,ha,hi⟩

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
