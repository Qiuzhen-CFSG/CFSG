module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.LinearTwo
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.TerminalRank
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.QuotientRank
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels.SporadicBounds

/-!
# Terminal ordinary components on the actual residual input

The odd linear and alternating rows are excluded directly. All non-Janko-four
sporadic rows contradict the rank-two marked involution centralizer. Janko-four
has a fixed residual with quotient 3.M22, excluded by solvable cubic closure in
the equality row. The final source consumer derives that row and the seed order
from the original wreath hypotheses.

This closes the terminal ordinary family without a partner residual identity.
The earlier characteristic-two exclusion and even-model reduction still have
their original source owners. No plane-uniqueness packet is assumed.

Source: Aschbacher--Smith, proof of 15.2.15, pp.1117--1118.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
open OrdinaryComponents
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}
variable (r : ResidualInput h H B)
include r
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)

/-- The actual sporadic quotient is J₄, without using the partner residual identity. -/
theorem ResidualInput.ordinary_sporadic_quotient_eq_j4
    (hcard : Nat.card (centralInvolutions T) = 2)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (name : SporadicName) (hne : name ≠ .j3)
    (e : (c.component ⧸ pCore 2 c.component) ≃* name.Carrier)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hai : TwoCentralInner a) : name = .j4 := by
  by_contra hj
  let : IsQuasisimple c.component := c.isComponent.2
  let : IsSimpleGroup (c.component ⧸ center c.component) := IsQuasisimple.simple
  let eZ := (QuotientGroup.quotientMulEquivOfEq c.center_eq).trans e
  let : IsSimpleGroup name.Carrier := eZ.symm.isSimpleGroup
  let : Finite name.Carrier := Finite.of_injective e.symm e.symm.injective
  obtain ⟨t,ht,htc,hr⟩ := r.quotient_centralizer_three_rank_direct c hcard hI hz hzne e
    (Candidates.SignedReduction.RankOneModels.sporadic_rank name hne)
    (SporadicBounds.outer_two name hne hj) a ha hai
  have hu : primeRank 3 (centralizer ({t} : Set name.Carrier)) ≤ 1 :=
    primeRank_le_of_prime_pow_not_dvd
      (SporadicBounds.centralizer_not_nine name hne hj t ht htc)
  omega

/-- Every terminal ordinary-component row is excluded on the actual input.
The literal Sylow and marked model are the outputs of the independent source
selection and even-model reduction. -/
theorem ResidualInput.ordinary_terminal_false
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* Wreath))
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (ht : HasTerminalModelAction115 c.component z) : False := by
  obtain ⟨he,_,hc,_⟩ := source_chosen_index_two_equality_row h r hquotient
  obtain ⟨a,ha,hm⟩ := ht
  cases hm with
  | seven σ hσ hm =>
    exact r.ordinary_seven_false c hc hI hz hzne a ha σ hσ hm
  | linear_three hm hi =>
    exact r.ordinary_linear_three_false c hc hI hz hzne a ha hm hi
  | linear_two p hp hl hm _ =>
    exact r.ordinary_linear_two_false c hc hI hP hz hzne hp hl hm
  | sporadic name hn hm hi =>
    obtain ⟨e⟩ := hm
    have hj := r.ordinary_sporadic_quotient_eq_j4 c hc hI hz hzne name hn e a ha hi
    subst name
    exact r.janko_four_fixed_residual_false_of_eq he hc c hz hzne a ha e hi

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
