module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels.SporadicBounds
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.QuotientRank

/-!
# The remaining sporadic component in original plane uniqueness

Apply the original residual containment and the central two-kernel rank
comparison to the actual marked sporadic quotient. Its involution centralizer
has three-rank at least two, contradicting the nine native model bounds.
Only J₄ remains. The consumer combines this with the earlier proved linear
and alternating exclusions on the same component and automorphism.

This does not construct 15.2.24 or the final J₄ residual-section contradiction.
Source: Aschbacher--Smith, proof of 15.2.15, printed p.1118,
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

/-- The actual marked sporadic quotient in 15.2.15 must be J₄. All nine other
rows are eliminated, including nontrivial central two-covers. -/
theorem sporadic_quotient_eq_j4 (hI : PlaneEscapes Mc ZS I)
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
  obtain ⟨t,ht,htc,hr⟩ := quotient_centralizer_three_rank d c hI hz hzne e
    (Candidates.SignedReduction.RankOneModels.sporadic_rank name hne)
    (SporadicBounds.outer_two name hne hj) a ha hai
  have hu : primeRank 3 (centralizer ({t} : Set name.Carrier)) ≤ 1 :=
    primeRank_le_of_prime_pow_not_dvd
      (SporadicBounds.centralizer_not_nine name hne hj t ht htc)
  omega

/-- After the original 15.2.24 reduction, the sole surviving actual quotient
is J₄ with the same two-central marked action. The J₄ residual-section
contradiction and construction of 15.2.24 remain separate proof obligations. -/
theorem janko_four_of_terminal_model (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (ht : HasTerminalModelAction115 c.component z) :
    ∃ a : MulAut c.component,
      Nonempty ((c.component ⧸ pCore 2 c.component) ≃* Janko4.Model) ∧
      (∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) ∧
      TwoCentralInner a := by
  obtain ⟨name,a,hn,⟨e⟩,ha,hai⟩ := sporadic_of_terminal_model d c hI hP hz hzne ht
  have hn4 := sporadic_quotient_eq_j4 d c hI hz hzne name hn e a ha hai
  subst name
  exact ⟨a,⟨e⟩,ha,hai⟩
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
