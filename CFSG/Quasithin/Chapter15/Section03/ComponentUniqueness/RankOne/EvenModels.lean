module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.Models
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.SourceReduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.SmallLinear
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BorelFields
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.LinearTwo
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.UnitaryBorel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection

/-!
# Characteristic-two component cases of 15.3.43

`not_model` excludes all incoming characteristic-two alternatives of
1.1.5(3)(a)--(c), after the separate Suzuki exclusion, from the explicit
`ReducedConfiguration` and compatible source involution.

For larger fields, the actual local quotient determines the maximal
S-invariant parabolic and then the linear or unitary Borel. Its normal
four-group forces degree two. The three concrete automorphism calculations
give the literal upstairs equality C_S(Y₊) = C_S(L), contradicting (c).
The linear-three calculation retains the nontrivial central two-covers;
the parabolic inspection excludes the G₂(4) covers.

For degree one, the binary inspection eliminates the actual S₈ middle
parabolic through its two-radical action, then identifies the surviving
quotient with S₆ and the original actor with A₄, contradicting (d).
It retains the genuine small derived groups, triality and Tits carriers,
and the compatible A₆ transposition action.

Every intermediate parabolic, Borel, field and recognition premise is
discharged here. The enclosing 15.3.43 proof still constructs the reduced
configuration and the incoming model alternative and excludes the other
characteristics and sporadic families.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
printed pp.1139--1140; 1.1.5(3)(a)--(c), pp.501--502; A.2.3--4, p.33.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The actual normal four-group forces degree two in every surviving Borel. -/
theorem larger_field_borel_degree_eq_two
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ} (hn : 1 < n)
    (hB : LargerFieldBorel S M L n) : n = 2 := by
  cases hB.model with
  | linearTwo _ hm => exact linear_borel_degree_eq_two c hm hB.intersection
  | linearThree _ hm => exact linear_three_borel_degree_eq_two c hn hm hB.intersection
  | unitaryThree hm =>
    exact (unitary_borel_degree_eq_two c (by omega) hm hB.intersection).1

/-- Uniform upstairs centralizer equality, obtained from the three model
calculations after the normal plane has restricted the field. -/
theorem larger_field_borel_centralizers
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ} (hn : 1 < n)
    (hB : LargerFieldBorel S M L n) :
    S ⊓ centralizer (Yplus : Set G) = S ⊓ centralizer (L : Set G) := by
  have hn2 := larger_field_borel_degree_eq_two c hn hB
  subst n
  cases hB.model with
  | linearTwo _ hm => exact linear_borel_centralizers c hm hB.intersection
  | linearThree he hm =>
    exact linear_three_borel_centralizers c (by decide) he hm hB.intersection
  | unitaryThree hm => exact unitary_borel_centralizers c (by decide) hm hB.intersection

/-- The larger-field characteristic-two alternatives, with the parabolic
recognition and Borel inspection fully discharged. -/
theorem not_larger_field (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (hz : SourceInvolution S M z) {n : ℕ} (hn : 1 < n)
    (hm : Model L z n) : False :=
  centralizers_ne c (larger_field_borel_centralizers c hn
    (ParabolicInspection.largerFieldBorel c hz hn hm))

/-- The complete characteristic-two model exclusion in 15.3.43. The only
inputs are the retained local configuration and genuine earlier source data. -/
theorem not_model (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (hz : SourceInvolution S M z) {n : ℕ} (hm : Model L z n) : False := by
  have hn := hm.positive
  by_cases hbinary : n = 1
  · subst n
    exact BinaryInspection.not_binary c hz hm
  · exact not_larger_field c hz (by omega) hm

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
