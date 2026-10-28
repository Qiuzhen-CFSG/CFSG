module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.BinaryDegree
public import Theory.Representation.BinaryOffender.CubicFixedSpaceSaturation

/-!
# Source reductions for the six small odd PSL₂ parameters

The binary degree bounds exclude parameters 13, 19 and 23 once the source's
degree-eight upper bound is proved. For parameters 11, 17 and 25, equality
in the actor bound instead forces a common fixed space. A product of actors
conjugate inside an involution centralizer can then give a contradiction.
The original group, central quotient, and binary representation are retained.

This module proves the reductions and their literal source applications.
The small-module and local-generation calculations remain outstanding; the
unconditional six-parameter exclusion is not asserted here. Final assembly
of those calculations belongs to this module, and full parameter assembly
belongs to LinearExclusion.

Source: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.1, manuscript pp.8--9.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- The degree calculation remaining for 13, 19 and 23 gives strict threshold two.
The degree-eight bound is an explicit outstanding source premise. -/
theorem source_exclusion_of_degree_eight {q : ℕ}
    (hq : q = 13 ∨ q = 19 ∨ q = 23)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 q)
    (hdegree : cubicRatio ρ ≤ 2 → Module.finrank (ZMod 2) V ≤ 8) :
    2 < cubicRatio ρ := by
  by_contra hn
  exact (not_le_of_gt
    (eight_lt_degree_of_thirteen_nineteen_twentyThree ρ h.faithful hq hm))
    (hdegree (le_of_not_gt hn))

/-- The literal prime-field actor has rank two and the involution's fixed space
as soon as its displacement reaches four. No containment of A in F* is assumed. -/
theorem source_prime_actor_saturation {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hp4 : 4 ≤ p) (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 p)
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) {t : G} (ht : t ∈ A)
    (htlarge : 4 ≤ fixedCodim ρ (zpowers t)) :
    rank A = 2 ∧ fixedCodim ρ A = 4 ∧
      fixedSpace ρ A = fixedSpace ρ (zpowers t) := by
  have hr : primeRank 2 G ≤ 2 := by
    simpa only [pow_one, ite_true] using
      source_two_rank_pslTwo ρ h hp ho (Or.inl rfl : 1 = 1 ∨ 1 = 2)
        (by simpa only [pow_one] using hp4) (by simpa only [pow_one] using hm)
  have hrA := rank_le_of_primeRank_le hA hr
  obtain ⟨hd, heq⟩ := fixedSpace_eq_of_saturated_actor ρ ht hrA hsmall htlarge
  exact ⟨by omega, hd, heq⟩

/-- The prime-field centralizer product calculation supplies the strict step.
The product and its displacement are still genuine local source obligations. -/
theorem source_prime_not_small_actor_of_product {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hp4 : 4 ≤ p) (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 p)
    {A : Subgroup G} (hA : IsElementaryTwo A) {t g a b : G}
    (ht : t ∈ A) (htlarge : 4 ≤ fixedCodim ρ (zpowers t))
    (hg : Commute g t) (ha : a ∈ A) (hb : b ∈ A)
    (hprod : 4 < fixedCodim ρ (zpowers (a * (g * b * g⁻¹)))) :
    ¬ fixedCodim ρ A ≤ 2 * rank A := by
  intro hsmall
  obtain ⟨hr, _, _⟩ := source_prime_actor_saturation ρ h hp ho hp4 hm hA hsmall ht htlarge
  exact not_small_actor_of_centralizer_product ρ hr.le ht htlarge hg ha hb hprod hsmall

/-- Parameter 25 retains the field outer actor: its possible rank is three. -/
theorem source_twentyFive_actor_saturation
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) {t : G} (ht : t ∈ A)
    (htlarge : 6 ≤ fixedCodim ρ (zpowers t)) :
    rank A = 3 ∧ fixedCodim ρ A = 6 ∧
      fixedSpace ρ A = fixedSpace ρ (zpowers t) := by
  have hr : primeRank 2 G ≤ 3 := by
    simpa only [show ¬ (2 : ℕ) = 1 by decide, ite_false] using
      source_two_rank_pslTwo ρ h (by decide : Nat.Prime 5) (by decide)
        (Or.inr rfl : 2 = 1 ∨ 2 = 2) (by decide) hm
  have hrA := rank_le_of_primeRank_le hA hr
  obtain ⟨hd, heq⟩ := fixedSpace_eq_of_saturated_actor ρ ht hrA hsmall htlarge
  exact ⟨by omega, hd, heq⟩

/-- The parameter-25 product calculation defeats the remaining equality six. -/
theorem source_twentyFive_not_small_actor_of_product
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    {A : Subgroup G} (hA : IsElementaryTwo A) {t g a b : G}
    (ht : t ∈ A) (htlarge : 6 ≤ fixedCodim ρ (zpowers t))
    (hg : Commute g t) (ha : a ∈ A) (hb : b ∈ A)
    (hprod : 6 < fixedCodim ρ (zpowers (a * (g * b * g⁻¹)))) :
    ¬ fixedCodim ρ A ≤ 2 * rank A := by
  intro hsmall
  obtain ⟨hr, _, _⟩ := source_twentyFive_actor_saturation ρ h hm hA hsmall ht htlarge
  exact not_small_actor_of_centralizer_product ρ hr.le ht htlarge hg ha hb hprod hsmall

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall
