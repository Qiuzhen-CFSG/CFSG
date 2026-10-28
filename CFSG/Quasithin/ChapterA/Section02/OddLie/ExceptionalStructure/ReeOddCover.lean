module

public import Theory.SpecificGroups.ReeG2.OddCentralCover
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import CFSG.Quasithin.Defs

/-!
# The large Ree exclusion on the original A.2 central cover

The original finite perfect central cover has an odd kernel. Its marked
Ree torus involution lifts to an involution whose actual centralizer
contains a faithful PSL₂(F), by the proved PSL₂ universal-cover theorem.
That centralizer has three-rank at least 2m+1, contradicting quasithinness
for m≥1. The central-quotient application uses the given map
G → G/Z(G) → Ree(F,m), including its original model identification.

No Ree multiplier or quasithinness of an arbitrary quotient is assumed.
The separate small derived group at m=0 is outside this statement.
Source: Aschbacher–Smith A.2.13 and A.2.17, printed pp.37–39.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering

namespace CFSG.Quasithin.ChapterA.Section02.ReeOddCover

variable {F G : Type*} [Field F] [Finite F] [CharP F 3] [Group G] [Finite G]

/-- A.2.17's large Ree branch for the original finite perfect central
cover, using its odd kernel and no Ree multiplier premise. -/
theorem not_quasithin_of_central_cover
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card F = 3 ^ (2 * m + 1))
    (f : PerfectCentralCovering.Cover G (Atlas.ReeG2.Model F m))
    (ho : Odd (Nat.card f.toMonoidHom.ker)) : ¬ IsQuasithin G := by
  intro hqt
  obtain ⟨t, ht, ht2, _htf, hr⟩ :=
    Atlas.ReeG2.OddCentralCover.exists_marked_involution_primeRank_ge
      m hm hcard f.toMonoidHom f.surjective f.ker_le_center ho
  have hloc := Theory.GroupTheory.isTwoLocal_involution_centralizer
    (orderOf_eq_prime ht2 ht)
  have hu := (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt) _ hloc 3
    (by decide) (by decide)
  omega

/-- The literal A.2 source application: the center has odd order and
the given quotient identification is used unchanged in the covering map. -/
theorem not_quasithin_of_centralQuotientEquiv [Group.IsPerfect G]
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card F = 3 ^ (2 * m + 1))
    (j : G ⧸ center G ≃* Atlas.ReeG2.Model F m)
    (ho : Odd (Nat.card (center G))) : ¬ IsQuasithin G := by
  apply not_quasithin_of_central_cover m hm hcard (centralQuotientCover j)
  simpa only [centralQuotientCover_ker] using ho

end CFSG.Quasithin.ChapterA.Section02.ReeOddCover
