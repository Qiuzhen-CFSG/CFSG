module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Bounds
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# Invariant intersections for elementary split SL₃ and PSL₃ pairs

In the actual SL₃ model over a field of order 1 modulo three, the center has
order three. Every elementary subgroup R of order nine contains that center:
an independent central element of order three would generate an elementary
subgroup of order 27 with R, contradicting the supplied ambient three-rank.
Consequently the central intersection has order exactly three.

In the actual PSL₃ model, the proved upper bound and nontriviality give
an intersection of order three with the derived subgroup of C_Q(Z(S)):
the intersection is a three-group, so its nontrivial order is divisible by
three. The nontriviality calculation includes both involution-centralizer
and monomial positions, derived from RS = SR and the ambient Sylow hypothesis.
Splitting the actual `LinearThreeModel` equivalence therefore proves the
full intersection alternative without an additional position premise.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528). The scalar-center order comes
from the existing attributed ATLAS port via `SL3.CenterProjectiveComparison`.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split

variable {Q : Type*} [Group Q] [Finite Q]

private theorem center_le_elementary_nine
    {R : Subgroup Q} (he : IsElementaryAbelian 3 R) (hc : Nat.card R = 9)
    (hr : primeRank 3 Q = 2) (hz : Nat.card (center Q) = 3) : center Q ≤ R := by
  let _ := he
  intro x hx
  by_contra hxR
  let z : center Q := ⟨x, hx⟩
  have hd : orderOf z ∣ 3 := hz ▸ orderOf_dvd_natCard z
  have ho : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · have h1' : z = 1 := orderOf_eq_one_iff.mp h1
      have hx1 : x = 1 := congrArg Subtype.val h1'
      exact (hxR (hx1.symm ▸ R.one_mem)).elim
    · exact h3
  have hox : orderOf x = 3 :=
    (orderOf_injective (center Q).subtype Subtype.val_injective z).trans ho
  have hfix : R ≤ centralizer ({x} : Set Q) := by
    intro a _
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hx a)
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join R x hox hxR hfix
    (show Nat.card R = 3 ^ 2 by simpa using hc)
  omega

/-- In every actual split SL₃ model, the elementary complement contains
the scalar center and its central intersection has order three. -/
theorem elementary_center_intersection_of_sl3
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (F : Type*) [Field F] [Finite F]
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hmod : Nat.card F % 3 = 1)
    (he : IsElementaryAbelian 3 R) (hc : Nat.card R = 9) :
    Nat.card ((center Q).subgroupOf R) = 3 := by
  have hZ : Nat.card (center Q) = 3 := by
    apply (Nat.card_congr (centerCongr e).toEquiv).trans
    apply Matrix.SL3.card_center_eq_three_of_ne_bot
    intro hz
    exact (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp hz hmod
  have hZR := center_le_elementary_nine he hc h.rank hZ
  exact (Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv).trans hZ

/-- An elementary complement of order nine in an actual split SL₃ or PSL₃
model has an order-three intersection with the center or with the derived
centralizer of the intrinsic Sylow center. -/
theorem elementary_intersections
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p) (hmod : p % 3 = 1)
    (hmodel : LinearThreeModel p Q) (he : IsElementaryAbelian 3 R)
    (hc : Nat.card R = 9) :
    Nat.card ((center Q).subgroupOf R) = 3 ∨
      Nat.card ((centralizerDerived (S : Subgroup Q)).subgroupOf R) = 3 := by
  rcases hmodel with ⟨F, _, _, hF, ⟨e⟩⟩ | hm
  · exact Or.inl (elementary_center_intersection_of_sl3 h F e
      (by simpa only [hF] using hmod) he hc)
  · right
    let A := (centralizerDerived (S : Subgroup Q)).subgroupOf R
    have hAp := h.oddComplement.isPGroup.to_subgroup A
    have hne := projective_elementary_intersection_ne_bot h hp ho hlarge hmod hm he hc
    have hd : 3 ∣ Nat.card A := hAp.card_eq_or_dvd.resolve_left
      (fun h1 => hne (Subgroup.card_eq_one.mp h1))
    exact le_antisymm
      (projective_elementary_intersection_le_three S R h p hp ho hlarge hmod hm he hc)
      (Nat.le_of_dvd Nat.card_pos hd)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split
