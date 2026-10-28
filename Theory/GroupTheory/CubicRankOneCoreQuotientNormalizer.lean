module

public import Theory.GroupTheory.CubicCoreQuotientNormalizer
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Elementary cubic actors on a rank-one core quotient

An elementary abelian three-group acting on a centerless group with
two-group outer automorphisms has elementary inner image. If the target
has three-rank at most one, this image has order at most three, even when
the target order is divisible by nine. Odd rank-one Sylow theory passes
the source rank bound through the literal two-core quotient.

Consequently a marked cubic subgroup inside a perfect subgroup K accounts
for the entire action image. The existing perfect core-kernel argument
then proves that the whole actor normalizes K. The actual prime-field
PSL₂ consumer is in Theory.SpecificGroups.PSL2.PrimeCartanNormalizer.

Source: Aschbacher–Smith, Proposition 9.3.1, printed p.732.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup.CubicCoreQuotientNormalizer

/-- An elementary cubic action has at most three inner automorphisms when
the centerless target has three-rank at most one and two-group outer group. -/
theorem elementary_action_image_card_le_three
    {E X : Type*} [Group E] [Group X] [Finite E] [Finite X]
    [IsElementaryAbelian 3 E]
    (a : E →* MulAut X) (hz : center X = ⊥)
    (hout : IsPGroup 2 (MulAut.Outer X)) (hr : primeRank 3 X ≤ 1) :
    Nat.card a.range ≤ 3 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup X)
  have h3 : IsPGroup 3 (a.range.map q) :=
    ((IsElementaryAbelian.isPGroup 3 E).of_surjective
      a.rangeRestrict a.rangeRestrict_surjective).map q
  have h2 : IsPGroup 2 (a.range.map q) := hout.to_subgroup _
  have hb : a.range.map q = ⊥ :=
    disjoint_self.mp (h3.disjoint_of_coprime h2 (by decide))
  have hi : a.range ≤ MulAut.innerSubgroup X := by
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff a.range).mp hb
  let ec : X ≃* MulAut.innerSubgroup X :=
    MonoidHom.ofInjective (conj_injective_of_center_eq_bot hz)
  have hrange : primeRank 3 a.range ≤ 1 := by
    let f := ec.symm.toMonoidHom.comp (inclusion hi)
    exact (primeRank_le_of_injective 3 f
      (ec.symm.injective.comp (inclusion_injective hi))).trans hr
  let : IsElementaryAbelian 3 a.range :=
    IsElementaryAbelian.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 3)]
  exact Nat.pow_le_pow_right (by decide) hrange

/-- The source rank bound is on J itself. Cyclic Sylow three-subgroups
pass it to J/O₂(J), where the marked conjugation action is evaluated. -/
theorem normalizes_of_rank_one
    {G : Type*} [Group G] [Finite G]
    (K J A B : Subgroup G) [Group.IsPerfect K] [IsElementaryAbelian 3 A]
    (hKJ : K ≤ J) (hAJ : A ≤ normalizer (J : Set G))
    (hBA : B ≤ A) (hBK : B ≤ K)
    (hQK : J.pCoreIn 2 ≤ normalizer (K : Set G)) (hB : Nat.card B = 3)
    (hz : center (J ⧸ pCore 2 J) = ⊥)
    (hout : IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J)))
    (hr : primeRank 3 J ≤ 1) : A ≤ normalizer (K : Set G) := by
  apply normalizes_of_small_image K J A B hKJ hAJ hBA hBK hQK hB hz
  apply elementary_action_image_card_le_three _ hz hout
  let P : Sylow 3 J := Classical.choice inferInstance
  exact P.primeRank_quotient_le_one
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) (pCore 2 J)

end Subgroup.CubicCoreQuotientNormalizer
