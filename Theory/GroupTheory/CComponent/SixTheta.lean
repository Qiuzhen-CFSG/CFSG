module

public import Theory.GroupTheory.CComponent.HexacodeTheta
public import Theory.GroupTheory.PResidual.QuasisimpleCubicGeneration
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.PrimeRankAutomorphismOrder

/-!
# Cubic generation in an A₆ or 3.A₆ C-component normalizer

In three-rank at most two, a normal C-component with two-core quotient A₆
contains every cubic element by its centerless outer-two action. For 3.A₆,
the intrinsic hexacode component calculation gives the same containment.
Perfectness and the small quotient center give the reverse cubic generation.
The ambient group here is the actual local normalizer, not the simple QTKE group.

Source: Aschbacher--Smith, A.3.17--18 and 12.2.8, printed pp.51--52, 797.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.SixCComponentTheta
variable {H : Type*} [Group H] [Finite H]

private theorem internal_cubic_generation (L : Subgroup H) (hL : L.IsCComponent)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hr : 2 ≤ primeRank 3 (L ⧸ pCore 2 L))
    (hz : primeRank 3 (center (L ⧸ pCore 2 L)) ≤ 1) :
    L ≤ closure {x : H | orderOf x=3} := by
  let : Group.IsPerfect L := hL.perfect
  have hrL : 2 ≤ primeRank 3 L := hr.trans
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
  have he := cubic_closure_eq_top_of_twoCore_quasisimple hrL hz
  have he' := congrArg (map L.subtype) he
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,range_subtype] at he'
  rw [←he']
  apply Subgroup.closure_mono
  rintro x ⟨y,hy,rfl⟩
  exact (L.orderOf_coe y).trans hy

theorem cubic_closure_eq_of_alternating_six (L : Subgroup H) [L.Normal]
    (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hrH : primeRank 3 H ≤ 2) : closure {x : H | orderOf x=3}=L := by
  have hr : 2 ≤ primeRank 3 (L ⧸ pCore 2 L) := by
    rw [primeRank_congr 3 e,GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 Nat.prime_three (by decide)]
  have hz : center (L ⧸ pCore 2 L)=⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    apply mem_bot.mpr
    have he : e x ∈ center (alternatingGroup (Fin 6)) := (centerCongr e ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have ho : IsPGroup 2 (MulAut.Outer (L ⧸ pCore 2 L)) :=
    (IsPGroup.of_card (n:=2) AlternatingSix.ShadowLocal.outer_card).of_injective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective
  have hres := hL.eq_primeToResidual_three_of_outer_twoGroup hz hr hrH ho
  apply le_antisymm
  · apply (closure_le L).mpr
    intro x hx
    rw [hres]
    apply mem_primeToResidual_of_pow (n:=1)
    change orderOf x = 3 at hx
    simpa only [pow_one, hx] using pow_orderOf_eq_one x
  · apply internal_cubic_generation L hL hr
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply primeRank_le_of_card_le_prime_pow (n:=1)
    rw [hz, Subgroup.card_bot]
    decide

theorem cubic_closure_eq_of_triple_six (L : Subgroup H) [L.Normal]
    (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hrH : primeRank 3 H ≤ 2) : closure {x : H | orderOf x=3}=L := by
  have hr : 2 ≤ primeRank 3 (L ⧸ pCore 2 L) := by
    rw [primeRank_congr 3 e]
    exact Representation.Hexacode.two_le_primeRank_even
  apply le_antisymm
  · apply (closure_le L).mpr
    intro x hx
    exact HexacodeTheta.order_three_mem L hL e hrH hx (le_normalizer_of_normal (mem_top x))
  · apply internal_cubic_generation L hL hr
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply primeRank_le_of_card_le_prime_pow (n:=1)
    rw [Nat.card_congr (centerCongr e).toEquiv,Representation.Hexacode.even_center_card]
    decide
end Theory.GroupTheory.SixCComponentTheta
