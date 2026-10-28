module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallCatalogue
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallJanko
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.OddSubgroups

/-!
# The original doubled alternating-six source is an FF-module

The actual odd-normalizer catalogue leaves J4, and the original whole-orbit
large-center argument excludes that component. Thus every abelian odd actor
centralizing the orbit has its normalizer in N(L); characteristic abelian
subgroups give the arbitrary odd-actor conclusion. The original non-FF Hall
source produces precisely an escaping such actor, yielding the contradiction.
No uniqueness, module classification, placement or local callback remains.
Source: Aschbacher--Smith 4.4.3, 4.4.10--11 and 12.2.7, printed pp.621--623
and 797, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every abelian odd actor centralizing the original doubled A6 orbit has
its full normalizer in the original component normalizer. -/
theorem sourceOrbit_six_abelian_oddNormalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A)) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨K,hK,_,_,hcore,_,hr,_,hj⟩ :=
    D.sourceOrbit_six_oddNormalizer_janko_component h hd hmodel A hne hAC ho hout
  exact D.sourceOrbit_six_oddNormalizer_not_janko h hd hmodel A hAC ho K hK hcore hr hj

/-- The same original orbit satisfies odd-normalizer control for every
nontrivial odd subgroup of its relative centralizer. -/
theorem sourceOrbit_six_oddNormalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) : normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  apply odd_normalizer_control_of_abelian ?_ A hne hA ho
  intro B hB hBC hodd hcomm
  let := hcomm
  exact D.sourceOrbit_six_abelian_oddNormalizer_le h hd hmodel B hB
    (hBC.trans inf_le_right) hodd

/-- Under the original chosen-module and maximal-overgroup hypotheses,
the marked doubled A6 source orbit is an FF-module. -/
theorem sourceOrbit_six_ff
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) : IsFFModule D.sourceOrbitNormalizerRepresentation := by
  by_contra hnon
  obtain ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,_⟩ :=
    D.sourceOrbit_six_hall_outside_component h hd hmany hnon hmodel
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  exact hout (D.sourceOrbit_six_abelian_oddNormalizer_le h hd hmodel A hne hAC hodd)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
