module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.FullRank
public import Theory.SpecificGroups.PSL3Three.RankLower
public import Theory.SpecificGroups.PSL3Three.InnerInvolutionCentralizer
public import Theory.SpecificGroups.PSL3Three.OuterTwo
public import Theory.GroupTheory.PrimeRankOrderBound
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The odd degree-three component in original plane uniqueness

An inner involution of the actual PSL₃(3) model has fixed subgroup GL₂(3),
of order48. Its three-rank is at most one, contradicting the lower bound
obtained by placing the original K inside the same component and fixed group.
The conjugating automorphism retains the original z and its order is proved
from the faithful source action.

Source: Aschbacher--Smith, proof of15.2.15, printed p.1118,
refs/quasithin.pdf; the intrinsic centralizer is the inner case of16.1.5(1).
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

open scoped MatrixGroups

/-- The actual PSL₃(3) row contradicts the three-rank of its marked fixed subgroup. -/
theorem not_linear_three_component (hI : PlaneEscapes Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : ClassicalGroup.IsPSL c.component 3 3)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let eq := e.trans (Atlas.fieldEquivPSL 3 ef)
  have hc : center c.component = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr (eq.trans Matrix.PSL3Three.equiv.symm) ⟨x,hx⟩).property
    change Matrix.PSL3Three.equiv.symm (eq x) ∈ center Matrix.PSL3Three.SL at hh
    have h1 := Matrix.PSL3Three.center_eq_bot.le hh
    exact (eq.trans Matrix.PSL3Three.equiv.symm).map_eq_one_iff.mp (mem_bot.mp h1)
  have hr : 2 ≤ primeRank 3 c.component := by
    rw [primeRank_congr 3 eq]
    exact Matrix.PSL3Three.primeRank_three_ge_two
  have ho := Matrix.PSL3Three.outer_isTwoGroup.of_equiv (MulAut.outerCongr eq).symm
  have hlow := fixed_three_rank_of_full_component d c hI hz hzne hc hr ho a ha
  let b := MulAut.congr eq a
  have hb : orderOf b = 2 := (MulAut.congr eq).orderOf_eq a |>.trans
    (marked_component_action_order_two c (marked_centralizer d hI hz hzne).1 hz hzne a ha)
  have hbi : ∃ x, b = MulAut.conj x := by
    apply (MulAut.congr_inner_iff eq a).mpr
    obtain ⟨x,hx⟩ := hi
    exact ⟨x,hx.symm⟩
  let efix := (MulAut.fixedSubgroupCongr eq a).trans
    (Matrix.PSL3Three.innerInvolutoryAutFixedEquiv b hb hbi)
  have hcard : Nat.card a.fixedSubgroup = 48 := by
    rw [Nat.card_congr efix.toEquiv, Matrix.card_GL_field]
    decide
  have hu : primeRank 3 a.fixedSubgroup ≤ 1 :=
    primeRank_le_of_prime_pow_not_dvd (by rw [hcard]; decide)
  omega
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
