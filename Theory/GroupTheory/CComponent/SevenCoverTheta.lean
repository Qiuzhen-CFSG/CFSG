module
public import Theory.GroupTheory.CComponent.TripleSevenTheta
public import Theory.GroupTheory.CComponent.ThreeCore
public import Theory.Alternating.OddCentralCovers
public import Theory.Alternating.PrimeRank
public import Theory.Alternating.Aut
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# Cubic elements around an A₇ central quotient

A normal C-component with central quotient A₇ in a group of three-rank
at most two contains every element of order three. For the centerless
quotient, the outer two-group calculation identifies its prime-to-three
residual. For the triple cover, the intrinsic cubic-actor theorem applies.
The odd-center alternatives preserve both covers of the original quotient.

Source: Aschbacher--Smith A.3.18 and 12.2.8, printed pp.51--53 and 797;
used in the proper-overcomponent branch of 12.3.12, printed p.811.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.SevenCComponentTheta
variable {H : Type*} [Group H] [Finite H]

private theorem seven_outer_two : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 7))) := by
  let A := alternatingGroup (Fin 7)
  have hcard : Nat.card (Equiv.Perm (Fin 7) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

/-- The centerless row, in the actual ambient group of three-rank at most two. -/
theorem order_three_mem_of_quotient_seven (L : Subgroup H) [L.Normal]
    (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (hr : primeRank 3 H ≤ 2) {x : H} (hx : orderOf x = 3) : x ∈ L := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    have he : e a ∈ center (alternatingGroup (Fin 7)) := (centerCongr e ⟨a, ha⟩).property
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hrL : 2 ≤ primeRank 3 (L ⧸ pCore 2 L) := by
    rw [primeRank_congr 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 3 Nat.prime_three (by decide)]
  have ho : IsPGroup 2 (MulAut.Outer (L ⧸ pCore 2 L)) :=
    seven_outer_two.of_injective (MulAut.outerCongr e).toMonoidHom
      (MulAut.outerCongr e).injective
  rw [hL.eq_primeToResidual_three_of_outer_twoGroup hz hrL hr ho]
  apply mem_primeToResidual_of_pow (n := 1)
  simpa only [pow_one, hx] using pow_orderOf_eq_one x

/-- The central quotient suffices; the original triple cover is retained. -/
theorem order_three_mem_of_central_quotient_seven (L : Subgroup H) [L.Normal]
    (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 7))
    (hr : primeRank 3 H ≤ 2) {x : H} (hx : orderOf x = 3) : x ∈ L := by
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot (G := L) 2) _ le_rfl
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 7 (by decide) e ho with
    hc | ⟨_, hc⟩
  · exact order_three_mem_of_quotient_seven L hL
      (GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 7 e hc) hr hx
  · obtain ⟨eL⟩ := GLS3.Chapter5.OddCentralCovers.triple_seven_equiv e hc
    exact TripleSevenTheta.order_three_mem L hL eL hr hx
      (le_normalizer_of_normal (mem_top x))

end Theory.GroupTheory.SevenCComponentTheta
