module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FourResiduals
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.GroupTheory.PResidual.OddImage

/-!
# Obstruction to the unrestricted four-residual count

The family `cubicResiduals X` includes every subgroup of order three. In
A₄ × A₄, four different three-cycle subgroups of the first factor and one
of the second give five distinct members. Nevertheless, the literal
quotient by the two-core is elementary abelian of order nine.

Thus the quotient identification in the moving-L₁ paragraph does not
justify the four-member assertion for the unrestricted family currently
used by `FourResidualGeometry`. Relative normality is absent from that
family. Counting the normal residuals of the four quotient-line preimages
is a possible repaired route; this module does not assert that repair.

This is an obstruction to the local counting inference, not a counterexample
to Hypothesis1223 or to the full source theorem under its ambient hypotheses.
The existing family, geometry and assembly interfaces are preserved.

Source under examination: Aschbacher–Smith, 12.4.6, final paragraph,
printed p.814 of the combined manuscript. The printed family also uses the
unrestricted wording “subgroups Y of X”.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

/-- Every subgroup of order three belongs to the literal cubic family:
it is two-perfect and has trivial two-core. -/
theorem cubicResiduals_mem_of_card_three {G : Type*} [Group G]
    (X Y : Subgroup G) (hle : Y ≤ X) (hc : Nat.card Y = 3) :
    Y ∈ cubicResiduals X := by
  have hp : IsPGroup 3 Y := IsPGroup.of_card (n := 1) hc
  have hperfect : IsPPerfect 2 Y := by
    apply (pResidual_eq_top_iff 2 Y).mp
    apply top_unique
    intro y _
    exact mem_pResidual_of_orderOf_coprime
      (hp.orderOf_coprime (by decide : Nat.Coprime 3 2) y).symm
  have hcore : pCore 2 Y = ⊥ := by
    have hd := pCore_isPGroup.disjoint_of_coprime (hp.to_subgroup ⊤)
      (by decide : Nat.Coprime 2 3)
    simpa only [disjoint_top] using hd
  refine ⟨hle, hperfect, ?_⟩
  rw [hcore]
  exact (Nat.card_congr (QuotientGroup.quotientBot : Y ⧸ (⊥ : Subgroup Y) ≃* Y).toEquiv).trans hc

namespace MovingResidualObstruction
private abbrev A := alternatingGroup (Fin 4)

/-- The actual product of two alternating groups of degree four. -/
abbrev Model := AlternatingFourPair.Model

private def cyclePerm (i : Fin 4) : Equiv.Perm (Fin 4) :=
  Equiv.swap (![0,0,0,1] i) (![1,1,2,2] i) *
    Equiv.swap (![1,1,2,2] i) (![2,3,3,3] i)

private theorem cyclePerm_even : ∀ i, cyclePerm i ∈ alternatingGroup (Fin 4) := by
  intro i
  rw [Equiv.Perm.mem_alternatingGroup]
  revert i
  decide +kernel

private def cycle (i : Fin 4) : A := ⟨cyclePerm i, cyclePerm_even i⟩

private def generator (i : Fin 5) : Model :=
  ![(cycle 0, 1), (cycle 1, 1), (cycle 2, 1), (cycle 3, 1), (1, cycle 0)] i

private theorem generator_order (i : Fin 5) : orderOf (generator i) = 3 := by
  apply orderOf_eq_prime
  · have h : ∀ i, generator i ^ 3 = 1 := by decide +kernel
    exact h i
  · have h : ∀ i, generator i ≠ 1 := by decide +kernel
    exact h i

private def C (i : Fin 5) : Subgroup Model := zpowers (generator i)

private theorem card_C (i : Fin 5) : Nat.card (C i) = 3 := by
  rw [C, Nat.card_zpowers, generator_order]

private theorem C_injective : Function.Injective C := by
  intro i j hij
  have hm : generator i ∈ C j := hij ▸ mem_zpowers (generator i)
  rw [C, mem_zpowers_iff_mem_range_orderOf, generator_order] at hm
  have h : ∀ i j : Fin 5,
      generator i ∈ (Finset.range 3).image (fun k => generator j ^ k) → i = j := by
    decide +kernel
  exact h i j hm

/-- Five explicit cyclic subgroups already exceed the proposed count. -/
theorem five_le_cubicResiduals : 5 ≤ (cubicResiduals (⊤ : Subgroup Model)).ncard := by
  have hs : Set.range C ⊆ cubicResiduals (⊤ : Subgroup Model) := by
    rintro Y ⟨i, rfl⟩
    exact cubicResiduals_mem_of_card_three _ _ le_top (card_C i)
  have hb := Set.ncard_le_ncard hs
  rwa [Set.ncard_range_of_injective C_injective, Nat.card_fin] at hb

/-- The unrestricted family is not the four-element quotient-line family. -/
theorem cubicResiduals_not_four : (cubicResiduals (⊤ : Subgroup Model)).ncard ≠ 4 := by
  have h := five_le_cubicResiduals
  omega

/-- The example has the same intrinsic two-core quotient order used in
 the source counting step. -/
theorem quotient_card_nine : Nat.card (Model ⧸ pCore 2 Model) = 9 := by
  have h := card_eq_card_quotient_mul_card_subgroup (pCore 2 Model)
  rw [AlternatingFourPair.card_twoCore, Nat.card_prod,
    alternatingGroup.card_of_card_eq_four (by simp)] at h
  omega

/-- The actual two-core quotient is elementary abelian, so the order-nine
 quotient is E₉ rather than cyclic of order nine. -/
theorem quotient_elementary : IsElementaryAbelian 3 (Model ⧸ pCore 2 Model) := by
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    have hcore : Nat.card (pCore 2 A) = 4 := by
      rw [AlternatingFourPair.twoCore_eq_kleinFour]
      exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
    have h := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
    rw [hcore,
      alternatingGroup.card_of_card_eq_four (by simp)] at h
    omega
  let : IsCyclic (A ⧸ pCore 2 A) := isCyclic_of_prime_card hc
  let : IsMulCommutative (A ⧸ pCore 2 A) := IsCyclic.isMulCommutative
  have hpow : ∀ x : A ⧸ pCore 2 A, x ^ 3 = 1 := by
    intro x
    simpa only [hc] using (pow_card_eq_one' (x := x))
  let e : (Model ⧸ pCore 2 Model) ≃* (A ⧸ pCore 2 A) × (A ⧸ pCore 2 A) :=
    (QuotientGroup.quotientMulEquivOfEq (pCore_prod 2)).trans
      (QuotientGroup.prodMulEquiv (pCore 2 A) (pCore 2 A))
  refine { toIsMulCommutative := ⟨⟨fun x y => e.injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply e.injective
  rw [map_pow, map_one]
  exact Prod.ext (hpow _) (hpow _)

end MovingResidualObstruction
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
