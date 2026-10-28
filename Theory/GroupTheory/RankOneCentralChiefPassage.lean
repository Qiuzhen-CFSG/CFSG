module
public import Theory.GroupTheory.SylowCharacteristicKernelLifting
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralChiefKernelQuotient

/-!
# Structure through a central-chief kernel

A normal kernel in the two-core leaves the quotient by the two-core unchanged.
If all its ambient chief factors are central, the no-characteristic-normal
hypothesis lifts exact Sylow class and exponent, while equivariant
Jordan–Hölder preserves the noncentral chief-factor count. Equal quotient
orders then identify any surjection kernel containing the two-core.

The actual consumer is the final passage in Niles, *Pushing-up in finite
groups* (1979), Theorem B, printed p.62.
-/

public section
open Subgroup NoncentralChiefRefinement
namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

/-- The original two-core quotient is unchanged by a normal two-core kernel. -/
noncomputable def pCoreQuotientEquivOfKernel
    (N : Subgroup H) [N.Normal] (hN : N ≤ pCore 2 H) :
    ((H ⧸ N) ⧸ pCore 2 (H ⧸ N)) ≃* (H ⧸ pCore 2 H) := by
  let π := QuotientGroup.mk' N
  have hp : IsPGroup 2 π.ker := by
    exact ((pCore_isPGroup (p := 2) (G := H)).to_le hN).of_equiv
      (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' N).symm)
  have he : (pCore 2 H).map π = pCore 2 (H ⧸ N) := by
    rw [← π.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective N) hp,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)]
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient N (pCore 2 H) hN)

/-- All structural conclusions pass back through the literal central-chief
kernel. The natural-module identification is supplied independently by the
original omega quotient, once this count is one. -/
theorem structure_of_central_chief_quotient
    {X : Type*} [Group X]
    (S : Sylow 2 H) (hno : NoCharacteristicNormal (S : Subgroup H))
    (N : Subgroup H) [N.Normal] (hN : N ≤ pCore 2 H)
    (s : SeriesOn N) (hc : ∀ i, s.Central i)
    (hclass : Group.nilpotencyClass ((S : Subgroup H).map (QuotientGroup.mk' N)) = 2)
    (hexp : Monoid.exponent ((S : Subgroup H).map (QuotientGroup.mk' N)) = 4)
    (he : Nonempty (((H ⧸ N) ⧸ pCore 2 (H ⧸ N)) ≃* X))
    (ht : ∃ t : SeriesOn (pCore 2 (H ⧸ N)), t.noncentralCount = 1) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* X) ∧
      ∀ t : SeriesOn (pCore 2 H), t.noncentralCount = 1 := by
  obtain ⟨hcl,hex⟩ := class_two_exponent_four_of_central_quotient
    S hno N (pCore_isPGroup.to_le hN) s hc hclass hexp
  obtain ⟨e⟩ := he
  refine ⟨hcl,hex,⟨(pCoreQuotientEquivOfKernel N hN).symm.trans e⟩,?_⟩
  obtain ⟨t,ht⟩ := ht
  intro u
  exact (core_noncentralCount_eq_of_central_chief_kernel N hN s hc u t).trans ht

/-- A surjection of the prescribed quotient order has exactly the two-core
kernel once that core is already known to act trivially. -/
theorem ker_eq_pCore_of_quotient_equiv
    {X : Type*} [Group X] [Finite X] (q : H →* X)
    (hq : Function.Surjective q) (hQ : pCore 2 H ≤ q.ker)
    (e : (H ⧸ pCore 2 H) ≃* X) : q.ker = pCore 2 H := by
  by_contra hn
  have hi := index_strictAnti (lt_of_le_of_ne hQ (Ne.symm hn))
  have hc : (pCore 2 H).index = q.ker.index := by
    rw [index_eq_card, index_eq_card]
    exact (Nat.card_congr e.toEquiv).trans
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv).symm
  rw [hc] at hi
  exact (lt_irrefl _ hi)

end Theory.GroupTheory
