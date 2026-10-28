module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Geometry
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients.Action
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The intrinsic two-core quotients of the M₂₂ pair stabilizers

The actions on the five hexads through {1,2} are surjective onto S₅. The inner
stabilizer has order 1920. The even intersection of the outer stabilizer is
isomorphic to the inner stabilizer and has index two, so the outer order is 3840. Counting
kernels gives orders 16 and 32. Since S₅ has no nontrivial normal two-subgroup,
these kernels are exactly the intrinsic two-cores. The first isomorphism
theorem then gives both actual multiplicative equivalences.

The outer order calculation uses the existing equivalence between the inner
intersection and the M₂₂ stabilizer. No split extension or order-only group
shape is used to identify either quotient.

Source: Aschbacher–Smith, E.4.3(2), printed pp. 241–242 (PDF pp. 252–253),
where the first local subgroup has shape S₅/E₁₆.
-/

namespace Sporadic.Mathieu.M22ValueBound.Concrete
open Subgroup Theory.GroupTheory
open scoped Pointwise

private noncomputable def firstEvenEquiv : inner.subgroupOf outerFirst ≃* first :=
  (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_left inner outerFirst).symm).trans
    ((Subgroup.subgroupOfEquivOfLe (show outerFirst ⊓ inner ≤ outerFirst from inf_le_left)).trans
      firstInnerEquiv)

/-- The setwise pair stabilizer in the full design automorphism group has order 3840. -/
public theorem outerFirst_card : Nat.card outerFirst = 3840 := by
  have hInner : inner = m22EvenDesignAut := by
    ext g
    simp [inner, M22, m22EvenDesignAut]
  have hIndex : inner.index = 2 := by rw [hInner]; exact m22EvenDesignAut_index
  have hle : (inner.subgroupOf outerFirst).index ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right
      (H := inner) (K := outerFirst) (L := ⊤) le_top (by simp [hIndex])
    rw [Subgroup.relIndex_top_right, hIndex] at h
    exact h
  let o : outerFirst :=
    ⟨⟨m22OddPairSwap, m22OddPairSwap_mem_designAut⟩, by
      change m22OddPairSwap • m22Pair12 = m22Pair12
      decide +kernel⟩
  have hne : inner.subgroupOf outerFirst ≠ ⊤ := by
    intro he
    have ho : o ∈ inner.subgroupOf outerFirst := he ▸ Subgroup.mem_top o
    exact m22OddPairSwap_not_mem_M22 ho
  have hOne : (inner.subgroupOf outerFirst).index ≠ 1 := by
    exact fun h => hne (Subgroup.index_eq_one.mp h)
  have hZero : (inner.subgroupOf outerFirst).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hTwo : (inner.subgroupOf outerFirst).index = 2 := by omega
  have hc : Nat.card (inner.subgroupOf outerFirst) = 1920 :=
    (Nat.card_congr firstEvenEquiv.toEquiv).trans m22PairStabilizer_card
  rw [← (inner.subgroupOf outerFirst).card_mul_index, hc, hTwo]

/-- The inner five-hexad action has kernel of order 16. -/
public theorem pairAction_ker_card : Nat.card pairAction.ker = 16 := by
  have hi : pairAction.ker.index = 120 := by
    rw [Subgroup.index_ker, pairAction.range_eq_top_of_surjective pairAction_surjective,
      Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    decide
  have h := pairAction.ker.card_mul_index
  rw [hi, m22PairStabilizer_card] at h
  omega

/-- The outer five-hexad action has kernel of order 32. -/
public theorem outerPairAction_ker_card : Nat.card outerPairAction.ker = 32 := by
  have hi : outerPairAction.ker.index = 120 := by
    rw [Subgroup.index_ker, outerPairAction.range_eq_top_of_surjective outerPairAction_surjective,
      Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    decide
  have h := outerPairAction.ker.card_mul_index
  rw [hi, outerFirst_card] at h
  omega

private theorem normal_two_perm_five_eq_bot (P : Subgroup (Equiv.Perm (Fin 5)))
    [P.Normal] (hP : IsPGroup 2 P) : P = ⊥ := by
  by_contra hn
  have hnt : Nontrivial P := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 5)) hnt
  have hdiv : 60 ∣ Nat.card P := by
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact hc ▸ card_dvd_of_le hle
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hthree : 3 ∣ 2 ^ n := hn ▸ (dvd_trans (by decide : 3 ∣ 60) hdiv)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)

private theorem ker_eq_twoCore_of_surjective_perm_five
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 5)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : f.ker = pCore 2 G := by
  have hle : f.ker ≤ pCore 2 G := le_sSup ⟨inferInstance, hk⟩
  apply le_antisymm hle
  have : ((pCore 2 G).map f).Normal := (inferInstance : (pCore 2 G).Normal).map f hf
  exact (Subgroup.map_eq_bot_iff _).mp
    (normal_two_perm_five_eq_bot _ (pCore_isPGroup.map f))

/-- The inner five-hexad action kernel is the intrinsic two-core. -/
public theorem pairAction_ker_eq_twoCore : pairAction.ker = pCore 2 first :=
  ker_eq_twoCore_of_surjective_perm_five pairAction pairAction_surjective
    (IsPGroup.of_card (n := 4) pairAction_ker_card)

/-- The outer five-hexad action kernel is the intrinsic two-core. -/
public theorem outerPairAction_ker_eq_twoCore : outerPairAction.ker = pCore 2 outerFirst :=
  ker_eq_twoCore_of_surjective_perm_five outerPairAction outerPairAction_surjective
    (IsPGroup.of_card (n := 5) outerPairAction_ker_card)

/-- The M₂₂ pair stabilizer modulo its intrinsic two-core is S₅. -/
public noncomputable def firstQuotientEquiv : (first ⧸ pCore 2 first) ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq pairAction_ker_eq_twoCore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective pairAction pairAction_surjective)

/-- The full-design pair stabilizer modulo its intrinsic two-core is S₅. -/
public noncomputable def outerFirstQuotientEquiv :
    (outerFirst ⧸ pCore 2 outerFirst) ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq outerPairAction_ker_eq_twoCore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective outerPairAction outerPairAction_surjective)

end Sporadic.Mathieu.M22ValueBound.Concrete
