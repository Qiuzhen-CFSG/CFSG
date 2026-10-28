module
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order

/-!
# Binary radical bounds for small Mathieu sections in J₄

A marked quotient modulo the two-core contributes its full two-part to
the index of any normalized two-group. The two-part of |J₄| is 2²¹,
so the M₁₂ and M₂₂ sections bound that two-group by 2¹⁵ and 2¹⁴.
The homomorphism retains its original two-group kernel, and the markings
retain the full center of the quotient by the two-core.

Source application: Aschbacher–Smith 4.2.13, printed pp.611–612.
The actual carrier orders and their ATLAS attribution come from the imports.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace Janko4
attribute [local irreducible] modelGroup matrixA matrixB

theorem normalized_twoGroup_card_le_of_core_index
    {F : Type*} [Group F] [Finite F]
    (f : F →* Model) (hk : IsPGroup 2 f.ker)
    (d : ℕ) (hd : 2 ^ d ∣ Nat.card (F ⧸ pCore 2 F))
    (U : Subgroup Model) (hU : IsPGroup 2 U)
    (hn : f.range ≤ normalizer (U : Set Model)) :
    ∃ n : ℕ, Nat.card U = 2 ^ n ∧ n + d ≤ 21 := by
  let B := U.comap f
  have hBn : B.Normal := by
    refine ⟨?_⟩
    intro b hb a
    change f (a*b*a⁻¹) ∈ U
    simpa only [map_mul,map_inv] using
      (mem_normalizer_iff.mp (hn (show f a ∈ f.range from ⟨a,rfl⟩)) (f b)).mp hb
  let := hBn
  have hBP : B ≤ pCore 2 F := le_sSup ⟨hBn,hU.comap_of_ker_isPGroup f hk⟩
  have hi : 2 ^ d ∣ U.relIndex f.range := by
    rw [←index_comap]
    exact hd.trans (index_dvd_of_le hBP)
  have hjoin : U.relIndex (f.range ⊔ U) = U.relIndex f.range := by
    let N := f.range ⊔ U
    let : (U.subgroupOf N).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le hn U.le_normalizer)
    have hh := relIndex_sup_right (f.range.subgroupOf N) (U.subgroupOf N)
    rw [←subgroupOf_sup le_sup_left le_sup_right,
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf le_sup_left] at hh
    exact hh
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup Model) U (f.range ⊔ U) bot_le le_sup_right
  simp only [relIndex_bot_left,hjoin] at hcount
  have hdiv : Nat.card U * 2 ^ d ∣ Nat.card Model := by
    apply (show Nat.card U * 2^d ∣ Nat.card (f.range ⊔ U : Subgroup Model) from ?_).trans
      (card_subgroup_dvd_card _)
    rw [←hcount]
    exact Nat.mul_dvd_mul_left _ hi
  obtain ⟨n,hnc⟩ := hU.exists_card_eq
  refine ⟨n,hnc,?_⟩
  rw [hnc,←pow_add] at hdiv
  by_contra hh
  have h22 : 2^22 ∣ Nat.card Model :=
    (pow_dvd_pow 2 (by omega : 22 ≤ n+d)).trans hdiv
  rw [Cardinality.model_card] at h22
  norm_num at h22

theorem small_mathieu_normalized_twoGroup_card_le
    {F : Type*} [Group F] [Finite F]
    (f : F →* Model) (hk : IsPGroup 2 f.ker)
    (U : Subgroup Model) (hU : IsPGroup 2 U)
    (hn : f.range ≤ normalizer (U : Set Model)) :
    (Nonempty (((F ⧸ pCore 2 F) ⧸ center (F ⧸ pCore 2 F)) ≃* Sporadic.Mathieu.M12) →
      Nat.card U ≤ 32768) ∧
    (Nonempty (((F ⧸ pCore 2 F) ⧸ center (F ⧸ pCore 2 F)) ≃* Sporadic.Mathieu.M22) →
      Nat.card U ≤ 16384) := by
  constructor
  · rintro ⟨e⟩
    have hd : 2^6 ∣ Nat.card (F ⧸ pCore 2 F) := by
      apply (show 2^6 ∣ Nat.card ((F ⧸ pCore 2 F) ⧸ center (F ⧸ pCore 2 F)) from ?_).trans
        (card_quotient_dvd_card _)
      rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m12_order]
      decide
    obtain ⟨n,he,hb⟩ := normalized_twoGroup_card_le_of_core_index f hk 6 hd U hU hn
    rw [he]
    exact (Nat.pow_le_pow_right (by decide) (by omega : n ≤ 15)).trans_eq (by decide)
  · rintro ⟨e⟩
    have hd : 2^7 ∣ Nat.card (F ⧸ pCore 2 F) := by
      apply (show 2^7 ∣ Nat.card ((F ⧸ pCore 2 F) ⧸ center (F ⧸ pCore 2 F)) from ?_).trans
        (card_quotient_dvd_card _)
      rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
      decide
    obtain ⟨n,he,hb⟩ := normalized_twoGroup_card_le_of_core_index f hk 7 hd U hU hn
    rw [he]
    exact (Nat.pow_le_pow_right (by decide) (by omega : n ≤ 14)).trans_eq (by decide)
end Janko4
