module

public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Cubic residuals and normalizing Sylow supplements

A subgroup with cubic two-core quotient has index three over a normalizing
Sylow two-subgroup after adjoining it. More generally a three-power two-core
quotient gives solvability, and adjoining a normalizing two-group preserves
the three-part of the order. Distinctness of two cubic residuals follows when
their join has two-core quotient of order nine.

These elementary finite-group calculations provide the algebraic input to
common binary flag coordinates in Aschbacher–Smith 13.8.25, printed p.960.
The index argument follows the normal-product calculation also used in the
chapter's OrdinarySource.LocalAlgebra, without its source-specific inputs.
-/

public section
open Subgroup
namespace BinaryLinear.CubicPairGeometry
variable {G : Type*} [Group G] [Finite G]

private theorem normalized_sup_index (Y S : Subgroup G)
    (hn : S ≤ normalizer (Y : Set G)) : S.relIndex (Y ⊔ S) = S.relIndex Y := by
  let J := Y ⊔ S
  let _ : (Y.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hn)
  have aux (A B : Subgroup J) [A.Normal] : B.relIndex (A ⊔ B) = B.relIndex A := by
    have hm : A.relIndex B * B.relIndex (A ⊔ B) = A.relIndex B * B.relIndex A := by
      calc
        _ = (B ⊓ A).relIndex (A ⊔ B) := by
          rw [← inf_relIndex_left (H := B) (K := A)]
          exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
        _ = (B ⊓ A).relIndex A * A.relIndex (A ⊔ B) :=
          (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
        _ = _ := by simp [inf_relIndex_right, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (index_ne_zero_of_finite : A.relIndex B ≠ 0)) hm
  have hi := aux (Y.subgroupOf J) (S.subgroupOf J)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf le_sup_left] at hi
  exact hi

/-- A normalizing Sylow has index three after adjoining a subgroup with cubic two-core quotient. -/
theorem cubic_join_index (U : Sylow 2 G) (A : Subgroup G)
    (hn : (U : Subgroup G) ≤ normalizer (A : Set G))
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    (U : Subgroup G).relIndex (A ⊔ U) = 3 := by
  have hi := normalized_sup_index A U hn
  have hd : (U : Subgroup G).relIndex (A ⊔ U) ∣ Nat.card A := by
    rw [hi]
    exact relIndex_dvd_card _ _
  have hs : Nat.card (pCore 2 A) * 3 = Nat.card A := by
    simpa only [Subgroup.index, hc] using (pCore 2 A).card_mul_index
  obtain ⟨n, hn'⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  rw [← hs, hn'] at hd
  have hodd : ¬ 2 ∣ (U : Subgroup G).relIndex (A ⊔ U) :=
    (U.subtype (show (U : Subgroup G) ≤ A ⊔ U from le_sup_right)).not_dvd_index
  have hcop : ((U : Subgroup G).relIndex (A ⊔ U)).Coprime 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hodd).symm
  have hd3 := (hcop.pow_right n).dvd_of_dvd_mul_left hd
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd3 with he | he
  · have hAU : A ≤ U := le_sup_left.trans (relIndex_eq_one.mp he)
    have hp := U.isPGroup'.to_le hAU
    have hdA : 3 ∣ Nat.card A := hc ▸ (pCore 2 A).index_dvd_card
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk] at hdA
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hdA) |>.elim
  · exact he

private theorem three_part_two_group {D : Type*} [Group D] [Finite D]
    (h : IsPGroup 2 D) : (Nat.card D).factorization 3 = 0 := by
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [hn, Nat.factorization_pow]
  simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]

/-- A normalizing two-group contributes no factor of three to a join. -/
theorem normalized_join_three_part (A U : Subgroup G) (hu : IsPGroup 2 U)
    (hn : U ≤ normalizer (A : Set G)) :
    (Nat.card (A ⊔ U : Subgroup G)).factorization 3 = (Nat.card A).factorization 3 := by
  have hi := normalized_sup_index A U hn
  have h1 := (U.subgroupOf (A ⊔ U)).card_mul_index
  have h2 := (U.subgroupOf A).card_mul_index
  change Nat.card (U.subgroupOf (A ⊔ U)) * U.relIndex (A ⊔ U) = _ at h1
  change Nat.card (U.subgroupOf A) * U.relIndex A = _ at h2
  have hnz : U.relIndex A ≠ 0 := index_ne_zero_of_finite
  rw [← h1, ← h2, hi, Nat.factorization_mul Nat.card_pos.ne' hnz,
    Nat.factorization_mul Nat.card_pos.ne' hnz]
  simp only [Finsupp.add_apply]
  have hz1 : (Nat.card (U.subgroupOf (A ⊔ U))).factorization 3 = 0 :=
    three_part_two_group hu.comap_subtype
  have hz2 : (Nat.card (U.subgroupOf A)).factorization 3 = 0 :=
    three_part_two_group hu.comap_subtype
  rw [hz1, hz2]

/-- The valuation at three of a group with two-core quotient of order nine is two. -/
theorem three_part_of_core_quotient_nine (A : Subgroup G)
    (hc : Nat.card (A ⧸ pCore 2 A) = 9) : (Nat.card A).factorization 3 = 2 := by
  rw [← (pCore 2 A).card_mul_index, Subgroup.index, hc,
    Nat.factorization_mul Nat.card_pos.ne' (by decide)]
  simp only [Finsupp.add_apply, three_part_two_group pCore_isPGroup, zero_add]
  rw [show 9 = 3 ^ 2 from rfl, Nat.factorization_pow]
  simp [Nat.Prime.factorization_self Nat.prime_three]

/-- A three-power two-core quotient gives solvability, also after adjoining a normalizing two-group. -/
theorem normalized_join_solvable (A U : Subgroup G) (hu : IsPGroup 2 U)
    (hn : U ≤ normalizer (A : Set G)) (k : ℕ)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3 ^ k) : Group.IsSolvable (A ⊔ U : Subgroup G) := by
  let : Group.IsNilpotent (pCore 2 A) := (pCore_isPGroup (p := 2) (G := A)).isNilpotent
  let : Group.IsNilpotent (A ⧸ pCore 2 A) := (IsPGroup.of_card hc).isNilpotent
  let : Group.IsSolvable A := (Group.isSolvable_iff_subgroup_quotient (pCore 2 A)).mpr
    ⟨inferInstance, inferInstance⟩
  let : Group.IsNilpotent U := hu.isNilpotent
  let J := A ⊔ U
  let N := A.subgroupOf J
  let S := U.subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show A ≤ J from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show A ≤ J from le_sup_left)).injective
  let : Group.IsSolvable S := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show U ≤ J from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show U ≤ J from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top N S
  rw [← subgroupOf_sup (show A ≤ J from le_sup_left) (show U ≤ J from le_sup_right)]
  exact subgroupOf_self _

omit [Finite G] in
/-- The two marked residuals, and hence their Sylow supplements, are distinct. -/
theorem cubic_joins_ne (U : Sylow 2 G) (A B : Subgroup G)
    (ha : IsPPerfect 2 A) (hb : IsPPerfect 2 B)
    (hna : (U : Subgroup G) ≤ normalizer (A : Set G))
    (hnb : (U : Subgroup G) ≤ normalizer (B : Set G))
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hab : Nat.card ((A ⊔ B : Subgroup G) ⧸ pCore 2 (A ⊔ B : Subgroup G)) = 9) :
    A ⊔ (U : Subgroup G) ≠ B ⊔ U := by
  intro he
  have hr := congrArg (fun P : Subgroup G => (pResidual 2 P).map P.subtype) he
  rw [embedded_pResidual_join_pGroup A U ha U.isPGroup' hna,
    embedded_pResidual_join_pGroup B U hb U.isPGroup' hnb] at hr
  rw [← hr, sup_idem, hc] at hab
  norm_num at hab
end BinaryLinear.CubicPairGeometry
