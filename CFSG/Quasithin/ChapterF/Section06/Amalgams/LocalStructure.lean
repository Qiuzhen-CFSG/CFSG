module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.Rigidity.Local
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Cubic residuals at exceptional Goldschmidt vertices

Failure of local characteristic two supplies the actual normal residual
of order three and its centralization of the local two-core. If both
vertices fail, the intersection of their two-cores is normalized by the
common Sylow subgroup and centralized by both residuals. The genuine
common-normal-core theorem kills that intersection. The two index-two
quotients then bound the common Sylow order by four.

Source: the exceptional branch of Aschbacher–Smith F.6.5, printed p.305.
No assertion about the ambient residual being odd is needed here.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

 theorem IsGoldschmidtTriple.local_solvable (h : IsGoldschmidtTriple G₁ G₂) :
    Group.IsSolvable G₁ := SymmetricThreeTwoCore.solvable h.quotient_left.some

 theorem IsGoldschmidtTriple.local_residual_order_three
    (h : IsGoldschmidtTriple G₁ G₂) (hbad : generalizedFitting G₁ ≠ pCore 2 G₁) :
    Nat.card (pResidual 2 G₁) = 3 := by
  rw [SymmetricThreeTwoCore.residual_eq_oddCore h.quotient_left.some hbad]
  exact SymmetricThreeTwoCore.oddCore_card_of_not_characteristic_two h.quotient_left.some hbad

 theorem IsGoldschmidtTriple.local_core_centralizes_residual
    (h : IsGoldschmidtTriple G₁ G₂) (hbad : generalizedFitting G₁ ≠ pCore 2 G₁) :
    (pCore 2 G₁).map G₁.subtype ≤ centralizer ((pResidual 2 G₁).map G₁.subtype : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← map_commutator, commutator_eq_bot_iff_le_centralizer.mpr
    (SymmetricThreeTwoCore.core_centralizes_residual h.quotient_left.some hbad), Subgroup.map_bot]

 theorem IsGoldschmidtTriple.core_intersection_eq_bot_of_neither_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (h₁ : generalizedFitting G₁ ≠ pCore 2 G₁)
    (h₂ : generalizedFitting G₂ ≠ pCore 2 G₂) :
    (pCore 2 G₁).map G₁.subtype ⊓ (pCore 2 G₂).map G₂.subtype = ⊥ := by
  let Q₁ := (pCore 2 G₁).map G₁.subtype
  let Q₂ := (pCore 2 G₂).map G₂.subtype
  let N := Q₁ ⊓ Q₂
  have hNT : N ≤ G₁ ⊓ G₂ := inf_le_left.trans h.local_twoCore_le_intersection
  have hTN : G₁ ⊓ G₂ ≤ normalizer (N : Set G) :=
    (le_inf (inf_le_left.trans h.left_core_normalized)
      (inf_le_right.trans h.symm.left_core_normalized)).trans
        inf_normalizer_le_normalizer_inf
  apply h.common_normal_eq_bot hcore N hNT
  · apply (normal_subgroupOf_iff_le_normalizer (hNT.trans inf_le_left)).mpr
    rw [← h.left_residual_sup_intersection]
    refine sup_le ?_ hTN
    exact (le_centralizer_iff.mpr
      (inf_le_left.trans (h.local_core_centralizes_residual h₁))).trans
        (centralizer_le_normalizer _)
  · apply (normal_subgroupOf_iff_le_normalizer (hNT.trans inf_le_right)).mpr
    rw [← h.right_residual_sup_intersection]
    refine sup_le ?_ hTN
    exact (le_centralizer_iff.mpr
      (inf_le_right.trans (h.symm.local_core_centralizes_residual h₂))).trans
        (centralizer_le_normalizer _)

 theorem IsGoldschmidtTriple.intersection_card_of_neither_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (h₁ : generalizedFitting G₁ ≠ pCore 2 G₁)
    (h₂ : generalizedFitting G₂ ≠ pCore 2 G₂) :
    Nat.card (G₁ ⊓ G₂ : Subgroup G) = 2 ∨ Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4 := by
  let T := G₁ ⊓ G₂
  let K₁ := ((pCore 2 G₁).map G₁.subtype).subgroupOf T
  let K₂ := ((pCore 2 G₂).map G₂.subtype).subgroupOf T
  have hi₁ : K₁.index = 2 := h.left_core_index
  have hi₂ : K₂.index = 2 := by
    change ((pCore 2 G₂).map G₂.subtype).relIndex (G₁ ⊓ G₂) = 2
    simpa only [inf_comm G₂ G₁] using h.symm.left_core_index
  have hmeet : K₁ ⊓ K₂ = ⊥ := by
    change ((pCore 2 G₁).map G₁.subtype ⊓ (pCore 2 G₂).map G₂.subtype).comap T.subtype = ⊥
    rw [h.core_intersection_eq_bot_of_neither_characteristic_two hcore h₁ h₂]
    exact (MonoidHom.ker_eq_bot_iff T.subtype).mpr T.subtype_injective
  have hbound := index_inf_le (H := K₁) (K := K₂)
  rw [hmeet, index_bot, hi₁, hi₂] at hbound
  have hc := K₁.index_mul_card
  rw [hi₁] at hc
  have hp := Nat.card_pos (α := T)
  change Nat.card T = 2 ∨ Nat.card T = 4
  omega
end CFSG.Quasithin.ChapterF
