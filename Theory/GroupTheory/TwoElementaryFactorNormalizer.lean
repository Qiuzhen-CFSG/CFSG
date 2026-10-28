module
public import Theory.GroupTheory.TwoElementaryIndexTwo
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# A normalizer fixing one elementary factor fixes the other

In a noncommutative finite group, two distinct elementary subgroups of
index two contain every elementary subgroup. An automorphism fixing the
first must therefore fix the second. The ambient version retains the
original factors and their join, as needed for13.5.11.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Preserve the second original elementary factor after preserving the first. -/
theorem normalizes_second_elementary_factor (A B : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hB : IsElementaryAbelian 2 B)
    (hiA : A.relIndex (A ⊔ B) = 2) (hiB : B.relIndex (A ⊔ B) = 2)
    (hJ : ¬ IsMulCommutative (A ⊔ B : Subgroup G)) :
    normalizer ((A ⊔ B : Subgroup G) : Set G) ⊓ normalizer (A : Set G) ≤ normalizer (B : Set G) := by
  let J := A ⊔ B
  let A₀ := A.subgroupOf J
  let B₀ := B.subgroupOf J
  let := hA
  let := hB
  have ha : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf le_sup_left
  have hb : IsElementaryAbelian 2 B₀ := IsElementaryAbelian.subgroupOf le_sup_right
  have hne : A ≠ B := by
    intro he
    rw [he,sup_idem,relIndex_self] at hiA
    contradiction
  have hne₀ : A₀ ≠ B₀ := by
    intro he
    apply hne
    have hm := congrArg (Subgroup.map J.subtype) he
    change (A.subgroupOf J).map J.subtype = (B.subgroupOf J).map J.subtype at hm
    rwa [map_subgroupOf_eq_of_le (show A ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show B ≤ J from le_sup_right)] at hm
  have hn : ¬ IsElementaryAbelian 2 J := fun he => hJ he.toIsMulCommutative
  intro g hg
  let E := B.map (MulAut.conj g).toMonoidHom
  have heJ : E ≤ J := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) (show B ≤ J from le_sup_right)
    exact hm.trans_eq (mem_normalizer_iff_map_conj_eq.mp hg.1)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have he : IsElementaryAbelian 2 (E.subgroupOf J) := IsElementaryAbelian.subgroupOf heJ
  have hcard : Nat.card A = Nat.card B := by
    have hca := A₀.card_mul_index
    have hcb := B₀.card_mul_index
    change Nat.card (A.subgroupOf J) * A.relIndex (A ⊔ B) = Nat.card J at hca
    change Nat.card (B.subgroupOf J) * B.relIndex (A ⊔ B) = Nat.card J at hcb
    rw [hiA,Nat.card_congr (subgroupOfEquivOfLe (show A ≤ J from le_sup_left)).toEquiv] at hca
    rw [hiB,Nat.card_congr (subgroupOfEquivOfLe (show B ≤ J from le_sup_right)).toEquiv] at hcb
    omega
  have hEcard : Nat.card E = Nat.card B := card_map_of_injective (MulAut.conj g).injective
  have hal := elementary_le_one_of_two_index_two A₀ B₀ ha hb hiA hiB hne₀ hn
    (E.subgroupOf J) he
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases hal with hal | hal
  · have hEA : E ≤ A := by
      intro x hx
      exact hal (show (⟨x,heJ hx⟩ : J) ∈ E.subgroupOf J from hx)
    have hEAeq : E = A := eq_of_le_of_card_ge hEA (hEcard.trans hcard.symm).ge
    have hAeq := mem_normalizer_iff_map_conj_eq.mp hg.2
    exact (hne ((map_injective (MulAut.conj g).injective)
      (hAeq.trans hEAeq.symm))).elim
  · have hEB : E ≤ B := by
      intro x hx
      exact hal (show (⟨x,heJ hx⟩ : J) ∈ E.subgroupOf J from hx)
    exact eq_of_le_of_card_ge hEB hEcard.ge

end Subgroup
