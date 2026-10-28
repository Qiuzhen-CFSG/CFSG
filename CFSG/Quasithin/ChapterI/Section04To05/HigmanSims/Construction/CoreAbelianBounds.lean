module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreE8Count
public import Theory.ElementaryAbelian.ExtraspecialPrimeAbelianBound
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Abelian subgroups and elementary-eight centralizers in the HS point core

The original extraspecial factor has order32 and index two in the point
core. Its abelian subgroup bound gives an order16 bound in the whole core.
An abelian16 intersects that factor in an abelian8, which is
self-centralizing there; consequently it is self-centralizing in the whole
point core. Joining an elementary8 through the marked involution to the
central cyclic4 therefore identifies its point-core centralizer of order16.

All factors, subgroups and centralizers retain their original embeddings.
These are consequences of HS1--HS2 preceding Aschbacher--Smith I.4.8,
printed p.418.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims

private theorem subgroupOf_card_inf {Q : Type*} [Group Q] (A B : Subgroup Q) :
    Nat.card (A.subgroupOf B) = Nat.card (A ⊓ B : Subgroup Q) := by
  rw [← inf_subgroupOf_right]
  exact Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ B ≤ B from inf_le_right)).toEquiv

/-- Every abelian subgroup of the actual quaternion--cyclic point-core
shape has order at most sixteen. -/
theorem CoreShape.abelian_card_le {Q : Type*} [Group Q] [Finite Q]
    (h : CoreShape Q) (A : Subgroup Q) [IsMulCommutative A] : Nat.card A ≤ 16 := by
  have hQcard := h.card
  obtain ⟨B, D, ⟨hB⟩, _, _, _, _⟩ := h
  let : IsExtraspecial 2 B := hB.extraspecial
  have hiB : B.index = 2 := by
    have hh := B.card_mul_index
    rw [hB.card, hQcard] at hh
    omega
  let : B.Normal := normal_of_index_eq_two hiB
  have hi : Nat.card (A ⊓ B : Subgroup Q) ≤ 8 := by
    have hh := extraspecial_prime_abelian_card_sq_le_any (p := 2) (A.subgroupOf B)
    rw [subgroupOf_card_inf, hB.card] at hh
    nlinarith
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes B A
    (show A ≤ normalizer (B : Set Q) by rw [normalizer_eq_top]; exact le_top)
  rw [hB.card, inf_comm] at hp
  have hs : Nat.card (B ⊔ A : Subgroup Q) ≤ 64 := by
    exact (Nat.card_le_card_of_injective (B ⊔ A).subtype (B ⊔ A).subtype_injective).trans_eq hQcard
  have hb := Nat.mul_le_mul hi hs
  rw [← hp] at hb
  omega

private theorem abelian_sixteen_selfcentralizing {Q : Type*} [Group Q] [Finite Q]
    (h : CoreShape Q) (A : Subgroup Q) [IsMulCommutative A] (hA : Nat.card A = 16) :
    centralizer (A : Set Q) = A := by
  have hQcard := h.card
  obtain ⟨B, D, ⟨hB⟩, _, _, _, _⟩ := h
  let : IsExtraspecial 2 B := hB.extraspecial
  have hiB : B.index = 2 := by
    have hh := B.card_mul_index
    rw [hB.card, hQcard] at hh
    omega
  let : B.Normal := normal_of_index_eq_two hiB
  have hi : Nat.card (A ⊓ B : Subgroup Q) = 8 := by
    have hh := extraspecial_prime_abelian_card_sq_le_any (p := 2) (A.subgroupOf B)
    rw [subgroupOf_card_inf, hB.card] at hh
    have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes B A
      (show A ≤ normalizer (B : Set Q) by rw [normalizer_eq_top]; exact le_top)
    rw [hB.card, hA, inf_comm] at hp
    have hs : Nat.card (B ⊔ A : Subgroup Q) ≤ 64 :=
      (Nat.card_le_card_of_injective (B ⊔ A).subtype (B ⊔ A).subtype_injective).trans_eq hQcard
    have hb := Nat.mul_le_mul_left (Nat.card (A ⊓ B : Subgroup Q)) hs
    rw [← hp] at hb
    nlinarith
  have hself : centralizer (A.subgroupOf B : Set B) = A.subgroupOf B :=
    extraspecial_prime_selfcentralizing_of_card_sq (p := 2) (A.subgroupOf B)
      (by rw [subgroupOf_card_inf, hi, hB.card]; norm_num)
  let C := centralizer (A : Set Q)
  have hCB : C ⊓ B ≤ A ⊓ B := by
    rintro x ⟨hxC, hxB⟩
    have hx : (⟨x, hxB⟩ : B) ∈ centralizer (A.subgroupOf B : Set B) := by
      intro a ha
      exact Subtype.ext (hxC a ha)
    rw [hself] at hx
    exact ⟨hx, hxB⟩
  have hCI : Nat.card (C ⊓ B : Subgroup Q) ≤ 8 := (card_le_of_le hCB).trans_eq hi
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes B C
    (show C ≤ normalizer (B : Set Q) by rw [normalizer_eq_top]; exact le_top)
  rw [hB.card, inf_comm] at hp
  have hs : Nat.card (B ⊔ C : Subgroup Q) ≤ 64 :=
    (Nat.card_le_card_of_injective (B ⊔ C).subtype (B ⊔ C).subtype_injective).trans_eq hQcard
  have hb := Nat.mul_le_mul hCI hs
  rw [← hp] at hb
  symm
  apply eq_of_le_of_card_ge A.le_centralizer
  change Nat.card C ≤ Nat.card A
  rw [hA]
  omega

private theorem eight_centralizer_card {Q : Type*} [Group Q] [Finite Q]
    (h : CoreShape Q) (E : Subgroup Q) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (z : Q) (hzE : z ∈ E) (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) :
    Nat.card (centralizer (E : Set Q)) = 16 := by
  obtain ⟨e⟩ := h.center_model
  let : IsCyclic (center Q) := e.isCyclic.mpr inferInstance
  have hZ : Nat.card (center Q) = 4 := by rw [Nat.card_congr e.toEquiv]; simp
  have hi : E ⊓ center Q = zpowers z := by
    apply le_antisymm ?_ (zpowers_le.mpr (show z ∈ E ⊓ center Q from ⟨hzE, hzZ⟩))
    rintro x ⟨hxE, hxZ⟩
    by_cases hx1 : x = 1
    · exact hx1 ▸ (zpowers z).one_mem
    have hx2 : orderOf x = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hxE) hx1
    have heq : (⟨x, hxZ⟩ : center Q) = ⟨z, hzZ⟩ := IsCyclic.eq_of_orderOf_eq_two
      (by simpa only [← orderOf_coe] using hx2)
      (by simpa only [← orderOf_coe] using hz2)
    have hxz : x = z := congrArg Subtype.val heq
    exact hxz ▸ mem_zpowers z
  let A := E ⊔ center Q
  let : IsMulCommutative A := le_centralizer_iff_isMulCommutative.mp
    (sup_le (le_centralizer_iff.mpr (sup_le E.le_centralizer (center_le_centralizer _)))
      (center_le_centralizer _))
  have hA : Nat.card A = 16 := by
    have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes E (center Q)
      (center_le_normalizer (E : Set Q))
    rw [hE, hZ, hi, Nat.card_zpowers, hz2] at hp
    change 8 * 4 = 2 * Nat.card A at hp
    omega
  have hC : centralizer (E : Set Q) = centralizer (A : Set Q) := by
    apply le_antisymm ?_ (centralizer_le (show (E : Set Q) ⊆ (A : Set Q) from fun x hx => (le_sup_left : E ≤ A) hx))
    intro x hx a ha
    have hAcentral : A ≤ centralizer ({x} : Set Q) := sup_le
      (fun a ha => mem_centralizer_singleton_iff.mpr (hx a ha))
      (center_le_centralizer _)
    exact mem_centralizer_singleton_iff.mp (hAcentral ha)
  rw [hC, abelian_sixteen_selfcentralizing h A hA, hA]

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Every actual elementary eight through the marked involution has a
centralizer of order sixteen inside the original point core. -/
theorem TypeAt.point_core_eight_centralizer_card (h : TypeAt z V)
    (E : pointCoreEights z) :
    Nat.card ((involutionCentralizer z).pCoreIn 2 ⊓ centralizer (E.val : Set G) : Subgroup G) = 16 := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  let EQ := E.val.subgroupOf Q
  let := E.property.2.2.1
  let : IsElementaryAbelian 2 EQ := IsElementaryAbelian.subgroupOf E.property.1
  have hEQ : Nat.card EQ = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe E.property.1).toEquiv).trans E.property.2.2.2
  have hs : CoreShape Q := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv
      ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective)
  let zQ : Q := ⟨z, E.property.1 E.property.2.1⟩
  have hzZ : zQ ∈ center Q := mem_center_iff.mpr fun q => Subtype.ext
    (mem_centralizer_singleton_iff.mp (pCoreIn_le 2 H q.property))
  have hc : Nat.card (centralizer (EQ : Set Q)) = 16 :=
    eight_centralizer_card hs EQ hEQ zQ E.property.2.1 hzZ
      (by simpa only [← orderOf_coe] using h.involution)
  have hm : (centralizer (EQ : Set Q)).map Q.subtype =
      Q ⊓ centralizer (E.val : Set G) := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.property, ?_⟩
      intro a ha
      exact congrArg Subtype.val (hx (⟨a, E.property.1 ha⟩ : Q) ha)
    · rintro ⟨hxQ, hxE⟩
      refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
      intro a ha
      exact Subtype.ext (hxE a ha)
  rw [← hm, card_map_of_injective Q.subtype_injective]
  exact hc

end CFSG.Quasithin.HigmanSims
