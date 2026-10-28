module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointSixteenCoreBound
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedPointCorePlane
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreInvolutionFusion
public import Theory.Combinatorics.SixEightIncidence
public import Theory.GroupTheory.IndexTwoIntersection

/-!
# Reciprocal point-core incidences on the original elementary sixteen

The six points of the original nonseed eight away from its marked line
have either zero or four neighbors outside that eight. Each exterior point
has one or three neighbors among those six. Transitivity on the six makes
the first count uniform, forcing every point-core intersection to be an eight.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z u : G} {V : Subgroup G}

private theorem difference_card (B C : Subgroup G) :
    ((B : Set G) \ (C : Set G)).ncard = Nat.card B - Nat.card (B ⊓ C : Subgroup G) := by
  have he : (B : Set G) \ (C : Set G) = (B : Set G) \ ((B ⊓ C : Subgroup G) : Set G) := by
    ext x
    simp only [Set.mem_sdiff, SetLike.mem_coe, mem_inf]
    tauto
  rw [he, Set.ncard_sdiff (show ((B ⊓ C : Subgroup G) : Set G) ⊆ B from inf_le_left)]
  rfl

omit [Finite G] in
private theorem crossing_intersection_card (A E F : Subgroup G)
    [IsElementaryAbelian 2 A] (hA16 : Nat.card A = 16) (hE8 : Nat.card E = 8)
    (hEA : E ≤ A) (hFA : F ≤ A) (hcross : ¬ F ≤ E) :
    2 * Nat.card (F ⊓ E : Subgroup G) = Nat.card F := by
  let EA := E.subgroupOf A
  let FA := F.subgroupOf A
  have hEc : Nat.card EA = 8 := (Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv).trans hE8
  have hi : EA.index = 2 := by
    have hh := EA.card_mul_index
    rw [hEc, hA16] at hh
    omega
  have hnot : ¬ FA ≤ EA := by
    intro hh
    exact hcross fun x hx => hh (show (⟨x, hFA hx⟩ : A) ∈ FA from hx)
  have hh := (EA.subgroupOf FA).card_mul_index
  rw [subgroupOf_index_eq_two EA FA hi hnot] at hh
  have hc : Nat.card (EA.subgroupOf FA) = Nat.card (F ⊓ E : Subgroup G) := by
    rw [← card_subtype FA, subgroupOf_map_subtype,
      ← card_subtype A, map_inf _ _ _ A.subtype_injective,
      map_subgroupOf_eq_of_le hEA, map_subgroupOf_eq_of_le hFA, inf_comm]
  rw [hc, Nat.card_congr (subgroupOfEquivOfLe hFA).toEquiv] at hh
  omega

/-- The actual neighbors outside a nonseed eight form a row of size zero
or four; its size is the whole point-core intersection minus the original
intersection plane. -/
theorem TypeAt.nonseed_incidence_row_counts (h : TypeAt u V)
    (E : pointCoreEights u) (hEn : E.val ∉ pointCoreSeedOrbit u V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hEA : E.val ≤ A)
    (v : G) (hv : v ∈ E.val) (hvline : v ∉ zpowers u) :
    let row := {b : G | b ∈ A ∧ b ∉ E.val ∧ b ∈ (involutionCentralizer v).pCoreIn 2}
    row.ncard = Nat.card (A ⊓ (involutionCentralizer v).pCoreIn 2 : Subgroup G) - 4 ∧
      (row.ncard = 0 ∨ row.ncard = 4) := by
  let R := (involutionCentralizer v).pCoreIn 2
  have hcap : (A ⊓ R : Subgroup G) ⊓ E.val = E.val ⊓ R := by
    rw [inf_right_comm, inf_eq_right.mpr hEA]
  have he : {b : G | b ∈ A ∧ b ∉ E.val ∧ b ∈ R} =
      ((A ⊓ R : Subgroup G) : Set G) \ (E.val : Set G) := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, mem_inf]
    tauto
  have hc : ({b : G | b ∈ A ∧ b ∉ E.val ∧ b ∈ R} : Set G).ncard =
      Nat.card (A ⊓ R : Subgroup G) - 4 := by
    rw [he, difference_card, hcap,
      h.nonseed_eight_point_core_intersection_card E hEn v hv hvline]
  have hv1 : v ≠ 1 := fun hh => hvline (hh ▸ (zpowers u).one_mem)
  have hv2 : orderOf v = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian v (hEA hv)) hv1
  have hvu : IsConj v u := h.centralizer_core_involution_isConj v (E.property.1 hv) hv2
  have hb := h.elementary_sixteen_conjugate_point_core_card A hA v (hEA hv) hvu
  refine ⟨hc, ?_⟩
  rw [hc]
  rcases hb with hb | hb
  · exact Or.inl (by rw [hb])
  · exact Or.inr (by rw [hb])

/-- An exterior point has one or three reciprocal neighbors in the six
points away from the marked line. Its original intersection with the eight
has half the order of its whole elementary-sixteen point-core intersection. -/
theorem TypeAt.nonseed_incidence_column_counts (h : TypeAt z V)
    (huT : TypeAt u V) (E : pointCoreEights u)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hEA : E.val ≤ A)
    (hAQ : A ⊓ (involutionCentralizer u).pCoreIn 2 = E.val)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (b : G) (hbA : b ∈ A) (hbE : b ∉ E.val) :
    let column := {v : G | v ∈ E.val ∧ v ∉ zpowers u ∧
      b ∈ (involutionCentralizer v).pCoreIn 2}
    column.ncard = Nat.card (E.val ⊓ (involutionCentralizer b).pCoreIn 2 : Subgroup G) - 1 ∧
      2 * Nat.card (E.val ⊓ (involutionCentralizer b).pCoreIn 2 : Subgroup G) =
        Nat.card (A ⊓ (involutionCentralizer b).pCoreIn 2 : Subgroup G) ∧
      (column.ncard = 1 ∨ column.ncard = 3) := by
  classical
  let Q := (involutionCentralizer b).pCoreIn 2
  let F := A ⊓ Q
  let C := E.val ⊓ Q
  have hb1 : b ≠ 1 := fun he => hbE (he ▸ E.val.one_mem)
  have hu1 : u ≠ 1 := by
    intro he
    have hh := huT.involution
    simp [he] at hh
  have hbz : IsConj b z := hpure b hbA hb1
  have huz : IsConj u z := hpure u (hEA E.property.2.1) hu1
  have huQ : u ∉ Q := by
    intro huQ
    have hbQ := (h.conjugate_point_core_reciprocal u b huz hbz).mpr huQ
    exact hbE (hAQ ▸ (show b ∈ A ⊓ (involutionCentralizer u).pCoreIn 2 from ⟨hbA, hbQ⟩))
  obtain ⟨W, hbT⟩ := h.exists_typeAt_of_isConj b hbz
  have hbb : b ∈ Q := by
    change b ∈ (pCore 2 (involutionCentralizer b)).map (involutionCentralizer b).subtype
    rw [← hbT.centralizer_fitting]
    exact hbT.seed_le_core hbT.involution_mem_seed
  have hcross : ¬ F ≤ E.val := fun hh => hbE (hh ⟨hbA, hbb⟩)
  have hdouble : 2 * Nat.card C = Nat.card F := by
    have hh := crossing_intersection_card A E.val F hA E.property.2.2.2 hEA inf_le_left hcross
    have he : F ⊓ E.val = C := by
      change (A ⊓ Q : Subgroup G) ⊓ E.val = E.val ⊓ Q
      rw [inf_right_comm, inf_eq_right.mpr hEA]
    rwa [he] at hh
  have hCU : C ⊓ zpowers u = ⊥ := by
    apply eq_bot_iff.mpr
    intro v hv
    have hvQ : v ∈ Q := hv.1.2
    have hvU : v ∈ zpowers u := hv.2
    rw [mem_zpowers_iff_mem_range_orderOf, huT.involution] at hvU
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hvU
    have hn2 : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · simp
    · exact (huQ (by simpa using hvQ)).elim
  have hcol : {v : G | v ∈ E.val ∧ v ∉ zpowers u ∧
      b ∈ (involutionCentralizer v).pCoreIn 2} = (C : Set G) \ (zpowers u : Set G) := by
    ext v
    constructor
    · rintro ⟨hv, hvU, hbQ⟩
      have hv1 : v ≠ 1 := fun he => hvU (he ▸ (zpowers u).one_mem)
      exact ⟨⟨hv, (h.conjugate_point_core_reciprocal v b (hpure v (hEA hv) hv1) hbz).mp hbQ⟩, hvU⟩
    · rintro ⟨⟨hv, hvQ⟩, hvU⟩
      have hv1 : v ≠ 1 := fun he => hvU (he ▸ (zpowers u).one_mem)
      exact ⟨hv, hvU, (h.conjugate_point_core_reciprocal v b (hpure v (hEA hv) hv1) hbz).mpr hvQ⟩
  have hcount : ({v : G | v ∈ E.val ∧ v ∉ zpowers u ∧
      b ∈ (involutionCentralizer v).pCoreIn 2} : Set G).ncard = Nat.card C - 1 := by
    rw [hcol, difference_card, hCU, card_bot]
  refine ⟨hcount, hdouble, ?_⟩
  rw [hcount]
  have hf := h.elementary_sixteen_conjugate_point_core_card A hA b hbA hbz
  change Nat.card C - 1 = 1 ∨ Nat.card C - 1 = 3
  change Nat.card F = 4 ∨ Nat.card F = 8 at hf
  rcases hf with hf | hf <;> omega

end CFSG.Quasithin.HigmanSims
