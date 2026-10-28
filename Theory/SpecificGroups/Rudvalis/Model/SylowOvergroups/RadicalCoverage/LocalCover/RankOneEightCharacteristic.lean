module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic.WordFacts
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue
public import Theory.ElementaryAbelian.BinaryExpansion

/-!
# The characteristic marked eight-subgroup of the Rudvalis local group

The three original marked words generate an elementary abelian group of
order eight, normalized by all four generators of `localP`. The complete
normal elementary catalogue has only one row of this order: its first two
rows have order at most four, and each later row contains nine distinct
explicit words. An arbitrary automorphism of `localP` preserves normality,
elementary abelianness and cardinality, and hence fixes the marked subgroup.
This includes automorphisms induced by possible ambient outer actions.

No full model order, simplicity or outer automorphism theorem is used.
The carrier and words are the original degree-4060 Rudvalis model, with
ATLAS attribution preserved in `LocalCover.Data`. The source application
is Aschbacher--Smith 15.3.43, printed p.1140, the list 1.1.5(3)(f), p.502,
and GLS3 Table 5.3r. This module proves the concrete characteristicity input;
it does not itself assert the full sporadic exclusion.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic
open Subgroup
open scoped IsMulCommutative

private theorem binary_closure {G : Type*} [Group G] [Finite G] {n : ℕ} (g : Fin n → G)
    (hc : ∀ i j, Commute (g i) (g j)) (hs : ∀ i, g i * g i = 1) :
    IsElementaryAbelian 2 (closure (Set.range g)) ∧
      Nat.card (closure (Set.range g)) ≤ 2 ^ n := by
  classical
  let H := closure (Set.range g)
  let : IsMulCommutative H := isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (hc i j).eq)
  have hp (x : G) (hx : x ∈ H) : x ^ 2 = 1 := by
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact (pow_two _).trans (hs i)
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      rw [(show Commute x y from setLike_mul_comm hx hy).mul_pow, ihx, ihy, one_mul]
    | inv x _ ih => rw [inv_pow, ih, inv_one]
  refine ⟨{ exponent_dvd_p := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    (fun x => Subtype.ext (hp x x.property))) }, ?_⟩
  let g' : Fin n → H := fun i => ⟨g i, subset_closure ⟨i, rfl⟩⟩
  have hg' : closure (Set.range g') = ⊤ := by
    apply map_injective H.subtype_injective
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rw [← MonoidHom.range_eq_map, range_subtype]
    rfl
  let f : (Fin n → Bool) → H := fun b => ∏ i, if b i then g' i else 1
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨b, hb⟩ := Theory.GroupTheory.exists_bool_prod_of_mem_closure_range
      g' (fun i => Subtype.ext (hs i)) (show x ∈ closure (Set.range g') by rw [hg']; trivial)
    exact ⟨b, hb.symm⟩
  simpa using Nat.card_le_card_of_surjective f hf

/-- The marked subgroup really is elementary abelian on the original carrier. -/
public theorem elementary_two_elementary : IsElementaryAbelian 2 (elementary 2) := by
  have h := (binary_closure basis basis_commute basis_square).1
  rwa [closure_basis] at h

/-- Binary expansion gives the upper bound, and the eight separated words give equality. -/
public theorem elementary_two_card : Nat.card (elementary 2) = 8 := by
  have h := (binary_closure basis basis_commute basis_square).2
  rw [closure_basis] at h
  exact Nat.le_antisymm h eight_le_card

/-- The fixed local subgroup normalizes the marked eight-subgroup. -/
public theorem localP_le_normalizer_elementary_two :
    localP ≤ normalizer (elementary 2 : Set Model) := by
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  apply mem_normalizer_fintype
  intro x hx
  have hle : closure (Set.range basis) ≤
      (elementary 2).comap (MulAut.conj (localGenerators i)).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact conjugate_basis_mem i j
  exact hle (closure_basis.symm ▸ hx)

/-- Normality is inside `localP`, not inside the ambient simple model. -/
public theorem elementary_two_normal : ((elementary 2).subgroupOf localP).Normal :=
  (normal_subgroupOf_iff_le_normalizer (elementary_le_localP 2)).mpr
    localP_le_normalizer_elementary_two

private theorem one_card_le_four : Nat.card (elementary 1) ≤ 4 := by
  let pair : Fin 2 → Model := ![basis 0, basis 1]
  have hgen : closure (Set.range pair) = elementary 1 := by
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [pair, basis]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hcomm (i j : Fin 2) : Commute (pair i) (pair j) := by
    fin_cases i <;> fin_cases j <;> exact basis_commute _ _
  have hsquare (i : Fin 2) : pair i * pair i = 1 := by
    fin_cases i <;> exact basis_square _
  have h := (binary_closure pair hcomm hsquare).2
  rwa [hgen] at h

/-- Only catalogue row two can have order eight; larger exact orders are unnecessary. -/
public theorem index_eq_two_of_card_eight (i : Fin 6)
    (hcard : Nat.card (elementary i) = 8) : i = 2 := by
  have hsmall : Nat.card (elementary 0) ≤ 4 := by
    have hle : elementary 0 ≤ elementary 1 := closure_mono (by simp [Set.subset_def])
    exact (Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)).trans one_card_le_four
  have hlarge (j : Fin 6) (hle : elementary 3 ≤ elementary j) :
      9 ≤ Nat.card (elementary j) := nine_le_card.trans
        (Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
  fin_cases i
  · change Nat.card (elementary 0) = 8 at hcard
    omega
  · change Nat.card (elementary 1) = 8 at hcard
    have := one_card_le_four
    omega
  · rfl
  · change Nat.card (elementary 3) = 8 at hcard
    have := nine_le_card
    omega
  · have hh := hlarge 4 (closure_mono (by simp [Set.subset_def]))
    change Nat.card (elementary 4) = 8 at hcard
    omega
  · have hh := hlarge 5 (closure_mono (by simp [Set.subset_def]))
    change Nat.card (elementary 5) = 8 at hcard
    omega

/-- The unique relatively normal elementary subgroup of order eight. -/
public theorem eq_elementary_two_of_normal_eight (E : Subgroup Model)
    (hEP : E ≤ localP) (hn : localP ≤ normalizer (E : Set Model))
    (hE : IsElementaryAbelian 2 E) (hc : Nat.card E = 8) : E = elementary 2 := by
  have hne : E ≠ ⊥ := by
    intro hb
    rw [hb] at hc
    norm_num at hc
  obtain ⟨i, hi⟩ := elementaryCatalogue E hne hEP hn hE
  have hi2 : i = 2 := index_eq_two_of_card_eight i (hi ▸ hc)
  exact hi.trans (congrArg elementary hi2)

/-- The marked eight-subgroup is fixed by every automorphism of `localP`. -/
public theorem elementary_two_characteristic :
    ((elementary 2).subgroupOf localP).Characteristic := by
  let H := (elementary 2).subgroupOf localP
  let : IsElementaryAbelian 2 (elementary 2) := elementary_two_elementary
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.subgroupOf (elementary_le_localP 2)
  have hHnormal : H.Normal := elementary_two_normal
  have hHcard : Nat.card H = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (elementary_le_localP 2)).toEquiv).trans elementary_two_card
  apply characteristic_iff_map_eq.mpr
  intro α
  let A : Subgroup localP := H.map α.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map α.toMonoidHom
  have hA : A.Normal := hHnormal.map α.toMonoidHom α.surjective
  let E : Subgroup Model := A.map localP.subtype
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map_subtype
  have hcard : Nat.card E = 8 := by
    rw [card_map_of_injective localP.subtype_injective,
      card_map_of_injective α.injective]
    exact hHcard
  have hn : localP ≤ normalizer (E : Set Model) := by
    apply le_normalizer_iff.mpr
    intro p hp x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    exact mem_map.mpr ⟨(⟨p, hp⟩ : localP) * a * (⟨p, hp⟩ : localP)⁻¹,
      hA.conj_mem a ha ⟨p, hp⟩, rfl⟩
  have hfixed : E = elementary 2 :=
    eq_elementary_two_of_normal_eight E (map_subtype_le A) hn hE hcard
  apply map_injective localP.subtype_injective
  exact hfixed.trans (map_subgroupOf_eq_of_le (elementary_le_localP 2)).symm
end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic
