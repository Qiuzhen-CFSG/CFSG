module
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.Coverage
public import Theory.GroupTheory.FourGroupNormalizerOvergroup
public import Theory.Mathieu.M24.Properties.Order

/-!
# Three normal four-group rows in the M₂₄ Sylow catalogue

The exhaustive normal elementary catalogue has 22 rows, but only rows 1, 2,
and 3 can have order four. Row 0 has order at most two. In every row of index
at least four, five explicit distinct products of the generators give a lower
bound of five. All finite index identities are checked by the Lean kernel.

Restrict a normal four-group to the marked Sylow carrier and apply the
catalogue. Sylow conjugacy then reduces the normalizer-overgroup criterion to
strict characteristic-two overgroups for those three concrete ambient rows.
Those three normalizer calculations remain explicit inputs; neither the
catalogue nor the order calculation asserts them.

Source context: Aschbacher--Smith, combined manuscript (1 March 2004), the
sporadic paragraph of 15.3.43, printed p.1140, and GLS3, Table 5.3e.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.FourNormalizers
open Subgroup SylowNormalizer OrderEnumeration EvenCatalogue EvenCatalogue.Coverage

private def fiveIndex (i : Fin 22) : Fin 5 → Fin 1024 :=
  ![0, generatorIndex i 0, generatorIndex i 1, generatorIndex i 2,
    multiply (generatorIndex i 0) (generatorIndex i 1)]

private theorem fiveIndex_injective : ∀ i : Fin 22, 4 ≤ i.val →
    Function.Injective (fiveIndex i) := by decide +kernel

private theorem five_mem (i : Fin 22) (j : Fin 5) :
    element (fiveIndex i j) ∈ subgroup i := by
  fin_cases j
  · exact element_zero ▸ (subgroup i).one_mem
  · exact generator_mem i 0
  · exact generator_mem i 1
  · exact generator_mem i 2
  · change element (multiply (generatorIndex i 0) (generatorIndex i 1)) ∈ subgroup i
    rw [element_multiply]
    exact (subgroup i).mul_mem (generator_mem i 0) (generator_mem i 1)

private theorem large_rows_card (i : Fin 22) (hi : 4 ≤ i.val) :
    5 ≤ Nat.card (subgroup i) := by
  let f : Fin 5 → subgroup i := fun j => ⟨element (fiveIndex i j), five_mem i j⟩
  have hf : Function.Injective f := by
    intro j k hjk
    exact fiveIndex_injective i hi (element_injective (congrArg Subtype.val hjk))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

private theorem row_zero_card_le_two : Nat.card (subgroup 0) ≤ 2 := by
  have hle : subgroup 0 ≤ zpowers (element 106) := by
    apply subgroup_le
    intro a
    fin_cases a
    · exact mem_zpowers _
    all_goals exact element_zero ▸ (zpowers (element 106)).one_mem
  have hp : (element 106) ^ 2 = 1 := by
    rw [pow_two, ← element_multiply,
      show multiply 106 106 = 0 by decide +kernel, element_zero]
  have hc : Nat.card (zpowers (element 106)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hp)
  exact (Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)).trans hc

/-- Only three rows of the exhaustive normal elementary catalogue can have
order four. Row numbers are zero-based, exactly as in `EvenCatalogue`. -/
theorem row_of_card_four (i : Fin 22) (hc : Nat.card (subgroup i) = 4) :
    i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi : i.val < 4 := by
    by_contra hn
    have := large_rows_card i (by omega)
    omega
  have hn : i ≠ 0 := by
    intro he
    rw [he] at hc
    have := row_zero_card_le_two
    omega
  have hn0 : i.val ≠ 0 := by
    intro hv
    exact hn (Fin.ext hv)
  have : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases this with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- Exhaustive intrinsic coverage of the normal four-groups in the marked
Sylow carrier, obtained from the checked elementary catalogue. -/
theorem normal_four_eq_row (R : Subgroup candidate) (hn : R.Normal)
    (hR : IsElementaryAbelian 2 R) (hc : Nat.card R = 4) :
    ∃ i : Fin 22, (i = 1 ∨ i = 2 ∨ i = 3) ∧ R = subgroup i := by
  have hne : R ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hc
    omega
  let : IsElementaryAbelian 2 R := hR
  obtain ⟨i, hi⟩ := catalogue_of_normal_exponent_two R hne hn (by
    intro x hx
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx)
  exact ⟨i, row_of_card_four i (hi ▸ hc), hi⟩

/-- The remaining native M₂₄ geometry consists of only three strict
normalizer enlargements. The exhaustive Sylow and order-four reductions are
already discharged here. -/
theorem fourNormalizerOvergroups_of_rows
    (h : ∀ i : Fin 22, i = 1 ∨ i = 2 ∨ i = 3 →
      ∃ D : Subgroup M24, normalizer (ambient i : Set M24) < D ∧
        Theory.GroupTheory.generalizedFitting D = pCore 2 D) :
    Theory.GroupTheory.FourNormalizerOvergroups M24 := by
  have hs : Nat.card candidate = 2 ^ (Nat.card M24).factorization 2 := by
    rw [candidate_card, m24_order]
    decide +kernel
  let P : Sylow 2 M24 := Sylow.ofCard candidate hs
  apply Theory.GroupTheory.FourNormalizerOvergroups.of_fixed_sylow P
  intro V hVP hPV hV hc
  have hVC : V ≤ candidate := hVP
  have hn : (V.subgroupOf candidate).Normal :=
    normal_subgroupOf_of_le_normalizer hPV
  let : IsElementaryAbelian 2 V := hV
  have he : IsElementaryAbelian 2 (V.subgroupOf candidate) :=
    IsElementaryAbelian.subgroupOf hVC
  have hcard : Nat.card (V.subgroupOf candidate) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv).trans hc
  obtain ⟨i, hi, hR⟩ := normal_four_eq_row (V.subgroupOf candidate) hn he hcard
  have hv : V = ambient i := by
    have hm := congrArg (Subgroup.map candidate.subtype) hR
    rw [map_subgroupOf_eq_of_le hVC] at hm
    exact hm
  rw [hv]
  exact h i hi

end Sporadic.Mathieu.M24LocalGeometry.FourNormalizers
