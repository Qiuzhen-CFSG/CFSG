module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction.RadicalAction
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Coverage of normal elementary four-groups in the fixed Hall–Janko Sylow

Normality makes every element commute with its Sylow-generator conjugates.
The checked involution test therefore puts an elementary normal subgroup
inside the embedded radical center. At order four it equals that center.
The existing 525-coset cover then proves that its full normalizer is contained
in the radical normalizer. Relative normality is throughout inside Seed.s.

Source: GLS3 Table 5.3g and the sporadic inspection in Aschbacher–Smith
15.3.43, printed p.1140. The actual group and tables are ATLAS J2G1-p100B0.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RankOneFourNormalizer
open Theory.GroupTheory ExceptionalParabolics GeneratorPair Seed PairNormalizer Subgroup
open PairNormalizer.RadicalData PairNormalizer.SylowData Checks

def four : Subgroup Carrier := (center q₂).map q₂.subtype

def fourElement (i : Fin 4) : Carrier := qElement (fourIndex i)

theorem fourElement_mem (i : Fin 4) : fourElement i ∈ four := by
  refine ⟨⟨fourElement i, qElement_mem _⟩, mem_center_iff.mpr ?_, rfl⟩
  intro y
  apply Subtype.ext
  have h : q₂ ≤ centralizer ({fourElement i} : Set Carrier) := by
    apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply inclusion_injective
    rw [map_mul, map_mul, q₂Generator_inclusion]
    change qGenTable j * inclusion (qElement (fourIndex i)) = _
    rw [qElement_inclusion]
    simpa only [fourElement, qElement_inclusion] using four_central_check i j
  exact mem_centralizer_singleton_iff.mp (h y.property)

theorem fourElement_injective : Function.Injective fourElement := by
  intro i j hij
  have h := qElement_injective hij
  exact (by decide : Function.Injective fourIndex) h

theorem card_four : Nat.card four = 4 := by
  have hu : Nat.card four ≤ 4 := by
    rw [four, card_map_of_injective q₂.subtype_injective]
    exact NormalizerAction.card_center_q₂_le
  have hl := Nat.card_le_card_of_injective
    (fun i : Fin 4 => (⟨fourElement i, fourElement_mem i⟩ : four))
    (fun _ _ h => fourElement_injective (congrArg Subtype.val h))
  exact le_antisymm hu (by simpa using hl)

theorem exists_fourElement {x : Carrier} (hx : x ∈ four) :
    ∃ i : Fin 4, fourElement i = x := by
  let f : Fin 4 → four := fun i => ⟨fourElement i, fourElement_mem i⟩
  have hi : Function.Injective f := fun _ _ h => fourElement_injective (congrArg Subtype.val h)
  have hs := (hi.bijective_of_nat_card_le (by simp only [card_four, Nat.card_fin, le_refl])).2
  obtain ⟨i, hi⟩ := hs ⟨x, hx⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem normal_elementary_le_four (W : Subgroup Carrier) (hWs : W ≤ s)
    (hWn : (W.subgroupOf s).Normal) (hWe : IsElementaryAbelian 2 W) : W ≤ four := by
  let := hWe
  intro x hx
  obtain ⟨i, hi⟩ := exists_sElement (hWs hx)
  have hs : inclusion x * inclusion x = 1 := by
    rw [← map_mul, ← pow_two, elemPow_eq_one_of_isElementaryAbelian x hx, map_one]
  rw [← hi, sElement_inclusion] at hs
  have hc (j : Fin 7) :
      let c := sGenTable j * sTable i * (sGenTable j)⁻¹
      (sTable i * c) 0 = (c * sTable i) 0 ∧
      (sTable i * c) 1 = (c * sTable i) 1 := by
    have hg : sGenerator j ∈ s := subset_closure ⟨j, rfl⟩
    have hm : sGenerator j * x * (sGenerator j)⁻¹ ∈ W :=
      (normal_subgroupOf_iff hWs).mp hWn x (sGenerator j) hx hg
    have hh := congrArg (fun y : W => inclusion (y : Carrier))
      (mul_comm' (⟨x, hx⟩ : W) ⟨_, hm⟩)
    change inclusion (x * (sGenerator j * x * (sGenerator j)⁻¹)) =
      inclusion ((sGenerator j * x * (sGenerator j)⁻¹) * x) at hh
    simp only [← hi, map_mul, map_inv, sElement_inclusion, sGenerator_inclusion] at hh
    exact ⟨congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hh,
      congrArg (fun p : Equiv.Perm (Fin 100) => p 1) hh⟩
  have hk := normal_element_check i
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hs)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 1) hs) hc
  rw [← hi]
  rcases hk with rfl | rfl | rfl | rfl
  · exact fourElement_mem 0
  · exact fourElement_mem 1
  · exact fourElement_mem 2
  · exact fourElement_mem 3

theorem normal_four_eq (W : Subgroup Carrier) (hWs : W ≤ s)
    (hWn : (W.subgroupOf s).Normal) (hWe : IsElementaryAbelian 2 W)
    (hW4 : Nat.card W = 4) : W = four :=
  eq_of_le_of_card_ge (normal_elementary_le_four W hWs hWn hWe)
    (by rw [card_four, hW4])

theorem p₂_le_normalizer_four : p₂ ≤ normalizer (four : Set Carrier) :=
  normalizer_le_normalizer_characteristic_image q₂ (center q₂)

open PairNormalizer.NormalizerCoverage in
theorem normalizer_four_le_p₂ : normalizer (four : Set Carrier) ≤ p₂ := by
  intro x hx
  obtain ⟨h, i, he⟩ := NormalizerCoverage.covers x
  have hr : NormalizerCoverage.repr i ∈ normalizer (four : Set Carrier) := by
    have hm := (normalizer (four : Set Carrier)).mul_mem
      ((normalizer _).inv_mem (p₂_le_normalizer_four (candidate_le_p₂ h.property))) hx
    simpa only [he, inv_mul_cancel_left] using hm
  have hi : i = 0 := by
    by_contra hn
    obtain ⟨j, hj⟩ := four_separation_check i hn
    have hc := ((mem_normalizer_iff.mp hr) (fourElement j)).mp (fourElement_mem j)
    obtain ⟨k, hk⟩ := exists_fourElement hc
    have hh : NormalizerCoverage.repr i * fourElement j =
        fourElement k * NormalizerCoverage.repr i := by
      rw [hk]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    apply hj k
    apply congrArg fingerprint
    funext p
    have hh' := congrArg (fun x : Carrier => inclusion x p) hh
    simpa only [fourElement, map_mul, Equiv.Perm.mul_apply, repr_spec,
      qElement_inclusion] using hh'
  subst i
  simpa only [he, repr_zero, mul_one] using candidate_le_p₂ h.property

theorem normal_four_normalizer_le (W : Subgroup Carrier) (hWs : W ≤ s)
    (hWn : (W.subgroupOf s).Normal) (hWe : IsElementaryAbelian 2 W)
    (hW4 : Nat.card W = 4) : normalizer (W : Set Carrier) ≤ p₂ := by
  rw [normal_four_eq W hWs hWn hWe hW4]
  exact normalizer_four_le_p₂

end Sporadic.LeechRelated.J2.RankOneFourNormalizer
