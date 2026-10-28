module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J2.EvenSetup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Exhaustive Sylow-local coverage for the concrete Hall–Janko group

A maximal two-local containing the fixed Sylow two-subgroup is the normalizer
of a nontrivial normal elementary abelian subgroup of that Sylow group.
The certified 128-element enumeration leaves exactly two possibilities:
the central involution line and the four-group on rows 0, 6, 5 and 26.

The first normalizer is `Seed.l₁`. For the four-group, the existing 525-coset
cover by the radical normalizer supplies the ambient exhaustion: each of the
524 other representatives moves a four-group element outside the four-group.
Its full normalizer is therefore `Seed.p₂`, not the relative normal closure
`Seed.l₂`. All checks use the original degree-100 ATLAS carrier and kernel
reduction. No simplicity, abstract-model identification or catalogue premise
is required.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed p.4 (Theorem 0.1.1(5),
printed p.482 in volume II); GLS3, Table 5.3g. The permutation tables and
coset witnesses are reused from the attributed ATLAS J2G1-p100B0 calculations
in `PairNormalizer.SylowOrder` and `PairNormalizer.NormalizerCoverage`.
-/

open Subgroup hiding inclusion inclusion_injective
open Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open GeneratorPair Seed PairNormalizer SylowData
open GeneratorPair.SecondOrbitCertificate

set_option maxRecDepth 100000

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J2Even.LocalCover

def fourIndex : Fin 4 → Fin 128 := ![0, 6, 5, 26]
def fourElement (i : Fin 4) : Carrier := sElement (fourIndex i)
def fourTable (i : Fin 4) : Equiv.Perm (Fin 100) := sTable (fourIndex i)

theorem fourElement_inclusion (i : Fin 4) : inclusion (fourElement i) = fourTable i :=
  sElement_inclusion _

def fourMul : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

private theorem four_mul_check : ∀ i j, fourTable i * fourTable j = fourTable (fourMul i j) := by
  apply allFin
  decide +kernel

private theorem four_sq_check : ∀ i, fourTable i * fourTable i = 1 := by
  apply allFin
  decide +kernel

theorem four_mul (i j : Fin 4) : fourElement i * fourElement j = fourElement (fourMul i j) := by
  apply inclusion_injective
  rw [map_mul, fourElement_inclusion, fourElement_inclusion, fourElement_inclusion]
  exact four_mul_check i j

theorem four_sq (i : Fin 4) : fourElement i * fourElement i = 1 := by
  apply inclusion_injective
  rw [map_mul, map_one, fourElement_inclusion]
  exact four_sq_check i

/-- The four explicitly listed elements form an actual subgroup of the carrier. -/
def four : Subgroup Carrier where
  carrier := Set.range fourElement
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨fourMul i j, (four_mul i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i, (eq_inv_iff_mul_eq_one.mpr (four_sq i))⟩

private theorem six_check : sTable 6 = FirstFusion.tPerm := by decide +kernel

theorem four_one : fourElement 1 = z := by
  apply inclusion_injective
  rw [fourElement_inclusion]
  exact six_check.trans FirstFusion.inclusion_t.symm

private theorem conjugation_check :
    sGenTable 3 * fourTable 2 * (sGenTable 3)⁻¹ = fourTable 3 ∧
    sGenTable 3 * fourTable 3 * (sGenTable 3)⁻¹ = fourTable 2 := by
  decide +kernel

theorem conjugation_two : sGenerator 3 * fourElement 2 * (sGenerator 3)⁻¹ = fourElement 3 := by
  apply inclusion_injective
  rw [map_mul, map_mul, map_inv, sGenerator_inclusion, fourElement_inclusion, fourElement_inclusion]
  exact conjugation_check.1

theorem conjugation_three : sGenerator 3 * fourElement 3 * (sGenerator 3)⁻¹ = fourElement 2 := by
  apply inclusion_injective
  rw [map_mul, map_mul, map_inv, sGenerator_inclusion, fourElement_inclusion, fourElement_inclusion]
  exact conjugation_check.2

private theorem rejection_check : ∀ i : Fin 128,
    ((sTable i * sTable i) 0 = 0 ∧ (sTable i * sTable i) 1 = 1) →
    (∀ j : Fin 7,
      (sTable i * (sGenTable j * sTable i * (sGenTable j)⁻¹)) 0 =
        ((sGenTable j * sTable i * (sGenTable j)⁻¹) * sTable i) 0 ∧
      (sTable i * (sGenTable j * sTable i * (sGenTable j)⁻¹)) 1 =
        ((sGenTable j * sTable i * (sGenTable j)⁻¹) * sTable i) 1) →
    i = 0 ∨ i = 6 ∨ i = 5 ∨ i = 26 := by
  apply allFin
  decide +kernel

/-- Squaring and commutation with conjugates leave only four Sylow rows. -/
theorem normal_elementary_le_four (H : Subgroup Carrier) (hHS : H ≤ s)
    (hn : ∀ x ∈ H, ∀ g ∈ s, g * x * g⁻¹ ∈ H)
    (he : IsElementaryAbelian 2 H) : H ≤ four := by
  let := he
  intro x hx
  obtain ⟨i, rfl⟩ := exists_sElement (hHS hx)
  have hs : sTable i * sTable i = 1 := by
    have hh := congrArg inclusion (elemPow_eq_one_of_isElementaryAbelian (p := 2) (sElement i) hx)
    simpa only [map_pow, map_mul, map_one, sElement_inclusion, pow_two] using hh
  have hc (j : Fin 7) : sTable i * (sGenTable j * sTable i * (sGenTable j)⁻¹) =
      (sGenTable j * sTable i * (sGenTable j)⁻¹) * sTable i := by
    have hh := congrArg inclusion (setLike_mul_comm hx
      (hn _ hx _ (subset_closure ⟨j, rfl⟩)))
    simpa only [map_mul, map_inv, sElement_inclusion, sGenerator_inclusion] using hh
  rcases rejection_check i
    ⟨congrArg (fun f : Equiv.Perm (Fin 100) => f 0) hs,
      congrArg (fun f : Equiv.Perm (Fin 100) => f 1) hs⟩
    (fun j => ⟨congrArg (fun f : Equiv.Perm (Fin 100) => f 0) (hc j),
      congrArg (fun f : Equiv.Perm (Fin 100) => f 1) (hc j)⟩) with hi | hi | hi | hi
  · exact ⟨0, hi ▸ rfl⟩
  · exact ⟨1, hi ▸ rfl⟩
  · exact ⟨2, hi ▸ rfl⟩
  · exact ⟨3, hi ▸ rfl⟩

/-- The two nontrivial normal elementary subgroups of the fixed Sylow group. -/
theorem normal_elementary_catalogue (R : Subgroup s) (hR : R ≠ ⊥)
    (hn : R.Normal) (he : IsElementaryAbelian 2 R) :
    R.map s.subtype = zpowers z ∨ R.map s.subtype = four := by
  let H := R.map s.subtype
  let := he
  have hH : H ≠ ⊥ := fun h => hR ((map_eq_bot_iff_of_injective R s.subtype_injective).mp h)
  have hnormal : ∀ x ∈ H, ∀ g ∈ s, g * x * g⁻¹ ∈ H := by
    intro x hx g hg
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨g, hg⟩ * y * (⟨g, hg⟩ : s)⁻¹, hn.conj_mem y hy ⟨g, hg⟩, rfl⟩
  have hsmall : H ≤ four := normal_elementary_le_four H (map_subtype_le R) hnormal
    IsElementaryAbelian.map_subtype
  have h23 : fourElement 2 ∈ H ↔ fourElement 3 ∈ H := by
    constructor
    · intro h
      rw [← conjugation_two]
      exact hnormal _ h _ (subset_closure ⟨3, rfl⟩)
    · intro h
      rw [← conjugation_three]
      exact hnormal _ h _ (subset_closure ⟨3, rfl⟩)
  by_cases h2 : fourElement 2 ∈ H
  · right
    have h3 := h23.mp h2
    have h1 : fourElement 1 ∈ H := (four_mul 2 3) ▸ H.mul_mem h2 h3
    apply le_antisymm hsmall
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact H.one_mem
    · exact h1
    · exact h2
    · exact h3
  · left
    have hle : H ≤ zpowers z := by
      intro x hx
      obtain ⟨i, rfl⟩ := hsmall hx
      fin_cases i
      · exact (zpowers z).one_mem
      · change fourElement 1 ∈ zpowers z
        rw [four_one]; exact mem_zpowers z
      · exact (h2 hx).elim
      · exact (h2 (h23.mpr hx)).elim
    apply le_antisymm hle
    apply zpowers_le.mpr
    obtain ⟨x, hx, hx1⟩ := H.bot_or_exists_ne_one.resolve_left hH
    obtain ⟨i, rfl⟩ := hsmall hx
    fin_cases i
    · exact (hx1 rfl).elim
    · exact four_one ▸ hx
    · exact (h2 hx).elim
    · exact (h2 (h23.mpr hx)).elim



private theorem radical_conj_check : ∀ j : Fin 6, ∀ i : Fin 4,
    RadicalData.qGenTable j * fourTable i * (RadicalData.qGenTable j)⁻¹ = fourTable i := by
  apply allFin
  decide +kernel

private def normalizerTable : Fin 3 → Equiv.Perm (Fin 100) :=
  ![sGenTable 3, QuotientData.oddTable 0, QuotientData.oddTable 1]

private def normalizerAction : Fin 3 → Fin 4 → Fin 4 :=
  ![![0, 1, 3, 2], ![0, 3, 1, 2], ![0, 1, 2, 3]]

private theorem normalizerGenerator_inclusion (j : Fin 3) :
    inclusion (normalizerGenerator j) = normalizerTable j := by
  fin_cases j
  · exact sGenerator_inclusion 3
  · exact oddGenerator_inclusion 0
  · exact oddGenerator_inclusion 1

private theorem normalizer_conj_check : ∀ j : Fin 3, ∀ i : Fin 4,
    normalizerTable j * fourTable i * (normalizerTable j)⁻¹ =
      fourTable (normalizerAction j i) := by
  apply allFin
  decide +kernel

private theorem mem_normalizer_four (g : Carrier)
    (h : ∀ i : Fin 4, ∃ j : Fin 4, g * fourElement i * g⁻¹ = fourElement j) :
    g ∈ normalizer (four : Set Carrier) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hle : four.map (MulAut.conj g).toMonoidHom ≤ four := by
    rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := h i
    exact ⟨j, hj.symm⟩
  exact eq_of_le_of_card_ge hle
    (le_of_eq (card_map_of_injective (MulAut.conj g).injective).symm)

/-- The already constructed radical normalizer preserves the explicit four-group. -/
theorem candidate_le_normalizer_four : candidate ≤ normalizer (four : Set Carrier) := by
  apply sup_le
  · apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    apply mem_normalizer_four
    intro i
    refine ⟨i, inclusion_injective ?_⟩
    rw [map_mul, map_mul, map_inv, q₂Generator_inclusion, fourElement_inclusion]
    exact radical_conj_check j i
  · apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    apply mem_normalizer_four
    intro i
    refine ⟨normalizerAction j i, inclusion_injective ?_⟩
    rw [map_mul, map_mul, map_inv, normalizerGenerator_inclusion,
      fourElement_inclusion, fourElement_inclusion]
    exact normalizer_conj_check j i

private theorem four_separation_check : ∀ i : Fin 525, i ≠ 0 →
    ∃ j : Fin 4, ∀ k : Fin 4,
    NormalizerCoverage.fingerprint (fun p => NormalizerCoverage.Data.reprMap i (fourTable j p)) ≠
      NormalizerCoverage.fingerprint (fun p => fourTable k (NormalizerCoverage.Data.reprMap i p)) := by
  apply allFin
  decide +kernel

private theorem repr_index_zero_of_normalizes_four (i : Fin 525)
    (hi : NormalizerCoverage.repr i ∈ normalizer (four : Set Carrier)) : i = 0 := by
  by_contra hn
  obtain ⟨j, hj⟩ := four_separation_check i hn
  have hc : NormalizerCoverage.repr i * fourElement j *
      (NormalizerCoverage.repr i)⁻¹ ∈ four :=
    ((mem_normalizer_iff.mp hi) _).mp ⟨j, rfl⟩
  obtain ⟨k, hk⟩ := hc
  have he : NormalizerCoverage.repr i * fourElement j =
      fourElement k * NormalizerCoverage.repr i := by
    rw [hk]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  apply hj k
  apply congrArg NormalizerCoverage.fingerprint
  funext p
  have hh := congrArg (fun x : Carrier => inclusion x p) he
  simpa only [map_mul, Equiv.Perm.mul_apply, fourElement_inclusion,
    NormalizerCoverage.repr_spec] using hh

/-- The full ambient normalizer of the four-group is the full radical normalizer. -/
theorem normalizer_four : normalizer (four : Set Carrier) = p₂ := by
  rw [full_normalizer_eq_candidate]
  apply le_antisymm _ candidate_le_normalizer_four
  intro x hx
  obtain ⟨h, i, he⟩ := NormalizerCoverage.covers x
  have hr : NormalizerCoverage.repr i ∈ normalizer (four : Set Carrier) := by
    have hm := (normalizer (four : Set Carrier)).mul_mem
      ((normalizer (four : Set Carrier)).inv_mem (candidate_le_normalizer_four h.property)) hx
    simpa only [he, inv_mul_cancel_left] using hm
  have hi := repr_index_zero_of_normalizes_four i hr
  simpa only [he, hi, NormalizerCoverage.repr_zero, mul_one] using h.property

end CFSG.Quasithin.MainConverse.SporadicLocal.J2Even.LocalCover

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J2Even

/-- Every maximal two-local containing the fixed Sylow subgroup is one of the two
actual Seed normalizers. -/
public theorem sylowLocalCover : SylowLocalCover := by
  intro M hM hSM
  obtain ⟨R, hR, hn, he, hMR⟩ :=
    exists_normal_elementary_normalizer_of_sylow_le sylowTwo hM hSM
  change M = normalizer (R.map s.subtype : Set Carrier) at hMR
  rcases LocalCover.normal_elementary_catalogue R hR hn he with h | h
  · left
    rw [h, normalizer_zpowers_eq_centralizer_of_order_two z
      (orderOf_eq_prime z_sq z_ne_one)] at hMR
    exact ⟨MulEquiv.subgroupCongr hMR⟩
  · right
    rw [h, LocalCover.normalizer_four] at hMR
    exact ⟨MulEquiv.subgroupCongr hMR⟩

end CFSG.Quasithin.MainConverse.SporadicLocal.J2Even
