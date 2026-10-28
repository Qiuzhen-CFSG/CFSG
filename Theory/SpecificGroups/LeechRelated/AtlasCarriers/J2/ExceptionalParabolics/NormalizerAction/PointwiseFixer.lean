module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction.Definitions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits

/-!
# The full automorphism pointwise fixer of the Hall--Janko radical

Every automorphism is realized by the checked degree-100 permutation extension.
Its two cosets, together with the eighteen inner-normalizer representatives,
reduce a radical fixer to 64 × 18 × 2 possibilities. Relative characteristicity
of the radical in the fixed two-subgroup ensures that the chosen outer
involution normalizes it. Positive-word induction proves the inner coset cover
from the existing representative multiplication table.

Commutation with the six radical generators, tested at points 0 and 1, excludes
all cosets outside the radical by kernel reduction. Faithful conjugation then
transfers the containment to the full automorphism group of the unchanged
ATLAS carrier. No simplicity or unproved fixer hypothesis is required.

Source: Aschbacher--Smith 15.3.42, final paragraph, printed p.1138;
GLS3 Table 5.3g. The permutation data are R. A. Wilson et al., ATLAS of
Finite Group Representations, `J2G1-p100B0`. Original data, attribution,
and rights are retained in `AtlasCarriers/source/`; this original proof
follows the repository's Apache 2.0 license.
-/

public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction
open Theory.GroupTheory Subgroup GeneratorPair Seed PairNormalizer
open PairNormalizer.RadicalData PairNormalizer.CandidateQuotient
open GeneratorPair.SecondOrbitCertificate
open scoped Pointwise

namespace PointwiseFixer

private def representative (i : Fin 18) : Carrier := evalWord normalizerGenerator (repWord i)

private theorem generator_inclusion (i : Fin 3) :
    inclusion (normalizerGenerator i) =
      ![SylowData.tTable, QuotientData.oddTable 0, QuotientData.oddTable 1] i := by
  fin_cases i
  · exact (sGenerator_inclusion 3).trans (by decide +kernel)
  · exact oddGenerator_inclusion 0
  · exact oddGenerator_inclusion 1

private theorem representative_inclusion (i : Fin 18) : inclusion (representative i) = repTable i := by
  have hw (w : List (Fin 3)) : inclusion (evalWord normalizerGenerator w) =
      evalWord ![SylowData.tTable, QuotientData.oddTable 0, QuotientData.oddTable 1] w := by
    induction w with
    | nil => exact map_one inclusion
    | cons j w ih => rw [evalWord, map_mul, generator_inclusion, ih, evalWord]
  exact hw (repWord i)

private theorem representative_mul (i j : Fin 18) :
    representative i * representative j =
      qElement (radicalFactor i j) * representative (mulIndex i j) := by
  apply inclusion_injective
  rw [map_mul, map_mul, representative_inclusion, representative_inclusion,
    representative_inclusion, qElement_inclusion]
  exact repTable_mul i j

/-- Positive-word induction lifts the eighteen checked quotient representatives. -/
private theorem normalizer_coverage {x : Carrier} (hx : x ∈ p₂) :
    ∃ q ∈ q₂, ∃ i : Fin 18, q * representative i = x := by
  rw [full_normalizer_eq_candidate] at hx
  have he : candidate = closure ((q₂ : Set Carrier) ∪ Set.range normalizerGenerator) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq]
    rfl
  rw [he] at hx
  change x ∈ (Subgroup.closure _).toSubmonoid at hx
  rw [closure_toSubmonoid_of_finite] at hx
  induction hx using Submonoid.closure_induction_left with
  | one => exact ⟨1, q₂.one_mem, 0, one_mul 1⟩
  | mul_left g hg y _ ih =>
    obtain ⟨q, hq, i, rfl⟩ := ih
    rcases hg with hg | ⟨j, rfl⟩
    · exact ⟨g * q, q₂.mul_mem hg hq, i, mul_assoc _ _ _⟩
    · let k : Fin 18 := ![9, 3, 1] j
      have hk : representative k = normalizerGenerator j := by
        fin_cases j <;> simp [k, representative, repWord]
      have hconj : normalizerGenerator j * q * (normalizerGenerator j)⁻¹ ∈ q₂ :=
        (mem_normalizer_iff.mp (normalizerGenerator_mem_p₂ j) q).mp hq
      refine ⟨(normalizerGenerator j * q * (normalizerGenerator j)⁻¹) *
        qElement (radicalFactor k i), q₂.mul_mem hconj (qElement_mem _), mulIndex k i, ?_⟩
      rw [mul_assoc, ← representative_mul, hk]
      group

private theorem extensionAction_into (g : Extension) (x : Carrier) :
    intoExtension (extensionAction g x) = g * intoExtension x * g⁻¹ := by
  apply extension.subtype_injective
  rfl

private theorem extensionAction_comp (g : Extension) :
    intoExtension.comp (extensionAction g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp intoExtension := by
  apply MonoidHom.ext
  intro x
  exact extensionAction_into g x

private theorem outerAction_map_s : s.map (extensionAction outerElement).toMonoidHom = s := by
  apply Subgroup.map_injective SecondParabolic.intoExtension_injective
  rw [Subgroup.map_map, extensionAction_comp, ← Subgroup.map_map]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp SecondParabolic.outerElement_normalizes_s

/-- Relative characteristicity in the fixed two-subgroup gives outer invariance. -/
private theorem outer_normalizes_radical :
    outerElement ∈ normalizer (q₂.map intoExtension : Set Extension) := by
  let e := extensionAction outerElement
  let f : MulAut s := (e.subgroupMap s).trans (MulEquiv.subgroupCongr outerAction_map_s)
  have hq := Subgroup.characteristic_iff_map_eq.mp q₂_characteristic f
  have hh := congrArg (Subgroup.map s.subtype) hq
  have hf : s.subtype.comp f.toMonoidHom = e.toMonoidHom.comp s.subtype := rfl
  rw [Subgroup.map_map, hf, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le q₂_le_s] at hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_map]
  change q₂.map ((MulAut.conj outerElement).toMonoidHom.comp intoExtension) = _
  rw [← extensionAction_comp, ← Subgroup.map_map, hh]

private theorem range_normalizes :
    (⊤ : Subgroup Extension) ≤ normalizer (intoExtension.range : Set Extension) := by
  apply le_normalizer_iff.mpr
  rintro g _ x ⟨y, rfl⟩
  exact ⟨extensionAction g y, extensionAction_into g y⟩

private theorem range_sup_outer : intoExtension.range ⊔ zpowers outerElement = ⊤ := by
  apply eq_of_le_of_card_ge le_top
  rw [card_sup_zpowers_of_normalizing_involution _ _ SecondParabolic.outerElement_sq
    SecondParabolic.outerElement_not_mem_range (range_normalizes (mem_top _))]
  have hc : Nat.card extension = 2 * Nat.card generated :=
    card_sup_zpowers_of_normalizing_involution _ _
      (by simpa only [pow_two] using involution_mul_self)
      involution_not_mem_generated involution_mem_normalizer
  rw [MonoidHom.range_eq_map, card_map_of_injective SecondParabolic.intoExtension_injective]
  simpa using le_of_eq hc

/-- The chosen odd involution represents the nonidentity coset of the carrier. -/
private theorem extension_cosets (x : Extension) :
    ∃ g : Carrier, x = intoExtension g ∨ x = intoExtension g * outerElement := by
  have hx : x ∈ (intoExtension.range : Set Extension) * (zpowers outerElement : Set Extension) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      (zpowers_le.mpr (range_normalizes (mem_top _))), range_sup_outer]
    trivial
  obtain ⟨_, ⟨g, rfl⟩, t, ht, rfl⟩ := hx
  refine ⟨g, ?_⟩
  have hne : outerElement ≠ 1 := fun h =>
    SecondParabolic.outerElement_not_mem_range (h ▸ intoExtension.range.one_mem)
  have ho : orderOf outerElement = 2 := orderOf_eq_prime SecondParabolic.outerElement_sq hne
  change t ∈ zpowers outerElement at ht
  rw [(isOfFinOrder_of_finite outerElement).mem_zpowers_iff_mem_range_orderOf, ho] at ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

private theorem normalizer_pullback {g : Carrier}
    (h : intoExtension g ∈ normalizer (q₂.map intoExtension : Set Extension)) : g ∈ p₂ := by
  have h' := le_normalizer_comap intoExtension h
  rwa [comap_map_eq_self_of_injective SecondParabolic.intoExtension_injective] at h'

set_option maxRecDepth 100000 in
/-- Two coordinates of the six commutation equations exclude every coset outside q₂. -/
private theorem fixer_check : ∀ i : Fin 64, ∀ j : Fin 18, ∀ b : Bool,
    (∀ k : Fin 6,
      let p := qTable i * repTable j * (if b then SecondParabolic.outerTable else 1)
      (p * qGenTable k) 0 = (qGenTable k * p) 0 ∧
      (p * qGenTable k) 1 = (qGenTable k * p) 1) →
    j = 0 ∧ b = false := by
  apply allFin
  decide +kernel

private theorem extension_fixer_le : centralizer (q₂.map intoExtension : Set Extension) ≤
    q₂.map intoExtension := by
  intro x hx
  have hn := centralizer_le_normalizer _ hx
  obtain ⟨g, b, hg⟩ : ∃ g : Carrier, ∃ b : Bool,
      x = intoExtension g * (if b then outerElement else 1) := by
    obtain ⟨g, hg | hg⟩ := extension_cosets x
    · exact ⟨g, false, by simpa using hg⟩
    · exact ⟨g, true, hg⟩
  have hb : (if b then outerElement else 1) ∈ normalizer (q₂.map intoExtension : Set Extension) := by
    cases b
    · exact one_mem _
    · exact outer_normalizes_radical
  have hp : g ∈ p₂ := by
    apply normalizer_pullback
    have hh := (normalizer (q₂.map intoExtension : Set Extension)).mul_mem hn
      ((normalizer _).inv_mem hb)
    simpa only [hg, mul_inv_cancel_right] using hh
  obtain ⟨q, hq, j, hj⟩ := normalizer_coverage hp
  obtain ⟨i, hi⟩ := exists_qElement hq
  have hx' : x = intoExtension (qElement i * representative j) *
      (if b then outerElement else 1) := by
    rw [hg, ← hj, ← hi]
  have ht : extension.subtype x = qTable i * repTable j *
      (if b then SecondParabolic.outerTable else 1) := by
    rw [hx', map_mul]
    change inclusion (qElement i * representative j) *
      extension.subtype (if b then outerElement else 1) = _
    rw [map_mul, qElement_inclusion, representative_inclusion]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
      map_one, SecondParabolic.outerElement_inclusion]
  obtain ⟨hj0, hb0⟩ := fixer_check i j b (by
    intro k
    have hc := mem_centralizer_iff.mp hx (intoExtension (q₂Generator k))
      (mem_map_of_mem intoExtension (subset_closure ⟨k, rfl⟩))
    have he := congrArg extension.subtype hc.symm
    simp only [map_mul] at he
    change extension.subtype x * inclusion (q₂Generator k) =
      inclusion (q₂Generator k) * extension.subtype x at he
    rw [ht, q₂Generator_inclusion] at he
    exact ⟨congrArg (fun p : Equiv.Perm (Fin 100) => p 0) he,
      congrArg (fun p : Equiv.Perm (Fin 100) => p 1) he⟩)
  subst j b
  have he : x = intoExtension (qElement i) := by simpa [representative, repWord] using hx'
  rw [he]
  exact mem_map_of_mem intoExtension (qElement_mem i)

end PointwiseFixer

/-- The full automorphism centralizer of the actual inner radical lies in that radical. -/
theorem radical_centralizer_le : centralizer (innerRadical : Set (MulAut Carrier)) ≤
    innerRadical := by
  intro f hf
  obtain ⟨x, rfl⟩ := extensionAction_surjective_of_pair_calculations
    first_generator_conjugate second_generator_orbits f
  have hx : x ∈ centralizer (q₂.map intoExtension : Set Extension) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨q, hq, rfl⟩
    apply extensionAction_injective
    simpa only [map_mul, extensionAction_inner] using
      mem_centralizer_iff.mp hf (MulAut.conj q) (mem_map_of_mem MulAut.conj hq)
  obtain ⟨q, hq, hqx⟩ := PointwiseFixer.extension_fixer_le hx
  rw [← hqx, extensionAction_inner]
  exact mem_map_of_mem MulAut.conj hq

end Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction
