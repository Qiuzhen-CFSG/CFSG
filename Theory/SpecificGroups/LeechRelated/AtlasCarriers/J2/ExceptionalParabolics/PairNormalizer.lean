module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.QuotientSeed
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient

/-!
# The characteristic radical and full local quotient of the ATLAS J₂ carrier

The imported certificates prove `q₂ ≤ s`, relative characteristicity, both
orders 64 and 128, and the relative-normal-closure/core bridges. A concrete
subgroup `candidate` lies in the full normalizer and contains `s`.

The checked coset cover identifies `candidate` with the full normalizer;
the eighteen quotient representatives construct an actual isomorphism with
`S₃ × C₃`. Together these give order 1152 and odd index nine for `s`.
Relative normality then identifies the ambient images of the intrinsic cores
of `l₂` and `p₂`. Using the independent core-cardinality calculation for `l₂`,
the final theorem identifies the full normalizer's intrinsic core with `q₂`
and proves the required core order and quotient equivalence. Only that
`l₂` core-cardinality premise remains explicit; its PSL₂(2) quotient premise
is unnecessary for this bridge and belongs to the second-parabolic calculation.

Source: GLS3 Table 5.3g and Aschbacher--Smith, printed p.511 (PDF p.528).
The carrier, words, and kernel-checked witnesses are the actual degree-100
ATLAS `J2G1-p100B0` data, with attribution in the adjacent source directories.
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
open Seed Subgroup

theorem card_quotientModel : Nat.card QuotientModel = 18 := by
  simp [QuotientModel, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem card_candidate_of_quotient
    (hquot : Nonempty ((candidate ⧸ q₂.subgroupOf candidate) ≃* QuotientModel)) :
    Nat.card candidate = 1152 := by
  obtain ⟨e⟩ := hquot
  have hidx : (q₂.subgroupOf candidate).index = 18 :=
    (Nat.card_congr e.toEquiv).trans card_quotientModel
  have hq : Nat.card (q₂.subgroupOf candidate) = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe q₂_le_candidate).toEquiv).trans card_q₂
  have h := (q₂.subgroupOf candidate).card_mul_index
  rw [hq, hidx] at h
  exact h.symm

theorem p₂_quotient_of_coverage
    (hcover : p₂ ≤ candidate)
    (hquot : Nonempty ((candidate ⧸ q₂.subgroupOf candidate) ≃* QuotientModel)) :
    Nonempty ((p₂ ⧸ q₂.subgroupOf p₂) ≃* QuotientModel) := by
  obtain ⟨e⟩ := hquot
  let f : p₂ ≃* candidate := MulEquiv.subgroupCongr (le_antisymm hcover candidate_le_p₂)
  have hf : (q₂.subgroupOf p₂).map f.toMonoidHom = q₂.subgroupOf candidate := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨f.symm x, hx, f.apply_symm_apply x⟩
  exact ⟨(QuotientGroup.congr _ _ f hf).trans e⟩

theorem p₂_core_and_quotient_of_coverage
    (hcover : p₂ ≤ candidate)
    (hquot : Nonempty ((candidate ⧸ q₂.subgroupOf candidate) ≃* QuotientModel))
    (hLcore : Nat.card (pCore 2 l₂) = 64) :
    Nat.card (pCore 2 p₂) = 64 ∧
      Nonempty ((p₂ ⧸ pCore 2 p₂) ≃* QuotientModel) := by
  have heq : p₂ = candidate := le_antisymm hcover candidate_le_p₂
  have hP : Nat.card p₂ = 1152 :=
    (Nat.card_congr (MulEquiv.subgroupCongr heq).toEquiv).trans (card_candidate_of_quotient hquot)
  refine ⟨p₂_core_card_of_card hP hLcore, ?_⟩
  obtain ⟨e⟩ := p₂_quotient_of_coverage hcover hquot
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (p₂_core_eq_q₂_of_card s_le_p₂ hP hLcore)).trans e⟩

/-- The fixed generated candidate has order 1152, computed from its actual quotient. -/
theorem card_candidate : Nat.card candidate = 1152 :=
  card_candidate_of_quotient candidate_quotient_equiv

/-- The full normalizer of the fixed radical has order 1152. -/
theorem card_p₂ : Nat.card p₂ = 1152 := by
  rw [full_normalizer_eq_candidate]
  exact card_candidate

/-- The quotient by the fixed radical is the actual group S₃ × C₃. -/
theorem p₂_quotient_equiv : Nonempty ((p₂ ⧸ q₂.subgroupOf p₂) ≃* QuotientModel) :=
  p₂_quotient_of_coverage full_normalizer_le_candidate candidate_quotient_equiv

/-- The chosen two-subgroup has odd index nine in the full normalizer. -/
theorem s_relIndex_p₂ : s.relIndex p₂ = 9 :=
  s_relIndex_p₂_of_card s_le_p₂ card_p₂

/-- The relative normal closure and its full overgroup have the same ambient two-core. -/
theorem mapped_p₂_core_eq_l₂_core :
    (pCore 2 p₂).map p₂.subtype = (pCore 2 l₂).map l₂.subtype :=
  mapped_p₂_core_eq_l₂_core_of_card s_le_p₂ card_p₂

/-- The independent intrinsic core order identifies the radical inside `l₂`. -/
theorem l₂_core_eq_q₂ (hLcore : Nat.card (pCore 2 l₂) = 64) :
    pCore 2 l₂ = q₂.subgroupOf l₂ :=
  l₂_core_eq_q₂_of_card q₂_le_l₂ hLcore

/-- The same radical is the intrinsic two-core of the full normalizer. -/
theorem p₂_core_eq_q₂ (hLcore : Nat.card (pCore 2 l₂) = 64) :
    pCore 2 p₂ = q₂.subgroupOf p₂ :=
  p₂_core_eq_q₂_of_card s_le_p₂ card_p₂ hLcore

/-- The local core order and quotient, conditional only on the independent `l₂` core order.
In particular, no quotient hypothesis for `l₂`, coverage premise, or splitting is required. -/
theorem p₂_core_and_quotient (hLcore : Nat.card (pCore 2 l₂) = 64) :
    Nat.card (pCore 2 p₂) = 64 ∧
      Nonempty ((p₂ ⧸ pCore 2 p₂) ≃* QuotientModel) :=
  p₂_core_and_quotient_of_coverage
    full_normalizer_le_candidate candidate_quotient_equiv hLcore

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
