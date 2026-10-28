module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.QuotientData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.RelativeCore
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# A shared concrete candidate for the full Hall--Janko normalizer

The two odd words normalize each of the six radical generators, as certified
by explicit words in the radical enumeration. Together with `sGenerator 3`
and `q₂`, they define an actual subgroup of `Seed.p₂` containing `Seed.s`.
This publishes one common carrier for independent normalizer-coverage and
quotient calculations. No coverage or quotient structure is assumed here.
Source: GLS3 Table 5.3g; the signed ATLAS words are retained in
`source/quotient-seed.json` and transcribed by `source/quotient-seed.py`.
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
open Theory.GroupTheory GeneratorPair Seed QuotientData RadicalData
open GeneratorPair.SecondOrbitCertificate

/-- The actual local quotient requested by the source. -/
abbrev QuotientModel := Equiv.Perm (Fin 3) × Multiplicative (ZMod 3)

/-- Two fixed odd words for the local quotient calculation. -/
def oddGenerator (i : Fin 2) : Carrier := localWord (oddWord i)

private theorem inclusion_localWord (w : List (Fin 3)) :
    inclusion (localWord w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a, b, b⁻¹] i * localWord w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> simp [a, b, inclusion, generatorA_eq_table, generatorB_eq_table]

set_option maxRecDepth 100000 in
private theorem odd_word_check : ∀ i,
    evalWord ![tableA, tableB, tableB⁻¹] (oddWord i) = oddTable i := by
  apply allFin
  decide +kernel

theorem oddGenerator_inclusion (i : Fin 2) : inclusion (oddGenerator i) = oddTable i :=
  (inclusion_localWord (oddWord i)).trans (odd_word_check i)

set_option maxRecDepth 100000 in
private theorem odd_conj_check : ∀ i j,
    oddTable i * qGenTable j * (oddTable i)⁻¹ = qTable (oddConjIndex i j) := by
  apply allFin
  decide +kernel

theorem oddGenerator_conj_q₂Generator (i : Fin 2) (j : Fin 6) :
    oddGenerator i * q₂Generator j * (oddGenerator i)⁻¹ = qElement (oddConjIndex i j) := by
  apply inclusion_injective
  rw [map_mul, map_mul, map_inv, oddGenerator_inclusion, q₂Generator_inclusion,
    qElement_inclusion]
  exact odd_conj_check i j

/-- The fixed odd words normalize the literal Seed radical. -/
theorem oddGenerator_mem_p₂ (i : Fin 2) : oddGenerator i ∈ p₂ := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hle : q₂.map (MulAut.conj (oddGenerator i)).toMonoidHom ≤ q₂ := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    change oddGenerator i * q₂Generator j * (oddGenerator i)⁻¹ ∈ q₂
    rw [oddGenerator_conj_q₂Generator]
    exact qElement_mem _
  apply Subgroup.eq_of_le_of_card_ge hle
  exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj (oddGenerator i)).injective).symm

/-- The involution outside the radical, followed by the two fixed odd words. -/
def normalizerGenerator : Fin 3 → Carrier :=
  ![sGenerator 3, oddGenerator 0, oddGenerator 1]

theorem normalizerGenerator_mem_p₂ (i : Fin 3) : normalizerGenerator i ∈ p₂ := by
  fin_cases i
  · exact s_le_p₂ (Subgroup.subset_closure ⟨3, rfl⟩)
  · exact oddGenerator_mem_p₂ 0
  · exact oddGenerator_mem_p₂ 1

/-- A concrete generated subgroup whose full-normalizer coverage remains to be proved. -/
def candidate : Subgroup Carrier := q₂ ⊔ Subgroup.closure (Set.range normalizerGenerator)

theorem q₂_le_candidate : q₂ ≤ candidate := le_sup_left

theorem normalizerGenerator_mem_candidate (i : Fin 3) : normalizerGenerator i ∈ candidate :=
  (show Subgroup.closure (Set.range normalizerGenerator) ≤ candidate from le_sup_right)
    (Subgroup.subset_closure ⟨i, rfl⟩)

theorem candidate_le_p₂ : candidate ≤ p₂ := by
  apply sup_le q₂.le_normalizer
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact normalizerGenerator_mem_p₂ i

theorem s_le_candidate : s ≤ candidate := by
  intro x hx
  obtain ⟨i, rfl⟩ := exists_sElement hx
  unfold sElement
  split
  · exact q₂_le_candidate (qElement_mem _)
  · exact candidate.mul_mem (normalizerGenerator_mem_candidate 0)
      (q₂_le_candidate (qElement_mem _))

@[instance] theorem q₂_normal_in_candidate : (q₂.subgroupOf candidate).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer candidate_le_p₂

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
