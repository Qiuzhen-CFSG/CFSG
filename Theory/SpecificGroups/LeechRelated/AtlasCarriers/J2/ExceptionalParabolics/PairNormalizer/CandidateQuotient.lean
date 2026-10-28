module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.QuotientSeed
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient.Checks
import Mathlib.Tactic.FinCases

/-!
# The concrete Hall--Janko candidate quotient is S₃ × C₃

The eighteen words t^b u^i v^j in the fixed normalizer generators define a
map from `Equiv.Perm (Fin 3) × Multiplicative (ZMod 3)` to the quotient of
`candidate` by the relative radical `Seed.q₂.subgroupOf candidate`.
The checked product table makes it a homomorphism. Separation from the
64 radical elements proves that its kernel is trivial; the definition of
`candidate` proves surjectivity. Inverting this map gives the requested
multiplicative equivalence without any splitting or normalizer-coverage premise.

The degree-100 ATLAS carrier and Seed generators are unchanged. The two odd
words come from `PairNormalizer/source/quotient-seed.json`; the finite
multiplication witnesses can be regenerated with
`CandidateQuotient/source/generate.py` and are checked by Lean's kernel.
Source: GLS3 Table 5.3g and Aschbacher--Smith, printed p.511 (PDF p.528).
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
open Theory.GroupTheory GeneratorPair Seed RadicalData
open GeneratorPair.SecondOrbitCertificate
namespace CandidateQuotient

private def representative (i : Fin 18) : Carrier :=
  evalWord normalizerGenerator (repWord i)

private theorem representative_mem (i : Fin 18) : representative i ∈ candidate := by
  have hw (w : List (Fin 3)) : evalWord normalizerGenerator w ∈ candidate := by
    induction w with
    | nil => exact candidate.one_mem
    | cons j w ih => exact candidate.mul_mem (normalizerGenerator_mem_candidate j) ih
  exact hw (repWord i)

private theorem generator_inclusion (i : Fin 3) :
    inclusion (normalizerGenerator i) =
      ![SylowData.tTable, QuotientData.oddTable 0, QuotientData.oddTable 1] i := by
  fin_cases i
  · exact (sGenerator_inclusion 3).trans (by decide +kernel)
  · exact oddGenerator_inclusion 0
  · exact oddGenerator_inclusion 1

private theorem representative_inclusion (i : Fin 18) :
    inclusion (representative i) = repTable i := by
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

private abbrev Q := candidate ⧸ q₂.subgroupOf candidate

private def quotientRepresentative (i : Fin 18) : Q :=
  QuotientGroup.mk' _ ⟨representative i, representative_mem i⟩

private theorem quotientRepresentative_mul (i j : Fin 18) :
    quotientRepresentative i * quotientRepresentative j =
      quotientRepresentative (mulIndex i j) := by
  have hq : (QuotientGroup.mk' (q₂.subgroupOf candidate))
      ⟨qElement (radicalFactor i j), q₂_le_candidate (qElement_mem _)⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (qElement_mem _)
  have h : (⟨representative i, representative_mem i⟩ : candidate) *
      ⟨representative j, representative_mem j⟩ =
      ⟨qElement (radicalFactor i j), q₂_le_candidate (qElement_mem _)⟩ *
      ⟨representative (mulIndex i j), representative_mem _⟩ :=
    Subtype.ext (representative_mul i j)
  simpa only [quotientRepresentative, map_mul, hq, one_mul] using congrArg (QuotientGroup.mk' (q₂.subgroupOf candidate)) h

private noncomputable def modelEquiv : Fin 18 ≃ QuotientModel :=
  Equiv.ofBijective model model_bijective

private noncomputable def modelToQuotient : QuotientModel →* Q where
  toFun m := quotientRepresentative (modelEquiv.symm m)
  map_one' := by
    have h : modelEquiv 0 = 1 := rfl
    rw [← h, modelEquiv.symm_apply_apply]
    change (QuotientGroup.mk' (q₂.subgroupOf candidate)) 1 = 1
    exact map_one _
  map_mul' m n := by
    obtain ⟨i, rfl⟩ := modelEquiv.surjective m
    obtain ⟨j, rfl⟩ := modelEquiv.surjective n
    have h : modelEquiv i * modelEquiv j = modelEquiv (mulIndex i j) :=
      (model_mul i j).symm
    rw [h, modelEquiv.symm_apply_apply, modelEquiv.symm_apply_apply,
      modelEquiv.symm_apply_apply]
    exact (quotientRepresentative_mul i j).symm

private theorem modelToQuotient_model (i : Fin 18) :
    modelToQuotient (model i) = quotientRepresentative i :=
  congrArg quotientRepresentative (modelEquiv.symm_apply_apply i)

private theorem modelToQuotient_injective : Function.Injective modelToQuotient := by
  apply (injective_iff_map_eq_one modelToQuotient).mpr
  intro m hm
  obtain ⟨i, rfl⟩ := model_bijective.surjective m
  rw [modelToQuotient_model] at hm
  have hmem : representative i ∈ q₂ :=
    (QuotientGroup.eq_one_iff (⟨representative i, representative_mem i⟩ : candidate)).mp hm
  obtain ⟨j, hj⟩ := exists_qElement hmem
  have heq := congrArg inclusion hj
  rw [qElement_inclusion, representative_inclusion] at heq
  have hi : i = 0 := repTable_separation i j
    (congrArg (fun p : Equiv.Perm (Fin 100) => (p 0, p 1, p 2)) heq.symm)
  subst i
  rfl

private theorem modelToQuotient_surjective : Function.Surjective modelToQuotient := by
  let R := modelToQuotient.range
  let H : Subgroup Carrier := (R.comap (QuotientGroup.mk' (q₂.subgroupOf candidate))).map
    candidate.subtype
  have hq : q₂ ≤ H := by
    intro x hx
    refine ⟨⟨x, q₂_le_candidate hx⟩, ?_, rfl⟩
    change (QuotientGroup.mk' (q₂.subgroupOf candidate)) ⟨x, q₂_le_candidate hx⟩ ∈ R
    have hx1 : (QuotientGroup.mk' (q₂.subgroupOf candidate))
        ⟨x, q₂_le_candidate hx⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨x, q₂_le_candidate hx⟩ : candidate)).mpr hx
    rw [hx1]
    exact R.one_mem
  have hg (j : Fin 3) : normalizerGenerator j ∈ H := by
    let k : Fin 18 := ![9, 3, 1] j
    have hk : representative k = normalizerGenerator j := by
      fin_cases j <;> simp [k, representative, repWord]
    refine ⟨⟨normalizerGenerator j, normalizerGenerator_mem_candidate j⟩, ?_, rfl⟩
    change ∃ m, modelToQuotient m =
      (QuotientGroup.mk' (q₂.subgroupOf candidate))
        ⟨normalizerGenerator j, normalizerGenerator_mem_candidate j⟩
    refine ⟨model k, ?_⟩
    rw [modelToQuotient_model]
    exact congrArg (QuotientGroup.mk' (q₂.subgroupOf candidate)) (Subtype.ext hk)
  have hc : candidate ≤ H := by
    apply sup_le hq
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact hg j
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (q₂.subgroupOf candidate) z
  obtain ⟨y, hy, hyx⟩ := hc x.property
  have hxy : y = x := Subtype.ext hyx
  subst y
  exact hy

end CandidateQuotient

/-- The concrete candidate has the source quotient S₃ × C₃ by the fixed radical. -/
theorem candidate_quotient_equiv :
    Nonempty ((candidate ⧸ Seed.q₂.subgroupOf candidate) ≃* QuotientModel) :=
  ⟨(MulEquiv.ofBijective CandidateQuotient.modelToQuotient
    ⟨CandidateQuotient.modelToQuotient_injective,
      CandidateQuotient.modelToQuotient_surjective⟩).symm⟩

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
