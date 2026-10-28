module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.FiniteData

/-!
# Involution fusion in the 256-entry quotient table

Every square-one entry of the fixed table is conjugate inside the actual
quotient group Q to one of the four marked images, including the identity.
For each entry, kernel arithmetic checks its square. A nonzero square index
is excluded by inequality of the decoded matrix codes, not of the indices.
For the 72 remaining entries, two checked products establish
`marked * g = g * entry`; the inverse of the certified Q element g then
conjugates the marked image to the entry.

This finite-table certificate supplies the fusion premise of the quotient
census independently of subgroup cardinality or table exhaustiveness.
The witnesses and conventions are in `source/README.md` and
`source/witness.json`. The counting motivation is Aschbacher--Smith,
`refs/quasithin.pdf`, printed pp.64--65, A.6.1--4; the matrix provenance
is retained in `TwoCoreCentralizer/source/`.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus.SylowTable

/-- The branch with a nonidentity square checks matrix-code inequality;
the identity-square branch checks both products of the fusion witness. -/
private def entryCheck (i : Fin 256) : Prop :=
  productCheck (tableIndex i) (tableIndex i) (squareIndex i) ∧
    if squareIndex i = 0 then
      productCheck (markedIndex (fusionIndex i)) (conjugatorIndex i) (fusionProductIndex i) ∧
      productCheck (conjugatorIndex i) (tableIndex i) (fusionProductIndex i)
    else code (squareIndex i) ≠ code 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem entry_checked : ∀ i : Fin 256, entryCheck i := by
  unfold entryCheck
  apply forall_fin_of_range
  decide +kernel

/-- All square-one table entries, including identity, fuse to the four
published quotient images, with conjugators in Q itself. -/
theorem table_involution_coverage (i : Fin 256) (hi : (table i)^2 = 1) :
    ∃ j : Fin 4, IsConj (q (lift j)) (table i) := by
  have hc := entry_checked i
  have hs : (table i)^2 = element (squareIndex i) := by
    rw [pow_two]
    exact productCheck_sound hc.1
  by_cases hz : squareIndex i = 0
  · have hf := hc.2
    rw [if_pos hz] at hf
    have he : q (lift (fusionIndex i)) * conjugator i = conjugator i * table i := by
      rw [← element_marked]
      exact (productCheck_sound hf.1).trans (productCheck_sound hf.2).symm
    refine ⟨fusionIndex i, isConj_iff.mpr ⟨(conjugator i)⁻¹, ?_⟩⟩
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left] using
      congrArg (fun x : Q => (conjugator i)⁻¹ * x) he
  · have hn := hc.2
    rw [if_neg hz] at hn
    exfalso
    apply hn
    apply decode_injective
    rw [← element_val, ← element_val]
    exact congrArg (fun x : Q => x.val.val) ((hs.symm.trans hi).trans element_zero.symm)

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus.SylowTable
