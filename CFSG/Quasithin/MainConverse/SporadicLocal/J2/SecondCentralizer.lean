module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J2.EvenSetup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient.Checks
import Mathlib.Tactic.FinCases

/-!
# Self-centralization of the second Hall–Janko local radical

Inside the actual degree-100 ATLAS carrier, the full normalizer of `Seed.q₂`
has normal forms `q * r`, with `q` one of the 64 certified radical elements
and `r` one of the eighteen quotient representatives. Their checked product
table and radical normality make these normal forms a submonoid. Finiteness
makes it a subgroup, and the full-normalizer coverage theorem proves exhaustion.

Commutation with radical generators 2 and 0, evaluated at point 1, already
forces the quotient representative to be the identity. The finite check uses
only the existing permutation tables and is verified by Lean's kernel. It
therefore proves the intrinsic centralizer inclusion in the full `Seed.p₂`.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed pp.4 and 482;
GLS3, Table 5.3g, the local subgroup `2^(2+4).(S₃ × C₃)`.
The unchanged ATLAS `J2G1-p100B0` tables and their source attribution are in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/J2/ExceptionalParabolics/`.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J2Even
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open GeneratorPair GeneratorPair.SecondOrbitCertificate Seed PairNormalizer
open PairNormalizer.RadicalData PairNormalizer.CandidateQuotient

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
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul, map_mul, representative_inclusion, representative_inclusion,
    representative_inclusion, qElement_inclusion]
  exact repTable_mul i j

private def normalForms : Submonoid Carrier where
  carrier := {x | ∃ q ∈ q₂, ∃ i, x = q * representative i}
  one_mem' := ⟨1, q₂.one_mem, 0, by rfl⟩
  mul_mem' := by
    rintro x y ⟨q, hq, i, rfl⟩ ⟨r, hr, j, rfl⟩
    have hn := candidate_le_p₂ (representative_mem i)
    have hc : representative i * r * (representative i)⁻¹ ∈ q₂ :=
      ((Subgroup.mem_normalizer_iff.mp hn) r).mp hr
    refine ⟨q * (representative i * r * (representative i)⁻¹) *
      qElement (radicalFactor i j), q₂.mul_mem (q₂.mul_mem hq hc) (qElement_mem _),
      mulIndex i j, ?_⟩
    calc
      (q * representative i) * (r * representative j) =
          (q * (representative i * r * (representative i)⁻¹)) *
            (representative i * representative j) := by simp only [mul_assoc, inv_mul_cancel_left]
      _ = _ := by rw [representative_mul]; simp only [mul_assoc]

private theorem normalizer_normalForm {x : Carrier} (hx : x ∈ p₂) :
    ∃ (j : Fin 64) (i : Fin 18), x = qElement j * representative i := by
  have hclosed : (Subgroup.closure (normalForms : Set Carrier)).toSubmonoid =
      normalForms := by
    rw [Subgroup.closure_toSubmonoid_of_finite, Submonoid.closure_eq]
  have hq : q₂ ≤ Subgroup.closure (normalForms : Set Carrier) := by
    intro q hq
    apply Subgroup.subset_closure
    exact ⟨q, hq, 0, (mul_one q).symm⟩
  have hg (k : Fin 3) : normalizerGenerator k ∈
      Subgroup.closure (normalForms : Set Carrier) := by
    apply Subgroup.subset_closure
    let i : Fin 18 := ![9, 3, 1] k
    have hi : representative i = normalizerGenerator k := by
      fin_cases k <;> simp [i, representative, repWord]
    exact ⟨1, q₂.one_mem, i, by rw [one_mul, hi]⟩
  have hle : candidate ≤ Subgroup.closure (normalForms : Set Carrier) := by
    apply sup_le hq
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact hg k
  have hm : x ∈ normalForms := by
    rw [← hclosed]
    exact hle (full_normalizer_le_candidate hx)
  obtain ⟨q, hq, i, hi⟩ := hm
  obtain ⟨j, rfl⟩ := exists_qElement hq
  exact ⟨j, i, hi⟩

set_option maxRecDepth 100000 in
private theorem centralizer_check : ∀ (i : Fin 18) (j : Fin 64),
    (qTable j * repTable i) (qGenTable 2 1) = qGenTable 2 ((qTable j * repTable i) 1) →
    (qTable j * repTable i) (qGenTable 0 1) = qGenTable 0 ((qTable j * repTable i) 1) →
    i = 0 := by
  apply allFin
  decide +kernel

/-- The fixed second radical is self-centralizing inside its full normalizer. -/
public theorem second_radical_centralizer_le :
    centralizer (Seed.q₂.subgroupOf Seed.p₂ : Set Seed.p₂) ≤
      Seed.q₂.subgroupOf Seed.p₂ := by
  intro x hx
  obtain ⟨j, i, hi⟩ := normalizer_normalForm x.property
  have hc (k : Fin 6) :
      (qTable j * repTable i) (qGenTable k 1) =
        qGenTable k ((qTable j * repTable i) 1) := by
    have hg : q₂Generator k ∈ q₂ := Subgroup.subset_closure ⟨k, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hx
      (⟨q₂Generator k, q₂.le_normalizer hg⟩ : p₂) hg
    have he : (x : Carrier) * q₂Generator k = q₂Generator k * (x : Carrier) :=
      (congrArg Subtype.val h).symm
    have hp := congrArg (fun y : Carrier => inclusion y 1) he
    simpa only [hi, map_mul, qElement_inclusion, representative_inclusion,
      q₂Generator_inclusion, Equiv.Perm.mul_apply] using hp
  have hz : i = 0 := centralizer_check i j (hc 2) (hc 0)
  change (x : Carrier) ∈ q₂
  rw [hi, hz]
  exact q₂.mul_mem (qElement_mem j) q₂.one_mem

end CFSG.Quasithin.MainConverse.SporadicLocal.J2Even
