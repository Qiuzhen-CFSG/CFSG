module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.CentralizerIntersections.Data
import Mathlib.Tactic.FinCases

/-!
# Kernel certificates for a J₃ centralizer intersection

The selected generators are checked on every letter. Positive words are
then checked at the separating pair, and explicit nonmembership witnesses
exclude all remaining rows of the exhaustive `CRep` enumeration.
Source: GLS 3, Table 5.3h, p.269, via the fixed ATLAS permutation model.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.Intersections
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal Theory.GroupTheory
open OrderCertificate CentralizerCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false

private theorem selectedU_eq_0 :
    CRep (selectedU 0) = evalWord fastThompson (localWordU 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem selectedU_eq_1 :
    CRep (selectedU 1) = evalWord fastThompson (localWordU 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem selectedU_eq_2 :
    CRep (selectedU 2) = evalWord fastThompson (localWordU 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem selectedU_eq_3 :
    CRep (selectedU 3) = evalWord fastThompson (localWordU 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem selectedU_eq (j : Fin 4) :
    CRep (selectedU j) = evalWord fastThompson (localWordU j) := by
  fin_cases j
  · exact selectedU_eq_0
  · exact selectedU_eq_1
  · exact selectedU_eq_2
  · exact selectedU_eq_3

public theorem selectedU_mem (j : Fin 4) :
    CRep (selectedU j) ∈ (localFamily 2).map embedding := by
  rw [selectedU_eq]
  exact word_mem _ _ fastThompson_mem _

private theorem positiveU : ∀ r : CIndex, goodU r →
    CRep r 0 = evalWord (fun j => CRep (selectedU j)) (wordU r) 0 ∧
    CRep r 1 = evalWord (fun j => CRep (selectedU j)) (wordU r) 1 := by
  rintro ⟨r0,r1,r2,r3,r4,r5⟩
  revert r0 r1 r2 r3 r4 r5
  decide +kernel

public theorem goodU_mem (r : CIndex) (hr : goodU r) :
    CRep r ∈ (localFamily 2).map embedding := by
  have he := eq_of_pair (rep_mem r)
    (word_mem C0H _ (fun j => rep_mem (selectedU j)) (wordU r))
    (positiveU r hr).1 (positiveU r hr).2
  rw [he]
  exact word_mem _ _ selectedU_mem _

/-- A selected basis vector witnesses failure to normalize the indicated span. -/
public theorem exclusionU : ∀ r : CIndex, ¬ goodU r →
    ∀ k : Fin 16, supported 5 k →
      (CRep r * fastBasis (outsideU r) * (CRep r)⁻¹) 0 ≠ fastElementary k 0 ∨
      (CRep r * fastBasis (outsideU r) * (CRep r)⁻¹) 1 ≠ fastElementary k 1 := by
  rintro ⟨r0,r1,r2,r3,r4,r5⟩
  revert r0 r1 r2 r3 r4 r5
  decide +kernel

public theorem outsideU_supported : ∀ r : CIndex,
    (5 : Nat).testBit (outsideU r).val = true := by
  rintro ⟨r0,r1,r2,r3,r4,r5⟩
  revert r0 r1 r2 r3 r4 r5
  decide +kernel

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.Intersections
