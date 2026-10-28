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

private theorem selectedE_eq_0 :
    CRep (selectedE 0) = evalWord fastAffine (localWordE 0) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem selectedE_eq_1 :
    CRep (selectedE 1) = evalWord fastAffine (localWordE 1) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem selectedE_eq_2 :
    CRep (selectedE 2) = evalWord fastAffine (localWordE 2) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

private theorem selectedE_eq_3 :
    CRep (selectedE 3) = evalWord fastAffine (localWordE 3) := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem selectedE_eq (j : Fin 4) :
    CRep (selectedE j) = evalWord fastAffine (localWordE j) := by
  fin_cases j
  · exact selectedE_eq_0
  · exact selectedE_eq_1
  · exact selectedE_eq_2
  · exact selectedE_eq_3

public theorem selectedE_mem (j : Fin 4) :
    CRep (selectedE j) ∈ (localFamily 1).map embedding := by
  rw [selectedE_eq]
  exact word_mem _ _ fastAffine_mem _

private theorem positiveE : ∀ r : CIndex, goodE r →
    CRep r 0 = evalWord (fun j => CRep (selectedE j)) (wordE r) 0 ∧
    CRep r 1 = evalWord (fun j => CRep (selectedE j)) (wordE r) 1 := by
  rintro ⟨r0,r1,r2,r3,r4,r5⟩
  revert r0 r1 r2 r3 r4 r5
  decide +kernel

public theorem goodE_mem (r : CIndex) (hr : goodE r) :
    CRep r ∈ (localFamily 1).map embedding := by
  have he := eq_of_pair (rep_mem r)
    (word_mem C0H _ (fun j => rep_mem (selectedE j)) (wordE r))
    (positiveE r hr).1 (positiveE r hr).2
  rw [he]
  exact word_mem _ _ selectedE_mem _

/-- A selected basis vector witnesses failure to normalize the indicated span. -/
public theorem exclusionE : ∀ r : CIndex, ¬ goodE r →
    ∀ k : Fin 16, supported 15 k →
      (CRep r * fastBasis (outsideE r) * (CRep r)⁻¹) 0 ≠ fastElementary k 0 ∨
      (CRep r * fastBasis (outsideE r) * (CRep r)⁻¹) 1 ≠ fastElementary k 1 := by
  rintro ⟨r0,r1,r2,r3,r4,r5⟩
  revert r0 r1 r2 r3 r4 r5
  decide +kernel

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.Intersections
