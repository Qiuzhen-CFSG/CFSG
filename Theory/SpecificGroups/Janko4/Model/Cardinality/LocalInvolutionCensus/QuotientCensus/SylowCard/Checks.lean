module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.FiniteData
import Mathlib.Tactic.FinCases

/-!+# Kernel certificates for the 256-entry quotient subgroup table

The multiplication tree starts at the identity, and all right transitions by
the four generators and their proposed inverses agree with matrix products.
Adjacent sorted matrix codes are strictly increasing. These checks use the
literal data in `FiniteData`; no discovery-program assertion is assumed.

The subgroup and cardinality consequences are assembled in `SylowCard`.
This is a finite certificate for the local census motivated by
Aschbacher--Smith, `refs/quasithin.pdf`, printed pp.64--65, A.6.1--4.
Matrix and witness provenance is recorded in `QuotientCensus/source/README.md`.
-/

set_option maxRecDepth 100000

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus.SylowTable.CardChecks

theorem root : tableIndex 0 = 0 := by decide +kernel

theorem parent_lt : ∀ i : Fin 256, i ≠ 0 → parent i < i := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem tree : ∀ i : Fin 256, i ≠ 0 →
    productCheck (tableIndex (parent i)) (genIndex (letter i)) (tableIndex i) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem inverses : ∀ a : Fin 4, productCheck (genIndex a) (genInvIndex a) 0 := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem sorted_lt : ∀ i : Fin 255,
    (code (tableIndex (sorted i.castSucc))).toNat <
      (code (tableIndex (sorted i.succ))).toNat := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem forward0 : ∀ i : Fin 256,
    productCheck (tableIndex i) (genIndex 0) (tableIndex (step 0 i)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem forward1 : ∀ i : Fin 256,
    productCheck (tableIndex i) (genIndex 1) (tableIndex (step 1 i)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem forward2 : ∀ i : Fin 256,
    productCheck (tableIndex i) (genIndex 2) (tableIndex (step 2 i)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem forward3 : ∀ i : Fin 256,
    productCheck (tableIndex i) (genIndex 3) (tableIndex (step 3 i)) := by
  apply forall_fin_of_range
  decide +kernel

theorem forward (a : Fin 4) (i : Fin 256) :
    productCheck (tableIndex i) (genIndex a) (tableIndex (step a i)) := by
  fin_cases a
  · exact forward0 i
  · exact forward1 i
  · exact forward2 i
  · exact forward3 i

set_option maxHeartbeats 4000000 in
private theorem backward0 : ∀ i : Fin 256,
    productCheck (tableIndex i) (genInvIndex 0) (tableIndex (stepInv 0 i)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem backward1 : ∀ i : Fin 256,
    productCheck (tableIndex i) (genInvIndex 1) (tableIndex (stepInv 1 i)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem backward2 : ∀ i : Fin 256,
    productCheck (tableIndex i) (genInvIndex 2) (tableIndex (stepInv 2 i)) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem backward3 : ∀ i : Fin 256,
    productCheck (tableIndex i) (genInvIndex 3) (tableIndex (stepInv 3 i)) := by
  apply forall_fin_of_range
  decide +kernel

theorem backward (a : Fin 4) (i : Fin 256) :
    productCheck (tableIndex i) (genInvIndex a) (tableIndex (stepInv a i)) := by
  fin_cases a
  · exact backward0 i
  · exact backward1 i
  · exact backward2 i
  · exact backward3 i

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus.SylowTable.CardChecks
