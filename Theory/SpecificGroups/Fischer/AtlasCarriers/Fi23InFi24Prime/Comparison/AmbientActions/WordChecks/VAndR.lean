module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Part0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Part1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Part2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Part3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Part4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Part5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Part6
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Part7

/-!
# Exact forward v and r actions on every Fi₂₃ label

Eight bounded certificates cover all 31671 labels. Their Boolean checks reduce
in the Lean kernel using the literal `wordMap`, `letterMap`, `labelMap`, and the
shared auxiliary witnesses. The balanced checker transfers the result to every
finite label. Neither signed-letter cancellation nor interpretation in the
original carrier is assumed.

These two identities discharge the v and r premises of
`candidateAMap_apply_labelMap_of_auxiliary_checks`; v also discharges the
corresponding premise for B. `VAndR.Application` records those applications.
Source: retained ATLAS F24G1-p306936B0 tables and the exact `WordSetup` lists;
see `WordChecks/source/README.md` for the witness transcription.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks

private theorem vAndR_checked : checkPow VAndR.pointTest 0 15 = true :=
  checkPow_join VAndR.pointTest 14 0
    (checkPow_join VAndR.pointTest 13 0
      (checkPow_join VAndR.pointTest 12 0 VAndR.checked0 VAndR.checked1)
      (checkPow_join VAndR.pointTest 12 8192 VAndR.checked2 VAndR.checked3))
    (checkPow_join VAndR.pointTest 13 16384
      (checkPow_join VAndR.pointTest 12 16384 VAndR.checked4 VAndR.checked5)
      (checkPow_join VAndR.pointTest 12 24576 VAndR.checked6 VAndR.checked7))

private theorem vAndR_point_properties (i : Fin 31671) :
    wordMap letterMap false vLetters (labelMap i) = labelMap (vMap i) ∧
    wordMap letterMap false rLetters (labelMap i) = labelMap (rMap i) := by
  have h := checkPow_sound VAndR.pointTest 15 0 vAndR_checked i.val
    (Nat.zero_le _) (Nat.lt_trans i.isLt (by decide))
  have hi : Fin.ofNat 31671 i.val = i := by simp
  simpa only [VAndR.pointTest, hi, decide_eq_true_eq] using h

/-- The exact packed forward v word acts as its source-label witness. -/
theorem vWord_apply_labelMap : ∀ i : Fin 31671,
    wordMap letterMap false vLetters (labelMap i) = labelMap (vMap i) :=
  fun i => (vAndR_point_properties i).1

/-- The exact packed forward r word acts as its source-label witness. -/
theorem rWord_apply_labelMap : ∀ i : Fin 31671,
    wordMap letterMap false rLetters (labelMap i) = labelMap (rMap i) :=
  fun i => (vAndR_point_properties i).2

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks
