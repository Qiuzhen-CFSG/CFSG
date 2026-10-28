module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The MS conditions from the original C.2.7 setup

Characteristic-normalizer control in a proper local subgroup gives MS3 on
both H and the literal component-radical product. When the radical is the
two-core of a proper subgroup containing a Sylow two-subgroup, that same
subgroup supplies MS2(a), including its exact embedded-core equality.

The generated first parabolic in 14.6.10(5) supplies this subgroup. These
are structural MS inputs; no block reconstruction or module identification
is asserted here.

Source: Aschbacher--Smith C.1.31, p.135, C.2.3 and C.2.7, pp.144--147.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H R M K : Subgroup G}

omit [Finite G] in
/-- MS3 on the original local group follows from its characteristic control. -/
theorem msCharacteristic_from_source (h : Input κ H R M K) :
    MSCharacteristicCondition (R.subgroupOf H) := by
  have hp : M.subgroupOf H < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro he
    apply h.outside
    exact h.component.1.trans (subgroupOf_eq_top.mp he)
  intro C hC hne
  let := hC
  exact not_normal_of_characteristicNormalizerClosure_le _ _ hp
    h.setup.characteristic_control C hne

/-- Restriction to the actual component-radical product retains MS3. -/
theorem join_msCharacteristic_from_source (h : Input κ H R M K) :
    MSCharacteristicCondition (R.subgroupOf (K ⊔ R)) :=
  msCharacteristic_from_source (source_join_input h)

/-- The actual first core and its Sylow-containing overgroup supply MS2(a). -/
theorem msOddIndexRadical_of_first_core (h : Input κ H R M K)
    (P : Subgroup G) (hPH : P ≤ H) (hPM : P ≤ M)
    (S : Sylow 2 H) (hSP : (S : Subgroup H) ≤ P.subgroupOf H)
    (hR : R = P.pCoreIn 2) :
    MSOddIndexRadical (R.subgroupOf H) := by
  have hp : P.subgroupOf H < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro he
    exact h.outside (h.component.1.trans ((subgroupOf_eq_top.mp he).trans hPM))
  refine ⟨P.subgroupOf H,hp,?_,?_⟩
  · rw [← Nat.not_even_iff_odd,even_iff_two_dvd]
    exact fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le hSP))
  · change (P.subgroupOf H).pCoreIn 2 = R.subgroupOf H
    rw [pCoreIn_subgroupOf 2 P H hPH,hR]
end CFSG.Quasithin.ChapterC.C27Source
