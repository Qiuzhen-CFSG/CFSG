module
public import Theory.SpecificGroups.LieType.F4LongParabolic.BinaryOriginalCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head

/-!
# A literal original-core action diagnostic at the MS source boundary

The finite binary F4 matrix overgroup P and its normal perfect subgroup L
have an element of [O2(P),L] centralizing L but moved by O2(P). Transport the
checked matrix calculation through the actual subgroup inclusion to retain
exactly the BinaryMS.commutatorCore and centralizer conventions.

This disproves the proposed local centrality implication from normality and
perfectness alone. The full MS-pair assumptions have not been certified for
this carrier: quotient, C-component, generalized-Fitting, SQTK, radical and
canonical-carrier comparisons remain with qt-rank-two-ms93. No counterexample
to the full source theorem or classification conclusion is claimed.

Source: Aschbacher--Smith C.1.34(4), printed pp.136--137, whose centrality
argument refers to MS93 (4.4)--(4.5); MS93's F4 examples, printed p.831.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.F4OriginalCandidate
open Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates

/-- A concrete finite overgroup and a normal perfect subgroup for which the
literal original commutator core has a noncentral fixed factor. This is a
counterexample to that local implication, not a certified full MS pair. -/
theorem original_binaryCore_fixed_not_central :
    ¬ BinaryMS.commutatorCore (L.subgroupOf P) ⊓
      centralizer (L.subgroupOf P : Set P) ≤ centralizer (pCore 2 P : Set P) := by
  intro hc
  apply original_core_fixed_factor_not_central
  intro y hy x hx
  have hm : (BinaryMS.commutatorCore (L.subgroupOf P)).map P.subtype =
      ⁅P.pCoreIn 2,L⁆ := by
    rw [BinaryMS.commutatorCore,map_commutator,map_subgroupOf_eq_of_le L_le_P]
    rfl
  obtain ⟨yP,hyP,rfl⟩ := hm.symm ▸ hy.1
  have hyc : yP ∈ centralizer (L.subgroupOf P : Set P) := by
    intro l hl
    exact Subtype.ext (hy.2 l hl)
  obtain ⟨xP,hxP,rfl⟩ := hx
  have hh := hc ⟨hyP,hyc⟩ xP hxP
  simpa only [map_mul] using congrArg P.subtype hh

/-- Normality and perfectness hold for this same literal subgroup. No component,
SQTK, quotient, or radical hypothesis is being assumed or claimed. -/
theorem original_binaryCore_normal_perfect_diagnostic :
    (L.subgroupOf P).Normal ∧ Group.IsPerfect (L.subgroupOf P) ∧
    ¬ BinaryMS.commutatorCore (L.subgroupOf P) ⊓
      centralizer (L.subgroupOf P : Set P) ≤ centralizer (pCore 2 P : Set P) := by
  let := L_isPerfect
  have hp : Group.IsPerfect (L.subgroupOf P) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe L_le_P).symm.toMonoidHom)
      (subgroupOfEquivOfLe L_le_P).symm.surjective
  exact ⟨L_normal_in_P,hp,original_binaryCore_fixed_not_central⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.F4OriginalCandidate
