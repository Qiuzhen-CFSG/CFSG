module
public import Theory.GroupTheory.NormalElementaryNinePerfect
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Perfect subgroups centralizing a normal section of order nine

If a normal subgroup B has image of order nine modulo the ambient two-core,
every perfect subgroup centralizes that image. The resulting commutator lies
both in B and in the ambient two-core. Subnormal core transport identifies
this intersection with the intrinsic O₂(B), retaining the original quotient.

This is the section-centralizer step used in Aschbacher--Smith 8.3.7,
printed pp.724--725, in the normal-X branch. Its source application is in
Chapter10's selected-module QuietTensorEscape development.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Perfect subgroups centralize a normal section of order nine modulo its
own two-core, when that section is the image in the ambient two-core quotient. -/
theorem perfect_centralizes_normal_nine_section
    {H : Type*} [Group H] [Finite H] (B : Subgroup H) [B.Normal]
    (hB : Nat.card (B.map (QuotientGroup.mk' (pCore 2 H))) = 9)
    (J : Subgroup H) [Group.IsPerfect J] : ⁅J,B⁆ ≤ B.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let : (B.map q).Normal := (inferInstance : B.Normal).map q
    (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect (J.map q) := Group.IsPerfect.map q
  have hc := commutator_eq_bot_iff_le_centralizer.mpr
    (normal_nine_perfect_centralizes (B.map q) hB (J.map q))
  have hp : ⁅J,B⁆ ≤ pCore 2 H := by
    simpa only [←map_commutator,Subgroup.map_eq_bot_iff,q,QuotientGroup.ker_mk'] using hc
  have he : B.pCoreIn 2 = B ⊓ pCore 2 H := by
    rw [pCoreIn,←(Normal.isSubnormal (inferInstance : B.Normal)).pCore_subgroupOf 2,
      subgroupOf_map_subtype,inf_comm]
  rw [he]
  exact le_inf (commutator_le_right J B) hp

end Theory.GroupTheory
