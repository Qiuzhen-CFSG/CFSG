module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic
public import Theory.GroupTheory.CComponent.SolvableQuotient

/-!
# C-components of a natural extension

A nonbinary natural extension has just one C-component, the whole group.
Indeed, a C-component has nontrivial subnormal image in the simple SL₂
quotient, hence supplements the solvable kernel. The perfect-subnormal
supplement theorem identifies it with the solvable residual, which is the
whole extension by perfectness.

This supplies the intrinsic component step for symplectic root centralizers
in Aschbacher--Smith, E.6.25, printed p.256 (1 March 2004 manuscript).
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.NaturalExtension
variable {F L : Type*} [Field F] [Finite F] [CharP F 2] [Group L] [Finite L]
variable {Q : Subgroup L} [Q.Normal] (d : NaturalExtension (F := F) Q)
include d

/-- Every C-component of a nonbinary natural extension is the whole group. -/
theorem cComponent_eq_top (hF : 2 < Nat.card F)
    {B : Subgroup L} (hB : B.IsCComponent) : B = ⊤ := by
  let := d.elementary
  let : Group.IsNilpotent Q := (IsElementaryAbelian.isPGroup 2 Q).isNilpotent
  let : Group.IsSolvable Q := inferInstance
  let := d.perfect hF
  let := hB.perfect
  let : IsSimpleGroup (L ⧸ Q) :=
    (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq d.kernel.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective d.projection d.surjective))).mpr
      (NaturalExtension.model_simple hF)
  have hm : B.map (QuotientGroup.mk' Q) = ⊤ := by
    rcases (hB.map_quotient Q).subnormal.eq_bot_or_top_of_isSimpleGroup
        (inferInstance : IsSimpleGroup (L ⧸ Q)) with hb | ht
    · exact ((hB.map_quotient Q).ne_bot hb).elim
    · exact ht
  have hsup : B ⊔ Q = ⊤ := by
    simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using
      congrArg (Subgroup.comap (QuotientGroup.mk' Q)) hm
  exact (hB.subnormal.eq_solvableResidual_of_sup_eq_top Q hsup).trans
    Subgroup.solvableResidual_eq_top

end Theory.SpecificGroups.SymplecticFour.NaturalExtension
