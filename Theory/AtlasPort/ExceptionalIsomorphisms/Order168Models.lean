module

/-
Adapted from Atlas/Comparisons/Exceptional/Order168Models.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.PSL3Two.AlternatingFiveObstruction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
set_option warningAsError false

public section

/-!
# The matrix models of order 168

The scalar-center count and the existing CFSG determinant calculation identify
SL₃(2) with its projective quotient and establish its order. The elementary
Iwasawa proof gives simplicity for the subsequent faithful Sylow action.
The source PSL₂(7) order is computed from the same scalar-quotient identity.
-/


namespace Atlas.Comparisons.Exceptional
open scoped MatrixGroups
local instance order168ModelsPrime1 : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem psl2Seven_card : Nat.card PSL(2, ZMod 7) = 168 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 7) 2
  norm_num [Fin.prod_univ_succ] at h
  rw [Nat.card_eq_fintype_card]
  omega

theorem sl3Two_center_eq_bot : Subgroup.center SL(3, ZMod 2) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [Atlas.ExceptionalSupport.card_sl_center (ι := Fin 3) (F := ZMod 2)]
  norm_num [Nat.card_eq_fintype_card]

noncomputable def sl3TwoEquivPsl3Two : SL(3, ZMod 2) ≃* PSL(3, ZMod 2) :=
  MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨by
    apply (QuotientGroup.mk' _).ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_mk', sl3Two_center_eq_bot], QuotientGroup.mk'_surjective _⟩

theorem sl3Two_card : Nat.card SL(3, ZMod 2) = 168 := Matrix.PSL3Two.card_SL

theorem psl3Two_simple : IsSimpleGroup PSL(3, ZMod 2) :=
  Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)

theorem sl3Two_simple : IsSimpleGroup SL(3, ZMod 2) := by
  let := psl3Two_simple
  exact sl3TwoEquivPsl3Two.isSimpleGroup

end Atlas.Comparisons.Exceptional
