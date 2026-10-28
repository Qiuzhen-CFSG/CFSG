module
public import Theory.GroupTheory.ExtraspecialSquare

/-!
# Subgroup images under an extraspecial square action

Preservation of an original subgroup gives invariance of its image in the
central quotient. Pointwise fixation of that image is exactly displacement
into the center. Both assertions use the literal square action and quotient.

Source application: the two singular four-spaces in Aschbacher--Smith,
proof of 12.6.26, pp.831--832.
-/

public section
open Subgroup
namespace Theory.GroupTheory.ExtraspecialSquare
variable (Q : Type*) [Group Q] [IsExtraspecial 2 Q]
/-- Restricting the square action fixes a subgroup image exactly when its
original displacement lies in the center. -/
theorem fixes_imageSpace_iff (a : MulAut Q) (W : Subgroup Q) :
    (∀ u ∈ imageSpace Q W, (isometryAction Q a).val u=u) ↔
      ∀ w ∈ W, a w / w ∈ center Q := by
  constructor
  · intro h w hw
    have hh := h (Additive.ofMul (QuotientGroup.mk' (center Q) w))
      (mem_map_of_mem (QuotientGroup.mk' (center Q)) hw)
    rw [isometryAction_apply,quotientAut_apply_mk] at hh
    exact QuotientGroup.eq_iff_div_mem.mp (congrArg Additive.toMul hh)
  · intro h u hu
    obtain ⟨w,hw,he⟩ := hu
    have he' : u=Additive.ofMul (QuotientGroup.mk' (center Q) w) :=
      congrArg Additive.ofMul he.symm
    rw [he',isometryAction_apply,quotientAut_apply_mk]
    exact congrArg Additive.ofMul (QuotientGroup.eq_iff_div_mem.mpr (h w hw))

/-- A subgroup preserved upstairs has an invariant image under the same
square action on the central quotient. -/
theorem preserves_imageSpace (a : MulAut Q) (W : Subgroup Q)
    (hW : ∀ w ∈ W, a w ∈ W) :
    ∀ u ∈ imageSpace Q W, (isometryAction Q a).val u ∈ imageSpace Q W := by
  intro u hu
  obtain ⟨w,hw,he⟩ := hu
  have he' : u=Additive.ofMul (QuotientGroup.mk' (center Q) w) :=
    congrArg Additive.ofMul he.symm
  rw [he',isometryAction_apply,quotientAut_apply_mk]
  exact mem_map_of_mem (QuotientGroup.mk' (center Q)) (hW w hw)
end Theory.GroupTheory.ExtraspecialSquare
