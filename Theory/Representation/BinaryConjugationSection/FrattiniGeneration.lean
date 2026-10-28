module
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages
public import Mathlib.GroupTheory.Frattini

/-!
# Full coordinate images through a Frattini kernel

A subgroup with full image under a binary conjugation section generates
the numerator together with the coordinate kernel. When that kernel lies
in the Frattini subgroup, the original subgroup is already the numerator.
The statement retains the actual coordinate map and ambient subgroups.

Source: the Frattini nongenerating property, as used in Aschbacher--Smith,
proof of 12.6.26, printed p.833, to lift the full cubic displacement.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z : Subgroup G} {σ : Representation (ZMod 2) H W}

/-- A full coordinate image contains the original numerator when the
coordinate kernel lies in its Frattini subgroup. -/
theorem le_of_full_image_of_kernel_le_frattini [Finite U]
    (κ : BinaryConjugationSection H U Z σ) (B : Subgroup G) (hBU : B ≤ U)
    (hZ : Z ≤ (frattini U).map U.subtype) (hfull : κ.imageSpace B = ⊤) : U ≤ B := by
  have hgen : U ≤ B ⊔ (frattini U).map U.subtype := by
    intro u hu
    apply κ.subspacePreimage_le_of_imageSpace_le ⊤ _
      (hZ.trans le_sup_right) _ ((κ.mem_subspacePreimage ⊤ u).mpr ⟨hu,Submodule.mem_top⟩)
    rw [←hfull]
    exact κ.imageSpace_mono le_sup_left
  have he : B.subgroupOf U ⊔ frattini U = ⊤ := by
    apply map_injective U.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBU,←MonoidHom.range_eq_map,range_subtype]
    exact le_antisymm (sup_le hBU (map_subtype_le _)) hgen
  have he' := congrArg (Subgroup.map U.subtype) (frattini_nongenerating he)
  rw [map_subgroupOf_eq_of_le hBU,←MonoidHom.range_eq_map,range_subtype] at he'
  exact he'.ge

end Representation.BinaryConjugationSection
