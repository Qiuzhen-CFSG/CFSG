module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Paths
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Index

/-!
# Outer degree of a genuine symplectic extension

The native inner image is normal. The inner-times-whole-middle factorization
then identifies its index with the index of the native overlap in the whole
middle, by the second isomorphism index formula. This preserves every outer
factor of the original extension.

Source: the extension bookkeeping in Aschbacher--Smith F.4.38,43,
printed pp.294,296 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour

namespace CFSG.Quasithin.Chapter5.Section03SymplecticSource
variable {F : Type*} [Field F]

theorem extension_inner_range_normal (E : SourceExtension F) : E.innerMap.range.Normal := by
  have hr : E.innerMap.range = (inner F).subgroupOf E.carrier := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨b,rfl⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,Subtype.ext hb⟩
  rw [hr]
  change ((MulAut.innerSubgroup (Sp F)).subgroupOf E.carrier).Normal
  infer_instance

theorem extension_outer_index_eq (E : SourceExtension F) :
    E.innerMap.range.index = ((inner F).subgroupOf E.middle).index := by
  let j : E.middle →* E.carrier := inclusion (inf_le_left.trans E.left_le)
  let : E.innerMap.range.Normal := extension_inner_range_normal E
  have hpre : E.innerMap.range.comap j = (inner F).subgroupOf E.middle := by
    ext a
    constructor
    · rintro ⟨b,hb⟩
      exact ⟨b,congrArg Subtype.val hb⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,Subtype.ext hb⟩
  have hgen : E.innerMap.range ⊔ j.range = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b,d,hd,he⟩ := E.factor a a.property
    have ha : a = E.innerMap b * j ⟨d,hd⟩ := Subtype.ext he
    rw [ha]
    exact (E.innerMap.range ⊔ j.range).mul_mem
      (Subgroup.mem_sup_left ⟨b,rfl⟩) (Subgroup.mem_sup_right ⟨⟨d,hd⟩,rfl⟩)
  rw [←hpre,index_comap,←relIndex_sup_left,hgen,relIndex_top_right]

end CFSG.Quasithin.Chapter5.Section03SymplecticSource
