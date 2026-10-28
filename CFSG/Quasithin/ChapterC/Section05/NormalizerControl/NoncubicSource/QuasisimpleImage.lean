module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Quotient
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
/-!
# Quasisimple images of short blocks

A short group with quasisimple two-core quotient has quasisimple quotient
by U. Any action that kills U and has kernel inside the two-core therefore
has nontrivial quasisimple image. This is the component step in C.5.12;
it does not identify the two-core quotient with the action image.
Source: Aschbacher–Smith C.1.8 and C.5.12, printed pp.123 and163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {L H : Type*} [Group L] [Group H]
theorem short_image_quasisimple (h : IsShort L) [IsQuasisimple (L ⧸ pCore 2 L)]
    (f : L →* H) (hf : Function.Surjective f)
    (hlo : blockU L ≤ f.ker) (hhi : f.ker ≤ pCore 2 L) : IsQuasisimple H := by
  let := h.finite
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : Nontrivial (L ⧸ pCore 2 L) := (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
  have hq : IsQuasisimple (L ⧸ blockU L) := h.quotient_blockU.resolve_right (by
    intro hc
    have hsur := blockCoreProjection_surjective (L := L)
    let : IsCyclic (L ⧸ blockU L) := isCyclic_of_prime_card hc
    let : CommGroup (L ⧸ blockU L) := IsMulCommutative.instCommGroup
    have : Group.IsSolvable (L ⧸ pCore 2 L) := Group.isSolvable_of_surjective hsur
    exact Group.IsPerfect.not_isSolvable _ this)
  let := hq
  let g := QuotientGroup.lift (blockU L) f hlo
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ _ hf _
  let : Nontrivial H := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    have hk : f.ker = ⊤ := top_unique (fun l _ => hs.elim (f l) 1)
    have ht : pCore 2 L = ⊤ := top_unique (hk ▸ hhi)
    have hi : Nontrivial (L ⧸ pCore 2 L) := inferInstance
    exact (QuotientGroup.nontrivial_iff.mp hi) ht
  exact IsQuasisimple.of_surjective g hg
end CFSG.Quasithin.ChapterC
