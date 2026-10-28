module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.QuasisimpleImage
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceImageNormal
/-!
# The literal centralizer-quotient image of a short block

The full block layer U(L) lies in the elementary source module V. Thus the
canonical quotient X/C_X(V) kills U(L), and its kernel on L is contained in
O₂(L) by the short-block centralizer theorem. Consequently the actual image
of L is quasisimple. Neither ambient quotient is identified with the other.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
theorem short_centralizer_image_quasisimple
    (L X V : Subgroup G) (hL : IsShort L) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hLX : L ≤ X) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U L ≤ V) [IsElementaryAbelian 2 V] :
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
    IsQuasisimple ((L.subgroupOf X).map q) := by
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let E := (subgroupOfEquivOfLe hLX).symm
  let f := (q.subgroupMap (L.subgroupOf X)).comp E.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp E.surjective
  have hlo : blockU L ≤ f.ker := by
    intro l hl
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    intro v hv
    apply Subtype.ext
    have h1 : (l : G) ∈ V := hUV (mem_map_of_mem L.subtype hl)
    exact congrArg (fun z : V => (z : G)) (mul_comm (⟨v,hv⟩ : V) ⟨(l : G),h1⟩)
  have hhi : f.ker ≤ pCore 2 L := by
    intro l hl
    rw [←hL.centralizer_blockU]
    intro u hu
    apply Subtype.ext
    have he : q (E l : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    have hc := (QuotientGroup.eq_one_iff _).mp he
    exact congrArg X.subtype (hc ⟨u,hVX (hUV (mem_map_of_mem L.subtype hu))⟩
      (hUV (mem_map_of_mem L.subtype hu)))
  exact short_image_quasisimple hL f hf hlo hhi
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
