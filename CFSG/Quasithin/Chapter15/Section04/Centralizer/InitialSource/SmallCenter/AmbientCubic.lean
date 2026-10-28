module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.BaumannCubic
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.SylowImage
public import Stellmacher.SectionTwo.BaumannOmegaSupplementData

/-!
# The selected cubic block is a block in the original local group

The normal closure L of Baum(T) has an actual Sylow subgroup with image
Baum(T), and inherits the solvable characteristic-two hypotheses. The
selected local class lies in L and supplies Thompson movement and literal
module support. Its block extends subnormally to L, then to the original
group by normality of L. The block and original J(T) are unchanged.

Source: Aschbacher--Smith C.1.26--28 and 15.4.7, pp.132--134,1158.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open ChapterC.GlaubermanNiles ChapterC.RankOne.Solvable
variable {G : Type*} [Group G] [Finite G]

/-- The local residual extends to an actual ambient A₃ block with its original Thompson action. -/
theorem selected_ambient_cubic_block
    (h : SectionTwo.Hypotheses G) (T : Sylow 2 G)
    (hcore : pCore 2 G = (T : Subgroup G) ⊓ centralizer (SectionTwo.vSubgroup T : Set G))
    (hnot : ¬ SectionTwo.vSubgroup T ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (hu : IsUniqueMaximalContaining (T : Subgroup G) ⊤)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (K : Subgroup G) (hBK : ChapterB.baumann (T : Subgroup G) ≤ K)
    (hclass : InLocalClass (inclusion hBK))
    (hb : ChapterC.IsBlock (pResidual 2 K))
    (ha : ChapterC.IsAlternatingBlock (pResidual 2 K) 3) :
    ChapterC.IsBlock ((pResidual 2 K).map K.subtype) ∧
    ChapterC.IsAlternatingBlock ((pResidual 2 K).map K.subtype) 3 ∧
    (pResidual 2 K).map K.subtype =
      ⁅(pResidual 2 K).map K.subtype,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let B := (T : Subgroup G) ⊓ centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G)) : Set G)
  let L := normalClosure (B : Set G)
  let : L.Normal := normalClosure_normal
  obtain ⟨PB,hPB,hL,_⟩ := SectionTwo.baumann_omega_supplement_data h T hcore hnot hu
  change (PB : Subgroup L).map L.subtype = B at hPB
  obtain ⟨hKL,hJ,_⟩ := selected_cubic_geometry T K hBK hclass hC hb ha
  change K ≤ L at hKL
  obtain ⟨P,he,hP⟩ := hclass.sylow
  have hPK : (P : Subgroup K).map K.subtype = B := by
    rw [←he,MonoidHom.range_eq_map,map_map]
    change (⊤ : Subgroup B).map B.subtype = B
    rw [←MonoidHom.range_eq_map,range_subtype]
  have hk := selected_localKernel T K P hPK hC
  let f : K →* L := inclusion hKL
  have hPP : (P : Subgroup K).map f = (PB : Subgroup L) := by
    apply map_injective L.subtype_injective
    rw [map_map,hPB]
    exact hPK
  have hJK := hclass.cubic_residual_thompson (baumann_isBaumannFixed T) hk hb ha P he
  have hUK : (ChapterC.blockU (pResidual 2 K)).map (pResidual 2 K).subtype ≤
      SectionTwo.vSubgroup P := by
    rw [←localV_eq_vSubgroup hclass.injective P he]
    exact hclass.cubic_block_support hk hb ha
  have hs := subnormal_map_of_sylow_image hL f (inclusion_injective hKL)
    P PB hPP (pResidual 2 K) hb.subnormal ha hJK hUK
  have hsG : ((pResidual 2 K).map K.subtype).IsSubnormal := by
    have hh := hs.trans' (inferInstance : L.Normal).isSubnormal
    rw [map_map] at hh
    exact hh
  have haG := isAlternatingBlock_of_equiv
    ((pResidual 2 K).equivMapOfInjective K.subtype K.subtype_injective) ha
  exact ⟨⟨inferInstance,haG.2.1,hsG⟩,haG,hJ⟩
end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
