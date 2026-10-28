module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.GraphActions
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Labels.ReflectedNeighbor
/-!
# The original labeled neighbor belongs to the base orbit

The genuine source pair alignment carries (u,C_P(u)) to (z,B5) while
normalizing the same marked I, hence its omega plane. Uniqueness of the
original z-colored parabolic containing B5 identifies the image of the
u-labeled neighbor with F1. The graph automorphism is literal ambient
conjugation; no transitivity of the six-member family is assumed.
Source: Aschbacher--Smith J.4.8--10, printed pp.443--445.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.SixCycle
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
open ChapterF.SourceCompletion.BinaryRee
variable {D:Type*} [Group D] (q:Completion D)
  {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
  (e:first≃*p.F₁ B5) (f:D→*G)
  (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
include q s hi f hleft hz hfive

theorem labeled_neighbor_conjugate_base
    (E:globalFamily p B5 c.z (sourceU e))
    (hE:(E:Subgroup G)∈colorFamily p B5 c.z (sourceU e) (sourceU e))
    (hB:fixedFive B5 (sourceU e)≤E) :
    ∃g:G,∃hg:g∈normalizer (pairSpan c.z (sourceU e):Set G),
      sourceGraphEquiv p B5 c e hz g hg E=baseVertex p B5 c e hz := by
  obtain ⟨g,hgu,hgB,hgI⟩ := source_pair_alignment q c B5 e f hleft hz hfive
  have hg:g∈normalizer (pairSpan c.z (sourceU e):Set G) :=
    sourceI_normalizer_le_pairSpan_normalizer p B5 c e hz
      (mem_normalizer_iff_map_conj_eq.mpr hgI)
  have hEg:E.val.conjBy g∈colorFamily p B5 c.z (sourceU e) c.z := by
    simpa only [hgu] using color_conjugate_mem p B5 c.z (sourceU e) g hg hE
  have hBg:B5Image B5≤E.val.conjBy g := by
    have hm:=map_mono (f:=(MulAut.conj g).toMonoidHom) hB
    change (fixedFive B5 (sourceU e)).conjBy g≤E.val.conjBy g at hm
    rwa [hgB] at hm
  have hBF:B5Image B5≤p.F₁ B5 := by
    rw [←hfive]
    rintro x ⟨a,_,rfl⟩
    exact (e a).property
  refine ⟨g,hg,Subtype.ext ?_⟩
  rw [sourceGraphEquiv_apply,baseVertex_coe]
  exact color_members_eq_of_five p s B5 hi c e hEg (first_mem_color p B5 c e hz)
    (B5Image_card d.card_Z B5) hBg hBF

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.SixCycle
