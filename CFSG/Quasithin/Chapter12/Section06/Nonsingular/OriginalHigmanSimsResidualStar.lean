module

public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients

/-!
# The exact common-residual image in the singular star quotient

For J inside H, the kernel of the actual inclusion followed by H/O₂(H)
is a normal two-subgroup of J. If the whole O₂(J) lies in O₂(H), this
kernel is exactly O₂(J). Thus the literal star image is J/O₂(J), without
taking a further quotient of that image.

The existing local-family quotient theorem transports the original
L(H,P) membership to the image of the actual full Sylow subgroup. In the
common HS residual application the resulting exact star image is A5.

Source: the original common-residual comparison in Section12.6 and
Aschbacher--Smith Proposition 1.2.1, printed pp.503--505.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsResidualStar
variable {G : Type*} [Group G]

/-- The exact kernel and full star image, through the literal inclusion and
quotient, when the intrinsic two-core is killed by the ambient quotient. -/
theorem star_quotient_equiv_of_core_le
    (H J : Subgroup G) (hJH : J ≤ H) (hc : J.pCoreIn 2 ≤ H.pCoreIn 2) :
    ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hJH)).ker = pCore 2 J ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Nonabelian.Setup.star H J) := by
  let f := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hJH)
  have hk2 : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hJH)
  have hk : f.ker = pCore 2 J := by
    have hle : f.ker ≤ pCore 2 J := le_sSup ⟨inferInstance,hk2⟩
    apply le_antisymm hle
    intro x hx
    obtain ⟨y,hy,he⟩ := hc (mem_map_of_mem J.subtype hx)
    change QuotientGroup.mk' (pCore 2 H) (inclusion hJH x) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    have hxy : inclusion hJH x = y := Subtype.ext he.symm
    rwa [hxy]
  have hr : f.range = Nonabelian.Setup.star H J := by
    simp only [f,MonoidHom.range_comp,inclusion_range,Nonabelian.Setup.star]
  exact ⟨hk,⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hr))⟩⟩

/-- The exact A5 star image retains the original local-family membership
relative to the image of the actual full ambient Sylow subgroup. -/
theorem star_five_mem_localCComponents [Finite G]
    (H J : Subgroup G) (P : Sylow 2 G) (hPH : (P : Subgroup G) ≤ H)
    (hJ : J ∈ Chapter1.LIn H (P : Subgroup G))
    (hc : J.pCoreIn 2 ≤ H.pCoreIn 2)
    (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) :
    Nonempty (Nonabelian.Setup.star H J ≃* alternatingGroup (Fin 5)) ∧
      Nonabelian.Setup.star H J ∈ ChapterA.Section03.localCComponents
        ((P.subtype hPH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) := by
  obtain ⟨_,⟨d⟩⟩ := star_quotient_equiv_of_core_le H J hJ.1 hc
  refine ⟨⟨d.symm.trans e⟩,?_⟩
  have hlocal := Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents
    ((Chapter1.mem_LIn_iff_subgroupOf hPH hJ.1).mp hJ)
  simpa only [Nonabelian.Setup.star,Sylow.coe_mapSurjective,Sylow.coe_subtype] using hlocal

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsResidualStar
