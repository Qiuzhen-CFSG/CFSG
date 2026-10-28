module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FixedFreeImage
/-!
# The original short block in the ambient two-core quotient

The supplied full Sylow normalizes the original block, so reducedness
bounds [O₂(X),K] by U(K). The fixed-layer argument identifies its action
image with K/O₂(K). Characteristic two makes the canonical map from
X/O₂(X) injective on this actual image. The resulting equivalence retains
both quotient maps and applies to the fixed-free A₅ source of C.5.12.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem short_fixedFree_twoCore_image_equiv
    (K X V : Subgroup G) (hK : IsShort K)
    (hKX : K ≤ X) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U K ≤ V) [IsElementaryAbelian 2 V]
    (S : Sylow 2 X) (hSK : (S : Subgroup X).map X.subtype ≤ normalizer (K : Set G))
    (hr : IsPReduced 2 (V.subgroupOf X))
    (hchar : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (hz : blockFixed K = ⊥) :
    Nonempty ((K ⧸ pCore 2 K) ≃* (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) := by
  let : (V.subgroupOf X).Normal := hr.normal
  have hQK : X.pCoreIn 2 ≤ normalizer (K : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    exact hSK (mem_map_of_mem X.subtype (pCore_isPGroup.le_sylow_of_normal S hx))
  have hVQ : V ≤ X.pCoreIn 2 := by
    intro v hv
    exact mem_map_of_mem X.subtype (hr.le_pCore (show (⟨v,hVX hv⟩ : X) ∈ V.subgroupOf X from hv))
  have hQCV : X.pCoreIn 2 ≤ centralizer (V : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ v hv
    exact congrArg X.subtype (le_centralizer_iff.mp hr.le_centralizer_pCore hx ⟨v,hVX hv⟩ hv)
  have hQKcomm : ⁅X.pCoreIn 2,K⁆ ≤ U K := by
    rw [commutator_comm]
    exact block_fixer_displacement hK hQK (hQCV.trans (centralizer_le hUV))
  have hVK : ⁅V,K⁆ ≤ U K := (commutator_mono hVQ le_rfl).trans hQKcomm
  obtain ⟨eK⟩ := short_fixedFree_centralizer_image_equiv K X V hK hKX hVX hXV hUV hVK hz
  have hcK : ⁅pCore 2 X,K.subgroupOf X⁆ ≤ V.subgroupOf X := by
    apply map_le_map_iff_of_injective X.subtype_injective |>.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hVX]
    exact hQKcomm.trans hUV
  let r := QuotientGroup.mk' (pCore 2 X)
  let B := (K.subgroupOf X).map r
  let φ := twoCoreToCentralizer (V.subgroupOf X) hr
  have hi := twoCoreToCentralizer_component_injective (V.subgroupOf X) (K.subgroupOf X) hr hchar hcK
  let eB := (MulEquiv.ofBijective (φ.subgroupMap B) ⟨hi,φ.subgroupMap_surjective B⟩).trans
    (MulEquiv.subgroupCongr (twoCoreToCentralizer_image (V.subgroupOf X) (K.subgroupOf X) hr))
  exact ⟨eK.trans eB.symm⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
