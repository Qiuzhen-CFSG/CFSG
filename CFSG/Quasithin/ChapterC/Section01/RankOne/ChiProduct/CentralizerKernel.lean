module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.AmbientLift
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
/-!
# The exact centralizer kernel and normal generation in C.1.27

Once the ambient lift has U(L)≤V and characteristic two, its centralizer
of U(L) lies in O₂(L). Thus the kernel of the literal map from L to
G/C_G(V) is exactly O₂(L); the opposite inclusion uses subnormal core
inheritance and O₂(G)≤C_G(V). The resulting quotient equivalence retains
the actual subgroup image. Two-perfection lifts normal generation through
this two-group kernel, so the B.1.13 component commutator generates L.

Source: Aschbacher–Smith C.1.27, printed p.133. No irreducibility or
short-group conclusion is used to identify the kernel.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

/-- Once U(L) is supported on V, the literal centralizer quotient has
exactly the intrinsic two-core as kernel on the lifted group. -/
theorem core_eq_centralizer_quotient_kernel
    (V L : Subgroup G) [V.Normal] (hL : L.IsSubnormal)
    (hf : generalizedFitting L = pCore 2 L)
    (hU : (blockU L).map L.subtype ≤ V)
    (hQC : pCore 2 G ≤ centralizer (V : Set G)) :
    ((QuotientGroup.mk' (centralizer (V : Set G))).subgroupMap L).ker = pCore 2 L := by
  rw [ker_subgroupMap, QuotientGroup.ker_mk']
  apply le_antisymm
  · intro x hx
    apply centralizer_blockU_le_of_fitting hf
    intro u hu
    apply Subtype.ext
    exact hx (u : G) (hU (mem_map_of_mem L.subtype hu))
  · intro x hx
    exact hQC (pCoreIn_le_of_subnormal 2 hL (mem_map_of_mem L.subtype hx))

/-- The original core quotient is isomorphic to its actual image, not an
abstract copy of the selected component. -/
noncomputable def coreQuotientEquivCentralizerImage
    (V L : Subgroup G) [V.Normal] (hL : L.IsSubnormal)
    (hf : generalizedFitting L = pCore 2 L)
    (hU : (blockU L).map L.subtype ≤ V)
    (hQC : pCore 2 G ≤ centralizer (V : Set G)) :
    (L ⧸ pCore 2 L) ≃* L.map (QuotientGroup.mk' (centralizer (V : Set G))) :=
  (QuotientGroup.quotientMulEquivOfEq
    (core_eq_centralizer_quotient_kernel V L hL hf hU hQC).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk' (centralizer (V : Set G))).subgroupMap_surjective L))

omit [Finite G] in
/-- Normal generation in the actual quotient lifts through the proven
 two-core kernel because the original group is two-perfect. -/
theorem normal_generation_of_twoGroup_kernel
    {D : Type*} [Group D] (f : G →* D) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (hpG : IsPPerfect 2 G) (K : Subgroup G)
    (hgen : conjugateSpanBy (K.map f) ⊤ = ⊤) :
    conjugateSpanBy K ⊤ = ⊤ := by
  let N := conjugateSpanBy K ⊤
  let : N.Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (le_normalizer_conjugateSpanBy K ⊤))
  have hm : N.map f = ⊤ := by
    change (conjugateSpanBy K ⊤).map f = ⊤
    rw [map_conjugateSpanBy, map_top_of_surjective _ hf, hgen]
  have hs : N ⊔ f.ker = ⊤ := by
    rw [← comap_map_eq, hm, comap_top]
  have hn : pResidual 2 G ≤ N :=
    sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N f.ker hker hs⟩
  rw [(pResidual_eq_top_iff 2 G).mpr hpG] at hn
  exact top_unique hn

omit [Finite G] in
/-- The component-commutator conclusion in B.1.13 supplies the normal
 generation needed in the central-kernel lift. -/
theorem conjugateSpan_eq_top_of_commutator_top
    (K : Subgroup G) (hcomm : ⁅K, (⊤ : Subgroup G)⁆ = ⊤) :
    conjugateSpanBy K ⊤ = ⊤ := by
  apply top_unique
  calc
    ⊤ = ⁅K, (⊤ : Subgroup G)⁆ := hcomm.symm
    _ ≤ conjugateSpanBy K ⊤ := by
      rw [conjugateSpanBy_eq_iSup_conj]
      exact commutator_le_iSup_conjugates K ⊤

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
