module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeDefs
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOpposite
public import Theory.GroupTheory.PCoreImage

/-!
# The residual quotient in the faithful cubic-span action

The original local kernel condition and the normal-span identity give
C_H(U_H/⟨z⟩) = O₂(H). Restriction of the centralizer-span action to H has
kernel contained in this two-core. For any subgroup K of H normalized by
C_G(z), relative normality gives the reverse inclusion on O₂(K), so the
restriction kernel is exactly O₂(K).

The resulting first-isomorphism equivalence identifies K/O₂(K) with the
literal image of K in the faithful action. Its representative formula
retains the projection used in the source component and diagram arguments.
Source: Aschbacher--Smith 5.1.23, printed pp.645--646 of `refs/quasithin.pdf`.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin
open CFSG.Quasithin.Chapter6.Source.RankOneGeneric


namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H C : Subgroup G} {z : G}

theorem LocalData.local_projection_kernel (d : LocalData T H C z) :
    (SpanAction.projection d.g2).ker = pCore 2 H := by
  apply le_antisymm ?_ (SpanAction.core_le_projection_kernel d.g2)
  intro x hx
  apply d.kernel_core
  change x ∈ (ChapterF.Section08.Setup.quotientCentralizer
    (setup T H C z) d.g2.H_le (setup T H C z).V).normalCore
  rw [← ChapterF.Section08.Setup.quotientCentralizer_span
    (setup T H C z) d.g2.H_le (d.g2.V_le_T.trans (le_sup_right.trans d.g2.local_le))]
  apply (ChapterF.Section08.Setup.mem_quotientCentralizer_iff
    (setup T H C z) d.g2.H_le _ (d.g2.U_le_H.trans d.g2.H_le) x).mpr
  exact (SpanAction.projection_eq_one_iff d.g2 x).mp hx

theorem LocalData.restriction_kernel_le (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (hHC : H ≤ centralizer ({z} : Set G)) :
    ((SpanAction.projection s).comp (inclusion hHC)).ker ≤ pCore 2 H := by
  rw [← d.local_projection_kernel]
  intro x hx
  apply (SpanAction.projection_eq_one_iff d.g2 x).mpr
  intro u hu
  exact (SpanAction.projection_eq_one_iff s (inclusion hHC x)).mp hx u
    (conjugateSpanBy_mono le_rfl hHC hu)

theorem LocalData.normal_subgroup_kernel (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (hHC : H ≤ centralizer ({z} : Set G))
    (K : Subgroup G) (hKH : K ≤ H)
    (hn : centralizer ({z} : Set G) ≤ normalizer (K : Set G)) :
    ((SpanAction.projection s).comp (inclusion (hKH.trans hHC))).ker = pCore 2 K := by
  let f := (SpanAction.projection s).comp (inclusion (hKH.trans hHC))
  apply le_antisymm
  · have hker : f.ker ≤ (pCore 2 H).comap (inclusion hKH) := by
      intro x hx
      exact d.restriction_kernel_le s hHC (show inclusion hKH x ∈
        ((SpanAction.projection s).comp (inclusion hHC)).ker from hx)
    exact le_sSup ⟨inferInstance,
      ((pCore_isPGroup (p := 2) (G := H)).comap_of_injective
        (inclusion hKH) (inclusion_injective hKH)).to_le hker⟩
  · intro x hx
    apply SpanAction.core_le_projection_kernel s
    have hsub := pCoreIn_mono_of_normalizes (p := 2) (hKH.trans hHC) hn
    have hm := hsub (mem_map_of_mem K.subtype hx)
    obtain ⟨y,hy,he⟩ := hm
    exact (Subtype.ext he : y = inclusion (hKH.trans hHC) x) ▸ hy

@[expose] noncomputable def LocalData.normalSubgroupQuotientEquiv (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (hHC : H ≤ centralizer ({z} : Set G))
    (K : Subgroup G) (hKH : K ≤ H)
    (hn : centralizer ({z} : Set G) ≤ normalizer (K : Set G)) :
    K ⧸ pCore 2 K ≃* (K.subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s) :=
  (QuotientGroup.quotientMulEquivOfEq (d.normal_subgroup_kernel s hHC K hKH hn).symm).trans
    ((QuotientGroup.quotientKerEquivRange
      ((SpanAction.projection s).comp (inclusion (hKH.trans hHC)))).trans
        (MulEquiv.subgroupCongr (by
          ext y
          constructor
          · rintro ⟨k,rfl⟩
            exact ⟨inclusion (hKH.trans hHC) k,k.property,rfl⟩
          · rintro ⟨k,hk,rfl⟩
            exact ⟨⟨k,hk⟩,rfl⟩)))

@[simp] theorem LocalData.normalSubgroupQuotientEquiv_apply (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (hHC : H ≤ centralizer ({z} : Set G))
    (K : Subgroup G) (hKH : K ≤ H)
    (hn : centralizer ({z} : Set G) ≤ normalizer (K : Set G)) (k : K) :
    (d.normalSubgroupQuotientEquiv s hHC K hKH hn (QuotientGroup.mk' (pCore 2 K) k) :
      SpanAction.Actor s) = SpanAction.projection s (inclusion (hKH.trans hHC) k) := rfl

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
