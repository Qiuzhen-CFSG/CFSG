module
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Maps

/-!
# Lifting binary star generation through the two-residual

The original star kernel lies in T and normalizes both U and Uᵍ.
Equality of the star images therefore makes I normal in LU, with
2-group quotient. The hypothesis L=O²(L) forces L into I. This proves
I=LU, both as a join and as a subgroup product, without changing g.
Only the star-image generation calculation remains an explicit input.

Source: Aschbacher–Smith, G.2.3(2), printed p.333.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

theorem BaseHypothesis.binary_core_normalizes_conjugate (h : D.BaseHypothesis) {g : G} (hg : g ∈ D.LT) :
    D.LT.pCoreIn 2 ≤ normalizer (conjugate D.U g : Set G) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hc : (g * (z : G) * g⁻¹) ∈ D.LT.pCoreIn 2 := by
    exact mem_map.mpr ⟨⟨g, hg⟩ * z * (⟨g, hg⟩ : D.LT)⁻¹,
      (inferInstance : (pCore 2 D.LT).Normal).conj_mem z hz ⟨g, hg⟩, rfl⟩
  have hn := h.binary_T_normalizes_U (h.binary_core_le_T hc)
  apply (le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
  refine mem_map.mpr ⟨g * (z : G) * g⁻¹, hn, ?_⟩
  change g⁻¹ * (g * (z : G) * g⁻¹) * (g⁻¹)⁻¹ = z
  group

theorem binary_I_eq_join_of_star_eq (h : D.BaseHypothesis) (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L)
    (hi : D.star (D.I g) = D.star (D.L ⊔ D.U)) : D.I g = D.L ⊔ D.U := by
  let K := D.L ⊔ D.U
  have hK : K ≤ D.LT := binary_join_le_LT hUT
  have hIK : D.I g ≤ K := binary_I_le_join hgL
  let q := D.binaryStarRestriction K hK
  let J := (D.I g).subgroupOf K
  have hqQ : q.ker.map K.subtype ≤ D.LT.pCoreIn 2 := by
    rintro x ⟨k, hk, rfl⟩
    exact ⟨inclusion hK k, (QuotientGroup.eq_one_iff _).mp hk, rfl⟩
  have hQN : q.ker.map K.subtype ≤ normalizer (D.I g : Set G) := by
    refine hqQ.trans ?_
    exact (le_inf (h.binary_core_le_T.trans h.binary_T_normalizes_U)
      (BaseHypothesis.binary_core_normalizes_conjugate h ((show D.L ≤ D.LT from le_sup_left) hgL))).trans
      (normalizer_inf_normalizer_le_normalizer_sup D.U (conjugate D.U g))
  have hqJ : q.ker ≤ normalizer (J : Set K) := by
    apply (le_normalizer_comap K.subtype).trans'
    intro x hx
    exact hQN (mem_map_of_mem K.subtype hx)
  have himage : J.map q = q.range := by
    change ((D.I g).subgroupOf K).map (D.binaryStarRestriction K hK) = _
    rw [binaryStarRestriction_map _ _ _ hIK, binaryStarRestriction_range, hi]
  have hcover : J ⊔ q.ker = ⊤ := by
    have hc := congrArg (fun A => A.comap q) himage
    simpa only [comap_map_eq, MonoidHom.comap_range_self] using hc
  have hJn : J.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hcover]
    exact sup_le J.le_normalizer hqJ
  let := hJn
  have hp : IsPGroup 2 (K ⧸ J) := isPGroup_quotient_of_sup_eq_top J q.ker
    (binaryStarRestriction_ker_isPGroup K hK) hcover
  let f : D.L →* K ⧸ J := (QuotientGroup.mk' J).comp (inclusion le_sup_left)
  have hf : f = 1 := ((pResidual_eq_top_iff 2 D.L).mp h.residual).hom_eq_one_of_isPGroup hp f
  have hLI : D.L ≤ D.I g := by
    intro l hl
    apply (QuotientGroup.eq_one_iff (N := J) (inclusion (show D.L ≤ K from le_sup_left) ⟨l, hl⟩)).mp
    exact DFunLike.congr_fun hf ⟨l, hl⟩
  exact le_antisymm hIK (sup_le hLI le_sup_left)

theorem binary_I_product_of_star_eq (h : D.BaseHypothesis) (hUT : D.U ≤ D.T)
    (g : G) (hgL : g ∈ D.L)
    (hi : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) := by
  rw [binary_I_eq_join_of_star_eq h hUT g hgL hi]
  exact (coe_mul_of_right_le_normalizer_left D.L D.U
    (hUT.trans h.T_normalizes_L))
end CFSG.Quasithin.ChapterG.Section02.Setup
