module

public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.PResidual.NormalizedGenerators
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Residual generation in a Goldschmidt triple

The common Sylow two-subgroup normalizes both embedded local two-residuals
and supplements each inside its generator. Their join is two-perfect and
has two-group quotient, so it is the ambient two-residual. The same Sylow
supplement gives the literal product `G = O²(G)T`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.6, printed p.305 (1 March 2004 manuscript).
-/

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

public theorem IsGoldschmidtTriple.intersection_normalizes_left_residual
    (_h : IsGoldschmidtTriple G₁ G₂) :
    G₁ ⊓ G₂ ≤ normalizer ((pResidual 2 G₁).map G₁.subtype : Set G) := by
  have hn := (pResidual 2 G₁).le_normalizer_map G₁.subtype
  simp only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
  exact inf_le_left.trans hn

public theorem IsGoldschmidtTriple.left_residual_sup_intersection
    (h : IsGoldschmidtTriple G₁ G₂) :
    (pResidual 2 G₁).map G₁.subtype ⊔ (G₁ ⊓ G₂) = G₁ := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  have hle : (T : Subgroup G) ≤ G₁ := hT.symm.le.trans inf_le_left
  have hs := congrArg (fun K : Subgroup G₁ => K.map G₁.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hle))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hs
  have he : ((T.subtype hle : Sylow 2 G₁) : Subgroup G₁).map G₁.subtype = G₁ ⊓ G₂ := by
    change ((T : Subgroup G).subgroupOf G₁).map G₁.subtype = _
    rw [map_subgroupOf_eq_of_le hle, hT]
  rwa [he] at hs

public theorem IsGoldschmidtTriple.intersection_normalizes_right_residual
    (h : IsGoldschmidtTriple G₁ G₂) :
    G₁ ⊓ G₂ ≤ normalizer ((pResidual 2 G₂).map G₂.subtype : Set G) := by
  simpa only [inf_comm G₂ G₁] using h.symm.intersection_normalizes_left_residual

public theorem IsGoldschmidtTriple.right_residual_sup_intersection
    (h : IsGoldschmidtTriple G₁ G₂) :
    (pResidual 2 G₂).map G₂.subtype ⊔ (G₁ ⊓ G₂) = G₂ := by
  simpa only [inf_comm G₂ G₁] using h.symm.left_residual_sup_intersection

public theorem IsGoldschmidtTriple.left_residual_sup_right
    (h : IsGoldschmidtTriple G₁ G₂) :
    (pResidual 2 G₁).map G₁.subtype ⊔ G₂ = ⊤ := by
  calc
    _ = ((pResidual 2 G₁).map G₁.subtype ⊔ (G₁ ⊓ G₂)) ⊔ G₂ := by
      rw [sup_assoc, sup_eq_right.mpr (inf_le_right : G₁ ⊓ G₂ ≤ G₂)]
    _ = ⊤ := by rw [h.left_residual_sup_intersection, h.generated]

public theorem IsGoldschmidtTriple.twoResidual_eq_sup
    (h : IsGoldschmidtTriple G₁ G₂) :
    pResidual 2 G = (pResidual 2 G₁).map G₁.subtype ⊔
      (pResidual 2 G₂).map G₂.subtype := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  apply pResidual_eq_sup_of_normalized_generators _ _ (G₁ ⊓ G₂)
    (isPPerfect_embedded_pResidual 2 G₁) (isPPerfect_embedded_pResidual 2 G₂)
    (hT ▸ T.isPGroup') h.intersection_normalizes_left_residual
    h.intersection_normalizes_right_residual
  calc
    _ = ((pResidual 2 G₁).map G₁.subtype ⊔ (G₁ ⊓ G₂)) ⊔
        ((pResidual 2 G₂).map G₂.subtype ⊔ (G₁ ⊓ G₂)) := by rw [sup_sup_sup_comm, sup_idem]
    _ = ⊤ := by rw [h.left_residual_sup_intersection, h.right_residual_sup_intersection, h.generated]

public theorem IsGoldschmidtTriple.twoResidual_mul_intersection
    (h : IsGoldschmidtTriple G₁ G₂) :
    (pResidual 2 G : Set G) * ((G₁ ⊓ G₂ : Subgroup G) : Set G) = Set.univ := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  rw [hT, ← normal_mul, pResidual_sup_sylow_eq_top T]
  rfl

end CFSG.Quasithin.ChapterF
