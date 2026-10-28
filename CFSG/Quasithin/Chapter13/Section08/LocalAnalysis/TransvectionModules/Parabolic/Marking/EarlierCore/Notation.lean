module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.CoreBounds
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Relative normalizers in the ordinary A₆ case

The two definitions of Lᵢ in Notations 13.2.1 and 13.3.3 agree: adjoining
the normalizing two-group T to N_L(Vᵢ) leaves its two-residual unchanged.
The proof uses the two-group quotient and idempotence of finite residuals;
neither relative normalizer is assumed normal in the ambient group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.877 and 885. These identities apply before the local conclusions
of 13.5.4 and the calculation on p.948 in 13.8.6.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

/-- The ambient image of O²(X). -/
def residual (X : Subgroup G) : Subgroup G := (pResidual 2 X).map X.subtype

/-- The definition from Notation 13.3.3, using N_L(X). -/
def localResidual (L X : Subgroup G) : Subgroup G :=
  residual (L ⊓ normalizer (X : Set G))

/-- The actual subgroup product in 13.5.4, expressed as a join. The product
interpretation requires normalization, proved separately below. -/
def localI (L V₁ V₂ : Subgroup G) : Subgroup G :=
  (normalizer (V₁ : Set G)).pCoreIn 2 ⊔ localResidual L V₂

theorem residual_le (X : Subgroup G) : residual X ≤ X := map_subtype_le _

theorem localResidual_le (L X : Subgroup G) : localResidual L X ≤ L :=
  (residual_le _).trans inf_le_left

theorem normalizer_le_residual_normalizer (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (residual X : Set G) :=
  normalizer_le_normalizer_characteristic_image X (pResidual 2 X)

/-- T-invariance of L and X gives T-invariance of the relative residual. -/
theorem normalizes_localResidual (L T X : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) (hTX : T ≤ normalizer (X : Set G)) :
    T ≤ normalizer (localResidual L X : Set G) :=
  ((le_inf hTL (hTX.trans (normalizer (X : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans (normalizer_le_residual_normalizer _)

/-- A normalizing two-group does not change the residual, even when the
original subgroup itself is not two-perfect. -/
theorem residual_sup_twoGroup [Finite G] (N T : Subgroup G)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (N : Set G)) :
    residual (N ⊔ T) = residual N := by
  let M := N ⊔ T
  let N' := N.subgroupOf M
  let _ : N'.Normal := normal_subgroupOf_of_le_normalizer (sup_le N.le_normalizer hn)
  have hgen : N' ⊔ T.subgroupOf M = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hp : IsPGroup 2 (M ⧸ N') :=
    isPGroup_quotient_of_sup_eq_top N' _ hT.comap_subtype hgen
  have hr : residual M ≤ N := by
    have hh : pResidual 2 M ≤ N' := sInf_le ⟨inferInstance, hp⟩
    rintro x ⟨y, hy, rfl⟩
    exact hh hy
  have hid : residual (residual M) = residual M := by
    unfold residual
    rw [(pResidual_eq_top_iff 2 _).mpr (isPPerfect_embedded_pResidual 2 M),
      ← MonoidHom.range_eq_map, range_subtype]
  exact le_antisymm (hid ▸ embedded_pResidual_mono 2 hr)
    (embedded_pResidual_mono 2 le_sup_left)

/-- The actual relative normalizer in LT is N_L(X)T. -/
theorem relative_normalizer_sup (L T X : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) (hTX : T ≤ normalizer (X : Set G)) :
    (L ⊔ T) ⊓ normalizer (X : Set G) = (L ⊓ normalizer (X : Set G)) ⊔ T := by
  apply le_antisymm
  · intro x hx
    have hm : x ∈ (L : Set G) * (T : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L T hTL]
      exact hx.1
    obtain ⟨l, hl, t, ht, rfl⟩ := hm
    have hln : l ∈ normalizer (X : Set G) := by
      have hh := (normalizer (X : Set G)).mul_mem hx.2
        ((normalizer (X : Set G)).inv_mem (hTX ht))
      simpa only [mul_inv_cancel_right] using hh
    exact ((L ⊓ normalizer (X : Set G)) ⊔ T).mul_mem
      ((show L ⊓ normalizer (X : Set G) ≤ _ from le_sup_left) ⟨hl, hln⟩)
      ((show T ≤ _ from le_sup_right) ht)
  · exact sup_le (inf_le_inf le_sup_left le_rfl) (le_inf le_sup_right hTX)

/-- Notations 13.2.1 and 13.3.3 define the same subgroup, not just
isomorphic quotients. -/
theorem residual_relative_normalizer_eq [Finite G] (L T X : Subgroup G)
    (hT : IsPGroup 2 T) (hTL : T ≤ normalizer (L : Set G))
    (hTX : T ≤ normalizer (X : Set G)) :
    residual ((L ⊔ T) ⊓ normalizer (X : Set G)) = localResidual L X := by
  rw [relative_normalizer_sup L T X hTL hTX]
  apply residual_sup_twoGroup _ T hT
  exact (le_inf hTL (hTX.trans (normalizer (X : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- The source join really is the set product O₂(G₁)L₂ once O₂(G₁)
normalizes L₂. In the source this follows from L₂ normal in G₂; L₂ need
not normalize V₁. -/
theorem localI_coe_eq_product (L V₁ V₂ : Subgroup G)
    (hn : (normalizer (V₁ : Set G)).pCoreIn 2 ≤
      normalizer (localResidual L V₂ : Set G)) :
    (localI L V₁ V₂ : Set G) =
      ((normalizer (V₁ : Set G)).pCoreIn 2 : Set G) * (localResidual L V₂ : Set G) := by
  exact coe_mul_of_left_le_normalizer_right _ _ hn

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore

end
