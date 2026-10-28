module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized

/-!
# Original C.5.1–2 and the C.5.3 characteristic-subgroup reduction

We retain H, M₀, R, K = O²(H), and the original Sylow subgroup T_H as
literal subgroups of G. The only exclusion is C.5.2: no nontrivial subgroup
of R is normal in ⟨M₀,H⟩. Residual generation then shows that a nontrivial
characteristic subgroup of R cannot be normal in RK, the input to C.1.26.

Source: Aschbacher–Smith C.5.1–3, printed pp.154–155.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G]

/-- The group-theoretic hypotheses of C.5.1–2. Strong quasithinness and
the K-group hypothesis remain the separate ambient `IsSQTK` assumption. -/
structure OriginalHypotheses (H M K R T : Subgroup G) where
  fitting : generalizedFitting H = pCore 2 H
  sylow : Sylow 2 H
  sylow_image : (sylow : Subgroup H).map H.subtype = T
  unique : Order.HasUniqueMaximalOver (sylow : Subgroup H) ⊤
  residual : (pResidual 2 H).map H.subtype = K
  R_le : R ≤ T
  T_le : T ≤ M
  R_normal : M ≤ normalizer (R : Set G)
  residual_sylow : Sylow 2 (R ⊔ K : Subgroup G)
  residual_sylow_image :
    (residual_sylow : Subgroup (R ⊔ K : Subgroup G)).map (R ⊔ K).subtype = R
  no_common_normal : ∀ N : Subgroup G, N ≤ R →
    (N.subgroupOf (M ⊔ H)).Normal → N = ⊥

variable {H M K R T : Subgroup G} (d : OriginalHypotheses H M K R T)
include d

theorem OriginalHypotheses.T_le_H : T ≤ H := by
  rw [← d.sylow_image]
  exact map_subtype_le _

theorem OriginalHypotheses.K_le_H : K ≤ H := by
  rw [← d.residual]
  exact map_subtype_le _

theorem OriginalHypotheses.R_le_H : R ≤ H := d.R_le.trans d.T_le_H

theorem OriginalHypotheses.R_le_M : R ≤ M := d.R_le.trans d.T_le

theorem OriginalHypotheses.R_twoGroup : IsPGroup 2 R := by
  have ht : IsPGroup 2 T := d.sylow_image ▸ d.sylow.isPGroup'.map H.subtype
  exact ht.to_le d.R_le

variable [Finite G]

/-- O²(H) and the original Sylow subgroup generate H. -/
theorem OriginalHypotheses.residual_sup_sylow : K ⊔ T = H := by
  have h := congrArg (Subgroup.map H.subtype) (pResidual_sup_sylow_eq_top d.sylow)
  simpa only [Subgroup.map_sup, d.residual, d.sylow_image, ← MonoidHom.range_eq_map,
    H.range_subtype] using h

theorem OriginalHypotheses.H_le_residual_sup_M : H ≤ K ⊔ M := by
  rw [← d.residual_sup_sylow]
  exact sup_le_sup_left d.T_le _

omit [Finite G] in
theorem OriginalHypotheses.normalizes_residual : H ≤ normalizer (K : Set G) := by
  rw [← d.residual]
  have hn : (⊤ : Subgroup H) ≤ normalizer (pResidual 2 H : Set H) :=
    le_normalizer_of_normal
  have hm := (map_mono (f := H.subtype) hn).trans
    ((pResidual 2 H).le_normalizer_map H.subtype)
  simpa only [← MonoidHom.range_eq_map, H.range_subtype] using hm

/-- RK is normal in H, since T_H normalizes R and O²(H). -/
theorem OriginalHypotheses.residual_join_normal :
    ((R ⊔ K).subgroupOf H).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (sup_le d.R_le_H d.K_le_H)).mpr
  rw [← d.residual_sup_sylow]
  apply sup_le
  · exact le_sup_right.trans (R ⊔ K).le_normalizer
  · exact (le_inf (d.T_le.trans d.R_normal)
      (d.T_le_H.trans d.normalizes_residual)).trans
      (normalizer_inf_normalizer_le_normalizer_sup R K)

/-- The C.5.2 exclusion discharges the characteristic-subgroup hypothesis
of C.1.26 on the actual group RK. -/
theorem OriginalHypotheses.characteristic_not_normal (C : Subgroup R)
    [C.Characteristic] (hC : C ≠ ⊥) :
    ¬ ((C.map R.subtype).subgroupOf (R ⊔ K)).Normal := by
  intro hn
  have hCR : C.map R.subtype ≤ R := map_subtype_le _
  have hMR : M ≤ normalizer (C.map R.subtype : Set G) :=
    d.R_normal.trans (normalizer_le_normalizer_characteristic_image R C)
  have hKR : R ⊔ K ≤ normalizer (C.map R.subtype : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hCR.trans le_sup_left)).mp hn
  have hHN : H ≤ normalizer (C.map R.subtype : Set G) :=
    d.H_le_residual_sup_M.trans (sup_le (le_sup_right.trans hKR) hMR)
  have hnormal : ((C.map R.subtype).subgroupOf (M ⊔ H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hCR.trans (d.R_le_M.trans le_sup_left))).mpr
      (sup_le hMR hHN)
  have he := d.no_common_normal (C.map R.subtype) hCR hnormal
  exact hC ((map_injective R.subtype_injective) (by simpa only [Subgroup.map_bot] using he))

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
