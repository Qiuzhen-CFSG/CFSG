module
public import CFSG.Quasithin.ChapterF.Section09.Basic
public import CFSG.Quasithin.ChapterF.Section07.Geometry
public import CFSG.Quasithin.ChapterF.Section07.LocalCores
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The F.7.6 specialization in F.9.2(4)

The Sylow supplement to the two-residual identifies the full point normalizer
in LT with L₁T, and hence with LT ∩ H. Characteristic two passes from L to
its extension by T. Reducedness identifies the two-core of C_LT(V) with that
of LT, giving the literal centralizer hypothesis of F.7.6.

The final two applications use the actual F.7 local cores and coset geometry:
the local kernel has the asserted odd-index residual, and the coset action
has trivial kernels at a uniform positive radius. No track theorem is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.2(4), printed p.318, and F.7.1,6–7, printed pp.311–312.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
namespace Hypothesis
variable (h : D.Hypothesis)
include h

private theorem pointNormalizer_L_le_local : D.L ⊓ D.Gz ≤ D.L₁ ⊔ (D.T : Subgroup G) := by
  let N := D.L.subgroupOf D.LT
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.L.le_normalizer h.normalizes_L)
  let P : Sylow 2 D.LT := D.T.subtype le_sup_right
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal N
  let e : N ≃* D.L := subgroupOfEquivOfLe (show D.L ≤ D.LT from le_sup_left)
  let R : Sylow 2 D.L := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRT : (R : Subgroup D.L).map D.L.subtype ≤ (D.T : Subgroup G) := by
    rintro _ ⟨l, hl, rfl⟩
    change l ∈ (Q : Subgroup N).map e.toMonoidHom at hl
    obtain ⟨q, hq, rfl⟩ := hl
    have hqp : (q : D.LT) ∈ P := by
      rw [hQ] at hq
      exact hq
    exact hqp
  let A := D.L ⊓ D.Gz
  let B := A.subgroupOf D.L
  have hRB : (R : Subgroup D.L) ≤ B := by
    intro l hl
    exact ⟨l.property, h.normalizer_point_eq ▸
      h.normalizes_point (hRT (mem_map_of_mem D.L.subtype hl))⟩
  let RB : Sylow 2 B := R.subtype hRB
  let eB : B ≃* A := subgroupOfEquivOfLe (show A ≤ D.L from inf_le_left)
  let RA : Sylow 2 A := RB.mapSurjective (f := eB.toMonoidHom) eB.surjective
  have hRA : (RA : Subgroup A).map A.subtype ≤ (D.T : Subgroup G) := by
    rintro _ ⟨a, ha, rfl⟩
    change a ∈ (RB : Subgroup B).map eB.toMonoidHom at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact hRT (mem_map_of_mem D.L.subtype (show (b : D.L) ∈ R from hb))
  have hs := congrArg (fun X : Subgroup A => X.map A.subtype)
    (pResidual_sup_sylow_eq_top RA)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hs
  change A ≤ D.L₁ ⊔ (D.T : Subgroup G)
  rw [← hs]
  exact sup_le le_sup_left (hRA.trans le_sup_right)

theorem normalizer_point_LT_eq :
    D.LT ⊓ normalizer (D.V₁ : Set G) = D.L₁ ⊔ (D.T : Subgroup G) := by
  rw [h.normalizer_point_eq]
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (D.L : Set G) * ((D.T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left D.L (D.T : Subgroup G) h.normalizes_L]
      exact hx.1
    obtain ⟨l, hl, t, ht, rfl⟩ := hx'
    have htG : t ∈ D.Gz := h.normalizer_point_eq ▸ h.normalizes_point ht
    have hlG : l ∈ D.Gz := by
      simpa only [mul_inv_cancel_right] using D.Gz.mul_mem hx.2 (D.Gz.inv_mem htG)
    exact (D.L₁ ⊔ (D.T : Subgroup G)).mul_mem
      (h.pointNormalizer_L_le_local ⟨hl, hlG⟩) (mem_sup_right ht)
  · exact sup_le
      (le_inf ((map_subtype_le _).trans (inf_le_left.trans le_sup_left))
        ((map_subtype_le _).trans inf_le_right))
      (le_inf le_sup_right (h.normalizer_point_eq ▸ h.normalizes_point))

theorem LT_inf_H_eq : D.LT ⊓ D.H = D.L₁ ⊔ (D.T : Subgroup G) := by
  apply le_antisymm
  · rw [← h.normalizer_point_LT_eq]
    exact inf_le_inf_left _ (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  · exact le_inf (h.normalizer_point_LT_eq.symm.le.trans inf_le_left) h.local_le

theorem characteristic_LT : generalizedFitting D.LT = pCore 2 D.LT := by
  have hc : centralizer (pCore 2 D.L : Set D.L) ≤ pCore 2 D.L := by
    simpa only [h.characteristic_L] using centralizer_generalizedFitting_le D.L
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (centralizer_pCore_sup_le 2 D.L (D.T : Subgroup G) hc D.T.isPGroup' h.normalizes_L)

theorem sylow_centralizer_LT :
    (D.T.subtype (show (D.T : Subgroup G) ≤ D.LT from le_sup_right) : Subgroup D.LT) ⊓
      centralizer (D.V.subgroupOf D.LT : Set D.LT) =
      (centralizer (D.V.subgroupOf D.LT : Set D.LT)).pCoreIn 2 := by
  rw [AmalgamLocalCores.reduced_centralizer_core _ h.reduced]
  apply map_injective D.LT.subtype_injective
  rw [Subgroup.map_inf _ _ _ D.LT.subtype_injective]
  change ((D.T : Subgroup G).subgroupOf D.LT).map D.LT.subtype ⊓ _ = _
  rw [map_subgroupOf_eq_of_le (show (D.T : Subgroup G) ≤ D.LT from le_sup_right)]
  change (D.T : Subgroup G) ⊓ _ = D.LT.pCoreIn 2
  rw [← h.sylow_centralizer]
  apply le_antisymm
  · rintro x ⟨ht, y, hy, rfl⟩
    refine ⟨ht, fun v hv => ?_⟩
    exact congrArg Subtype.val (hy ⟨v, h.V_le_LT hv⟩ hv)
  · rintro x ⟨ht, hc⟩
    refine ⟨ht, ⟨x, mem_sup_right ht⟩, ?_, rfl⟩
    intro v hv
    exact Subtype.ext (hc v hv)

/-- Every original F.7.6 input, on the literal vertex groups LT and H. -/
theorem lemma_F_9_2_four :
    generalizedFitting D.LT = pCore 2 D.LT ∧
    (∃ P : Sylow 2 (D.LT ⊓ D.H : Subgroup G),
      (P : Subgroup (D.LT ⊓ D.H : Subgroup G)).map (D.LT ⊓ D.H).subtype =
        (D.T : Subgroup G)) ∧
    (∃ P : Sylow 2 D.LT, (P : Subgroup D.LT).map D.LT.subtype = (D.T : Subgroup G)) ∧
    (∃ P : Sylow 2 D.H, (P : Subgroup D.H).map D.H.subtype = (D.T : Subgroup G)) ∧
    pCore 2 (D.LT ⊔ D.H : Subgroup G) = ⊥ ∧
    IsPReduced 2 (D.V.subgroupOf D.LT) ∧
    ((D.T : Subgroup G).subgroupOf D.LT ⊓ centralizer (D.V.subgroupOf D.LT : Set D.LT) =
      (centralizer (D.V.subgroupOf D.LT : Set D.LT)).pCoreIn 2) ∧
    D.LT ⊓ D.H = D.L₁ ⊔ (D.T : Subgroup G) := by
  refine ⟨h.characteristic_LT, ?_, ?_, ?_, h.generated_core, h.reduced,
    h.sylow_centralizer_LT, h.LT_inf_H_eq⟩
  · exact ⟨D.T.subtype (le_inf le_sup_right h.T_le_H),
      map_subgroupOf_eq_of_le (le_inf le_sup_right h.T_le_H)⟩
  · exact ⟨D.T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩
  · exact ⟨D.T.subtype h.T_le_H, map_subgroupOf_eq_of_le h.T_le_H⟩

/-- The local-core consumer uses the actual centralizer and odd-index residual. -/
theorem local_core_LT :
    (primeToResidual 2 (centralizer (D.V.subgroupOf D.LT : Set D.LT))).map
      (D.LT.subtype.comp (centralizer (D.V.subgroupOf D.LT : Set D.LT)).subtype) =
        (AmalgamLocalCores.localKernel D.LT (D.LT ⊓ D.H)).pCoreIn 2 ∧
    (AmalgamLocalCores.localKernel D.LT (D.LT ⊓ D.H)).pCoreIn 2 = D.LT.pCoreIn 2 := by
  apply LocalCores.lemma_F_7_7_one D.LT D.H (D.V.subgroupOf D.LT) h.reduced
    (D.T.subtype le_sup_right) _ h.sylow_centralizer_LT
  change ((D.T : Subgroup G).subgroupOf D.LT).map D.LT.subtype ≤ D.H
  rw [map_subgroupOf_eq_of_le (show (D.T : Subgroup G) ≤ D.LT from le_sup_right)]
  exact h.T_le_H

/-- The genuine coset geometry is faithful and has uniformly trivial finite-radius kernels. -/
theorem geometry_finite_radius :
    ∃ n : ℕ, 0 < n ∧ ∀ v : Section07.Geometry.Vertex D.LT D.H,
      Section07.Geometry.ballKernel D.LT D.H v n = ⊥ := by
  apply Section07.Geometry.uniform_trivial_ballKernel_of_ambientKernel_eq_bot
  exact LocalCores.lemma_F_7_3_eight_algebra D.LT D.H
    (Section07.Geometry.ambientKernel D.LT D.H)
    ((Section07.Geometry.ambientKernel_le D.LT D.H).trans inf_le_left)
    ((Section07.Geometry.ambientKernel_le D.LT D.H).trans inf_le_right)
    (Section07.Geometry.ambientKernel_normal_left D.LT D.H)
    (Section07.Geometry.ambientKernel_normal_right D.LT D.H)
    h.characteristic_LT h.generated_core

end Hypothesis
end CFSG.Quasithin.ChapterF.Section09.Setup
