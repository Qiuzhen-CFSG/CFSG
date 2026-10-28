module
public import CFSG.Quasithin.ChapterF.Section08.Closure
public import CFSG.Quasithin.ChapterF.Section07.Geometry
public import CFSG.Quasithin.ChapterF.Section07.LocalCores
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The F.7 specialization of the original F.8 setup

The Sylow supplement to the two-residual identifies the full point normalizer
in LT with L₁T, and hence with LT ∩ H. Characteristic two passes from L to
its extension by T. Reducedness identifies the two-core of C_LT(V) with that
of LT, giving the literal centralizer hypothesis of F.7.6.

The normalizer argument follows the same Sylow-supplement proof as the
F.9.2(4) specialization, here without an order-two restriction on V₁.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.8.3, printed p.316, and F.7.1,6–7, printed pp.311–312.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Section08.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
namespace Hypothesis
variable (h : D.Hypothesis)
include h

private theorem pointNormalizer_L_le_local : D.L ⊓ D.G₁ ≤ D.L₁ ⊔ D.T := by
  let N := D.L.subgroupOf D.LT
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.L.le_normalizer h.T_normalizes_L)
  obtain ⟨S, hS⟩ := h.sylow
  let P : Sylow 2 D.LT := S.subtype (hS ▸ le_sup_right)
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal N
  let e : N ≃* D.L := subgroupOfEquivOfLe (show D.L ≤ D.LT from le_sup_left)
  let R : Sylow 2 D.L := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRT : (R : Subgroup D.L).map D.L.subtype ≤ D.T := by
    rintro _ ⟨l, hl, rfl⟩
    change l ∈ (Q : Subgroup N).map e.toMonoidHom at hl
    obtain ⟨q, hq, rfl⟩ := hl
    have hqp : (q : D.LT) ∈ P := by
      rw [hQ] at hq
      exact hq
    exact hS ▸ hqp
  let A := D.L ⊓ D.G₁
  let B := A.subgroupOf D.L
  have hRB : (R : Subgroup D.L) ≤ B := by
    intro l hl
    exact ⟨l.property, h.T_normalizes_point (hRT (mem_map_of_mem D.L.subtype hl))⟩
  let RB : Sylow 2 B := R.subtype hRB
  let eB : B ≃* A := subgroupOfEquivOfLe (show A ≤ D.L from inf_le_left)
  let RA : Sylow 2 A := RB.mapSurjective (f := eB.toMonoidHom) eB.surjective
  have hRA : (RA : Subgroup A).map A.subtype ≤ D.T := by
    rintro _ ⟨a, ha, rfl⟩
    change a ∈ (RB : Subgroup B).map eB.toMonoidHom at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact hRT (mem_map_of_mem D.L.subtype (show (b : D.L) ∈ R from hb))
  have hs := congrArg (fun X : Subgroup A => X.map A.subtype)
    (pResidual_sup_sylow_eq_top RA)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hs
  change A ≤ D.L₁ ⊔ D.T
  rw [← hs]
  exact sup_le le_sup_left (hRA.trans le_sup_right)

theorem normalizer_point_LT_eq :
    D.LT ⊓ normalizer (D.V₁ : Set G) = D.L₁ ⊔ D.T := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (D.L : Set G) * (D.T : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left D.L D.T h.T_normalizes_L]
      exact hx.1
    obtain ⟨l, hl, t, ht, rfl⟩ := hx'
    have htG : t ∈ D.G₁ := h.T_normalizes_point ht
    have hlG : l ∈ D.G₁ := by
      simpa only [mul_inv_cancel_right] using D.G₁.mul_mem hx.2 (D.G₁.inv_mem htG)
    exact (D.L₁ ⊔ D.T).mul_mem
      (h.pointNormalizer_L_le_local ⟨hl, hlG⟩) (mem_sup_right ht)
  · exact sup_le
      (le_inf ((map_subtype_le _).trans (inf_le_left.trans le_sup_left))
        ((map_subtype_le _).trans inf_le_right))
      (le_inf le_sup_right (h.T_normalizes_point))

theorem LT_inf_H_eq : D.LT ⊓ D.H = D.L₁ ⊔ D.T := by
  apply le_antisymm
  · rw [← h.normalizer_point_LT_eq]
    exact inf_le_inf_left _ (h.H_le)
  · exact le_inf (h.normalizer_point_LT_eq.symm.le.trans inf_le_left) h.local_le

theorem characteristic_LT : generalizedFitting D.LT = pCore 2 D.LT := by
  obtain ⟨P, hP⟩ := h.sylow
  have hp : IsPGroup 2 D.T := hP ▸ P.isPGroup'
  have hc : centralizer (pCore 2 D.L : Set D.L) ≤ pCore 2 D.L := by
    simpa only [h.characteristic_L] using centralizer_generalizedFitting_le D.L
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (centralizer_pCore_sup_le 2 D.L D.T hc hp h.T_normalizes_L)

theorem sylow_centralizer_LT :
    D.T.subgroupOf D.LT ⊓ centralizer (D.V.subgroupOf D.LT : Set D.LT) =
      (centralizer (D.V.subgroupOf D.LT : Set D.LT)).pCoreIn 2 := by
  rw [AmalgamLocalCores.reduced_centralizer_core _ h.reduced]
  apply map_injective D.LT.subtype_injective
  rw [Subgroup.map_inf _ _ _ D.LT.subtype_injective,
    map_subgroupOf_eq_of_le (show D.T ≤ D.LT from le_sup_right)]
  change D.T ⊓ _ = D.LT.pCoreIn 2
  rw [← h.centralizer_eq]
  apply le_antisymm
  · rintro x ⟨ht, y, hy, rfl⟩
    refine ⟨ht, fun v hv => ?_⟩
    exact congrArg Subtype.val (hy ⟨v, h.V_le_LT hv⟩ hv)
  · rintro x ⟨ht, hc⟩
    refine ⟨ht, ⟨x, mem_sup_right ht⟩, ?_, rfl⟩
    intro v hv
    exact Subtype.ext (hc v hv)

/-- Every original F.7.6 input, on the literal vertex groups LT and H. -/
theorem lemma_F_8_3 :
    generalizedFitting D.LT = pCore 2 D.LT ∧
    (∃ P : Sylow 2 (D.LT ⊓ D.H : Subgroup G),
      (P : Subgroup (D.LT ⊓ D.H : Subgroup G)).map (D.LT ⊓ D.H).subtype =
        D.T) ∧
    (∃ P : Sylow 2 D.LT, (P : Subgroup D.LT).map D.LT.subtype = D.T) ∧
    (∃ P : Sylow 2 D.H, (P : Subgroup D.H).map D.H.subtype = D.T) ∧
    pCore 2 (D.LT ⊔ D.H : Subgroup G) = ⊥ ∧
    IsPReduced 2 (D.V.subgroupOf D.LT) ∧
    (D.T.subgroupOf D.LT ⊓ centralizer (D.V.subgroupOf D.LT : Set D.LT) =
      (centralizer (D.V.subgroupOf D.LT : Set D.LT)).pCoreIn 2) ∧
    D.LT ⊓ D.H = D.L₁ ⊔ D.T := by
  obtain ⟨P, hP⟩ := h.sylow
  have hTH : D.T ≤ D.H := le_sup_right.trans h.local_le
  refine ⟨h.characteristic_LT, ?_, ?_, ?_, h.generated_core, h.reduced,
    h.sylow_centralizer_LT, h.LT_inf_H_eq⟩
  · exact ⟨P.subtype (hP ▸ le_inf le_sup_right hTH),
      (map_subgroupOf_eq_of_le (hP ▸ le_inf le_sup_right hTH)).trans hP⟩
  · exact ⟨P.subtype (hP ▸ le_sup_right), (map_subgroupOf_eq_of_le (hP ▸ le_sup_right)).trans hP⟩
  · exact ⟨P.subtype (hP ▸ hTH), (map_subgroupOf_eq_of_le (hP ▸ hTH)).trans hP⟩

end Hypothesis
end CFSG.Quasithin.ChapterF.Section08.Setup
