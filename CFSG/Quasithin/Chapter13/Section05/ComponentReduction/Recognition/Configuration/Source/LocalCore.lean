module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Prefix
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.Actors
public import Theory.GroupTheory.NormalTwoThreeLayer

/-!
# The O₂,₃ step in the original marked configuration

The images of K,L₁,T_X generate the actual quotient X/C_X(K*). The latter
two centralize the marked involution. Consequently normalization of L̂₁ by
C_K̂(V̂) gives its normality in the full actor centralizer. The original
L₁/O₂(L₁) of order three then places L̂₁ in its actual O₂,₃.
The component-centralizer transport is the separate coprime-cover source step.
Source: Aschbacher–Smith13.5.21(ii), printed p.923.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- The literal marked images generate X̂. -/
theorem marked_images_generate : Khat s h ⊔ (L1hat s h ⊔ That s h) = ⊤ := by
  have hK : K ≤ X D K := le_sup_left
  have hL : D.L₁ ≤ X D K := le_sup_left.trans le_sup_right
  have hT : TX D K ≤ X D K := le_sup_right.trans le_sup_right
  change (K.subgroupOf (X D K)).map _ ⊔
    ((D.L₁.subgroupOf (X D K)).map _ ⊔ ((TX D K).subgroupOf (X D K)).map _) = ⊤
  rw [← Subgroup.map_sup,← Subgroup.map_sup,← subgroupOf_sup hL hT,
    ← subgroupOf_sup hK (sup_le hL hT)]
  change ((X D K).subgroupOf (X D K)).map _ = ⊤
  rw [subgroupOf_self,← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

/-- The original residual image centralizes the marked actor. -/
theorem marked_local_centralizes (hi : D.Vplus.relIndex D.V = 2)
    (hu : ¬ IsMulCommutative D.UH) (hv : D.V ≤ X D K) :
    L1hat s h ≤ centralizer (Vhat s h : Set (Xhat s h)) := by
  have hl : D.L₁ ≤ normalizer (D.V : Set G) := by
    intro x hx
    exact (h.normalizer_control ⟨h.local_le (mem_sup_left hx),
      h.local_normalizes (mem_sup_left hx)⟩).2
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact markedImage_commutator_eq_bot s h D.L₁ D.V
    (le_sup_left.trans le_sup_right) hv
    (commutator_eq_bot_iff_le_centralizer.mpr (Fitting.star_centralizes_V D h hi hu D.L₁ hl))

/-- Original T_X normalizes the same marked residual. -/
theorem marked_sylow_normalizes_local :
    That s h ≤ normalizer (L1hat s h : Set (Xhat s h)) := by
  have hn : (TX D K).subgroupOf (X D K) ≤
      normalizer (D.L₁.subgroupOf (X D K) : Set (X D K)) := by
    rw [← subgroupOf_normalizer_eq (show D.L₁ ≤ X D K from le_sup_left.trans le_sup_right)]
    exact comap_mono (inf_le_left.trans (local_residual_normalized D h))
  exact (map_mono hn).trans (le_normalizer_map _)

/-- Component centralizer normalization extends to the full actor centralizer. -/
theorem marked_centralizer_normalizes_local (Y : Subgroup G) (p : Prefix s h Y)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hv : D.V ≤ X D K)
    (hk : Khat s h ⊓ centralizer (Vhat s h : Set (Xhat s h)) ≤
      normalizer (L1hat s h : Set (Xhat s h))) :
    centralizer (Vhat s h : Set (Xhat s h)) ≤ normalizer (L1hat s h : Set (Xhat s h)) := by
  let C := centralizer (Vhat s h : Set (Xhat s h))
  let A := L1hat s h ⊔ That s h
  let : (Khat s h).Normal := by rw [←p.khat_fitting]; infer_instance
  have hAC : A ≤ C := sup_le (marked_local_centralizes s h hi hu hv)
    (le_centralizer_iff.mp p.actor_central)
  have hAN : A ≤ normalizer (L1hat s h : Set (Xhat s h)) :=
    sup_le (L1hat s h).le_normalizer (marked_sylow_normalizes_local s h)
  intro x hx
  have hx' : x ∈ Khat s h ⊔ A := (marked_images_generate s h).symm ▸ mem_top x
  obtain ⟨k,hkK,a,ha,rfl⟩ := mem_sup_of_normal_left.mp hx'
  have hkC : k ∈ C := by
    have hh := C.mul_mem hx (C.inv_mem (hAC ha))
    simpa only [mul_inv_cancel_right] using hh
  exact (normalizer (L1hat s h : Set (Xhat s h))).mul_mem (hk ⟨hkK,hkC⟩) (hAN ha)

/-- The original local order-three quotient supplies O₂,₃ after the normalizer step. -/
theorem source_local_core_condition (Y : Subgroup G) (p : Prefix s h Y)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hv : D.V ≤ X D K) (hc : Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3)
    (hk : Khat s h ⊓ centralizer (Vhat s h : Set (Xhat s h)) ≤
      normalizer (L1hat s h : Set (Xhat s h))) : LocalCoreCondition s h := by
  let C := centralizer (Vhat s h : Set (Xhat s h))
  let B := (L1hat s h).subgroupOf C
  have hLC : L1hat s h ≤ C := marked_local_centralizes s h hi hu hv
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (marked_centralizer_normalizes_local s h Y p hi hu hv hk)
  let q := QuotientGroup.mk' (componentCentralizer s h)
  let e := (subgroupOfEquivOfLe (show D.L₁ ≤ X D K from le_sup_left.trans le_sup_right)).symm
  let f : D.L₁ →* L1hat s h := (q.subgroupMap (D.L₁.subgroupOf (X D K))).comp e.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp e.surjective
  have hp : IsPGroup 3 (D.L₁ ⧸ pCore 2 D.L₁) := IsPGroup.of_card (n := 1) hc
  let g := (subgroupOfEquivOfLe hLC).symm.toMonoidHom.comp f
  have hg : Function.Surjective g := (subgroupOfEquivOfLe hLC).symm.surjective.comp hf
  have hb := le_twoThreeCore_of_normal B (quotient_twoCore_isThreeGroup_of_surjective g hg hp)
  intro x hx
  exact mem_map.mpr ⟨⟨x,hLC hx⟩,hb hx,rfl⟩
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
