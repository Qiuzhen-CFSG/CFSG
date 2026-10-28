module
public import Theory.GroupTheory.NormalizerAction
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.PPerfectCentralLift
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Mathlib.GroupTheory.Sylow
/-!
# Model bounds for the faithful normalizer omega center

The actual quotient N(K)/C(K) acts faithfully on K/Z(K) when K is perfect.
Its central omega subgroup fixes the image of a component Sylow pointwise.
An intrinsic model bound on elementary Sylow fixers therefore bounds the
omega center, without replacing the ambient Sylow or discarding a central
cover. A separate central-kernel lifting lemma recovers centralization of a
two-perfect subgroup from its image in the same normalizer quotient.

Source: Aschbacher--Smith, proof of15.1.22(**), printed p.1099.
-/
public section
open Subgroup
namespace Subgroup.NormalizerAction
variable {G : Type*} [Group G] (K : Subgroup G)
noncomputable def centralImageAction : Star K →* MulAut (componentImage K) :=
  (MulAut.centralQuotientAction (componentCentralQuotientEquiv K)).comp (action K)
theorem centralImageAction_injective [Group.IsPerfect K] :
    Function.Injective (centralImageAction K) :=
  MulAut.centralQuotientAction_comp_injective _ _ (action_injective K)
theorem centralImageAction_apply (x : Star K) (k : componentImage K) :
    (centralImageAction K x k : Star K) = x * k * x⁻¹ := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (C K) x
  obtain ⟨q, rfl⟩ := (componentCentralQuotientEquiv K).surjective k
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center K) q
  change (MulAut.centralQuotientAction (componentCentralQuotientEquiv K)
    (action K (quotient K n))
    (componentCentralQuotientEquiv K (QuotientGroup.mk' (center K) y)) : Star K) = _
  rw [MulAut.centralQuotientAction_apply, action_quotient,
    componentCentralQuotientEquiv_mk, componentCentralQuotientEquiv_mk]
  change quotient K _ = quotient K n * quotient K (inclusion K.le_normalizer y) * (quotient K n)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

variable [Finite G]
theorem omega_center_card_le_of_model_fixers [Group.IsPerfect K]
    (S : Subgroup G) (P : Sylow 2 K) (hPS : ∀ x ∈ P, (x : G) ∈ S)
    {X : Type*} [Group X] (e : (K ⧸ center K) ≃* X)
    (hfix : ∀ (Q : Sylow 2 X) (B : Subgroup (MulAut X)),
      IsElementaryAbelian 2 B → (∀ b ∈ B, ∀ x ∈ Q, b x = x) → Nat.card B ≤ 2) :
    Nat.card (omega₁ (center (sylowImage K S)) (p := 2)) ≤ 2 := by
  let E := omegaCenterIn (sylowImage K S)
  let ec : componentImage K ≃* X := (componentCentralQuotientEquiv K).symm.trans e
  let a : Star K →* MulAut X := (MulAut.congr ec).toMonoidHom.comp (centralImageAction K)
  have hai : Function.Injective a := (MulAut.congr ec).injective.comp (centralImageAction_injective K)
  let B := E.map a
  let q : K →* X := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q : Sylow 2 X := P.mapSurjective hq
  have hpfix : ∀ b ∈ B, ∀ x ∈ Q, b x = x := by
    rintro _ ⟨z,hz,rfl⟩ _ ⟨y,hy,rfl⟩
    let ystar : componentImage K := componentCentralQuotientEquiv K (QuotientGroup.mk' (center K) y)
    have hyS : (ystar : Star K) ∈ sylowImage K S :=
      ⟨inclusion K.le_normalizer y,hPS y hy,rfl⟩
    have hcomm := (mem_omegaCenterIn_iff (sylowImage K S) z).mp hz
    have he : centralImageAction K z ystar = ystar := by
      apply Subtype.ext
      rw [centralImageAction_apply, ← hcomm.2.1 ystar hyS, mul_inv_cancel_right]
    change ec (centralImageAction K z (ec.symm (q y))) = q y
    have hqy : q y = ec ystar := by
      simp only [q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ec,
        MulEquiv.trans_apply, ystar, MulEquiv.symm_apply_apply]
    rw [hqy,ec.symm_apply_apply,he]
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map a
  have hb := hfix Q B inferInstance hpfix
  rw [card_map_of_injective hai] at hb
  change Nat.card (((omega₁ (center (sylowImage K S)) (p := 2)).map
    (center (sylowImage K S)).subtype).map (sylowImage K S).subtype) ≤ 2 at hb
  rwa [card_map_of_injective (sylowImage K S).subtype_injective,
    card_map_of_injective (center (sylowImage K S)).subtype_injective] at hb

omit [Finite G] in
/-- Quotient commutation with a two-perfect subgroup reflects through a central two-cover. -/
theorem centralizes_of_quotient_centralizes (Y : Subgroup G) (hYK : Y ≤ K)
    (hp : IsPPerfect 2 Y) (hZ : IsPGroup 2 (center K))
    (z : normalizer (K : Set G))
    (hc : quotient K z ∈ centralizer
      ((Y.subgroupOf (normalizer (K : Set G))).map (quotient K) : Set (Star K))) :
    (z : G) ∈ centralizer (Y : Set G) := by
  let f : Y →* K := inclusion hYK
  let q := QuotientGroup.mk' (center K)
  have hqker : q.ker = center K := QuotientGroup.ker_mk' _
  have he : q.comp ((K.normalizerMonoidHom z).toMonoidHom.comp f) = q.comp f := by
    ext y
    apply (componentCentralQuotientEquiv K).injective
    apply Subtype.ext
    rw [MonoidHom.comp_apply,MonoidHom.comp_apply,MonoidHom.comp_apply,
      componentCentralQuotientEquiv_mk,componentCentralQuotientEquiv_mk]
    let yn : normalizer (K : Set G) := inclusion K.le_normalizer (f y)
    have hy : yn ∈ Y.subgroupOf (normalizer (K : Set G)) := y.property
    have hh := hc (quotient K yn) (mem_map_of_mem (quotient K) hy)
    change quotient K (z * yn * z⁻¹) = quotient K yn
    rw [map_mul,map_mul,map_inv, ← hh,mul_inv_cancel_right]
  have hf := hp.hom_eq_of_comp_eq_of_central_pGroup_kernel q
    (hqker.le) (hqker.symm ▸ hZ)
    ((K.normalizerMonoidHom z).toMonoidHom.comp f) f he
  intro y hy
  have hh := congrArg (fun ff : Y →* K => (ff ⟨y,hy⟩ : G)) hf
  change (z : G) * y * (z : G)⁻¹ = y at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end Subgroup.NormalizerAction
