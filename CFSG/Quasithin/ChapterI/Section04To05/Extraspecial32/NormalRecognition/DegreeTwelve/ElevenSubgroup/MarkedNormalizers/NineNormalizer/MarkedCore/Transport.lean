module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.Preparation
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Transport of the intrinsic marked core

An ambient automorphism carries the literal involution centralizer and its
intrinsic generalized Fitting subgroup to the corresponding objects at the
image involution. We transport every field of the source hypotheses, including
the chosen Sylow three-subgroup, its fixed subgroup, and the fusion witness.
Quaternion normality is transported inside the centralizer.

This is the conjugacy transport used in the Q_b calculation of Aschbacher,
“A 2-local characterization of M12”, Illinois J. Math. 47 (2003), 4.10, p.42.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer.MarkedCore
variable {G : Type*} [Group G] {z : G}

def centralizerEquiv (e : G ≃* G) (z : G) : Centralizer z ≃* Centralizer (e z) where
  toFun x := ⟨e x, mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨e.symm x, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)

theorem core_map (e : G ≃* G) :
    (Core z).map (centralizerEquiv e z).toMonoidHom = Core (e z) :=
  map_generalizedFitting_equiv _

def coreEquiv (e : G ≃* G) (z : G) : Core z ≃* Core (e z) :=
  ((centralizerEquiv e z).subgroupMap (Core z)).trans (MulEquiv.subgroupCongr (core_map e))

theorem coreInG_map (e : G ≃* G) :
    (coreInG z).map e.toMonoidHom = coreInG (e z) := by
  unfold coreInG
  rw [← core_map e, map_map, map_map]
  rfl

theorem core_mem (e : G ≃* G) (x : G) : e x ∈ coreInG (e z) ↔ x ∈ coreInG z := by
  rw [← coreInG_map e, mem_map_equiv, e.symm_apply_apply]

variable [Finite G]

noncomputable def transport (h : Hypotheses z) (e : G ≃* G) : Hypotheses (e z) where
  involution := (e.orderOf_eq z).trans h.involution
  extraspecial := IsExtraspecial.of_mulEquiv (coreEquiv e z) h.extraspecial
  core_card := (Nat.card_congr (coreEquiv e z).toEquiv).symm.trans h.core_card
  quotient_model := h.quotient_model.map fun f =>
    (QuotientGroup.congr (Core z) (Core (e z)) (centralizerEquiv e z) (core_map e)).symm.trans f
  X := h.X.mapSurjective (centralizerEquiv e z).surjective
  fixed := by
    let c := centralizerEquiv e z
    have hcentral : (centralizer (h.X : Set (Centralizer z))).map c.toMonoidHom =
        centralizer ((h.X : Subgroup (Centralizer z)).map c.toMonoidHom : Set (Centralizer (e z))) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ w ⟨v, hv, rfl⟩
        change c v * c y = c y * c v
        simpa only [← map_mul] using congrArg c (hy v hv)
      · intro hx
        refine ⟨c.symm x, ?_, c.apply_symm_apply x⟩
        intro y hy
        apply c.injective
        simpa only [map_mul, c.apply_symm_apply] using hx (c y) (mem_map_of_mem _ hy)
    have hh := congrArg (Subgroup.map c.toMonoidHom) h.fixed
    rw [map_inf _ _ _ c.injective, hcentral, core_map e, MonoidHom.map_zpowers] at hh
    exact hh
  fused := by
    obtain ⟨g, hg, hn⟩ := h.fused
    refine ⟨e g, ?_, ?_⟩
    · simpa only [map_mul, map_inv] using (core_mem e (g*z*g⁻¹)).mpr hg
    · simpa only [← map_mul, ← map_inv, e.injective.ne_iff] using hn

omit [Finite G] in
theorem normal_transport (hn : QuaternionSubgroupsNormal z) (e : G ≃* G) :
    QuaternionSubgroupsNormal (e z) := by
  let c := centralizerEquiv e z
  let q := coreEquiv e z
  intro T hT
  let R := T.map q.symm.toMonoidHom
  have hR : Nonempty (R ≃* QuaternionGroup 2) := hT.map fun f =>
    (q.symm.subgroupMap T).symm.trans f
  have hN := hn R hR
  have hm : ((R.map (Core z).subtype).map c.toMonoidHom) = T.map (Core (e z)).subtype := by
    rw [map_map]
    have he : c.toMonoidHom.comp (Core z).subtype = (Core (e z)).subtype.comp q.toMonoidHom := rfl
    rw [he, ← map_map]
    have hq : R.map q.toMonoidHom = T := by
      change (T.map q.symm.toMonoidHom).map q.toMonoidHom = T
      rw [map_map]
      have hcomp : q.toMonoidHom.comp q.symm.toMonoidHom = MonoidHom.id _ := by
        apply MonoidHom.ext
        intro x
        exact q.apply_symm_apply x
      rw [hcomp, map_id]
    rw [hq]
  exact hm ▸ hN.map c.toMonoidHom c.surjective

/-- The square-root assertion used in the proof of source 4.6. -/
@[expose] def SquareRootClosed (z : G) : Prop := ∀ x : G, x ^ 2 = z → x ∈ coreInG z

omit [Finite G] in
theorem squareRootClosed_transport (hsq : SquareRootClosed z) (e : G ≃* G) :
    SquareRootClosed (e z) := by
  intro x hx
  have hs : (e.symm x) ^ 2 = z := by
    apply e.injective
    simpa only [map_pow, e.apply_symm_apply] using hx
  have hm := (core_mem e (e.symm x)).mpr (hsq _ hs)
  simpa only [e.apply_symm_apply] using hm

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer.MarkedCore

end
