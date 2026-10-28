module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Orbit
public import CFSG.Quasithin.ChapterE.Section03.OddCore
public import CFSG.Quasithin.ChapterE.Section04.Basic

/-!
# The selected actor on the literal H-star quotient

The common-core and parameter-component constructions use the same omega
orbit and centralizer quotient. Transport their faithful binary action and
E.3.6 fixed-space family along this precise quotient identification. The
selected image has order at least 2ⁿ and centralizes every odd subgroup it
normalizes. Reducedness of V_H also makes O₂(H*) trivial, while the actual
residual image is normal with two-group quotient. These are the inputs to
`selected_star_le_residual` and the Sylow order comparison in the parent leaf.

Source: Aschbacher--Smith 11.3.4(1), 11.3.7 (first paragraph), and E.3.40,
printed pp.771, 773, 240 (combined manuscript, 1 March 2004).
The equality s(G,V) = n remains the explicit preceding-source input.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The two literal centralizer denominators agree after the omega-orbit identification. -/
theorem star_denominator_eq (hTH : (T : Subgroup G) ≤ H) :
    (centralizer (omegaClosure T H : Set G)).subgroupOf H =
      centralizer ((ParameterComponent.omegaOrbit T H).subgroupOf H : Set H) := by
  rw [omegaClosure_eq_parameterOrbit]
  ext x
  constructor
  · intro hx v hv
    exact Subtype.ext (hx v hv)
  · intro hx v hv
    exact congrArg H.subtype (hx ⟨v, ParameterComponent.omegaOrbit_le hTH hv⟩ hv)

/-- The quotient comparison preserves the projection from the original H. -/
noncomputable def starOrbitEquiv (hTH : (T : Subgroup G) ≤ H) :
    Star T H ≃* ParameterComponent.OrbitQuotient T H :=
  QuotientGroup.quotientMulEquivOfEq (star_denominator_eq hTH)

/-- The quotient comparison commutes with the original projection. -/
theorem starOrbitEquiv_projection (hTH : (T : Subgroup G) ≤ H) (h : H) :
    starOrbitEquiv hTH (starProjection T H h) = ParameterComponent.orbitProjection T H h := rfl

/-- The same ambient actor maps to the same quotient subgroup. -/
theorem starOrbitEquiv_actor (hTH : (T : Subgroup G) ≤ H) (A : Subgroup G) :
    ((A.subgroupOf H).map (starProjection T H)).map (starOrbitEquiv hTH).toMonoidHom =
      ParameterComponent.actorImage T H A := by
  rw [map_map]
  rfl

/-- Reducedness of the original omega orbit makes O₂(H*) trivial. -/
theorem source_star_core (s : Hypothesis1131At D S U₁ H) : pCore 2 (Star T H) = ⊥ := by
  have he := (ParameterComponent.omegaOrbit_reduced s).quotient_pCore_eq_bot
  apply Subgroup.map_injective (f := (starOrbitEquiv s.outside.1.1.2).toMonoidHom)
    (starOrbitEquiv s.outside.1.1.2).injective
  rw [pCore_map_iso, Subgroup.map_bot]
  exact he

/-- The original faithful binary action transported to the literal common-core quotient. -/
noncomputable def sourceStarRepresentation (s : Hypothesis1131At D S U₁ H) :
    letI := ParameterComponent.omegaOrbit_elementary s
    Representation (ZMod 2) (Star T H) (Additive (ParameterComponent.omegaOrbit T H)) :=
  (ParameterComponent.orbitRepresentation s).comp (starOrbitEquiv s.outside.1.1.2).toMonoidHom

/-- Faithfulness uses exactly the centralizer denominator. -/
theorem sourceStarRepresentation_injective (s : Hypothesis1131At D S U₁ H) :
    Function.Injective (sourceStarRepresentation s) :=
  (ParameterComponent.orbitRepresentation_injective s).comp
    (starOrbitEquiv s.outside.1.1.2).injective

/-- E.3.6 on the original selected conjugate, at the supplied source parameter n. -/
theorem selected_star_family (s : Hypothesis1131At D S U₁ H) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞)) :
    letI := ParameterComponent.omegaOrbit_elementary s
    ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ∈
      ChapterE.fixedSpaceFamily (sourceStarRepresentation s) S.field.degree := by
  let := D.elementary
  let := ParameterComponent.omegaOrbit_elementary s
  have hf := ParameterComponent.active_conjugate_fixedSpaceFamily s g hg
    (by simpa only [omegaClosure_eq_parameterOrbit] using ha)
  rw [hs, ENat.toNat_natCast] at hf
  let e := starOrbitEquiv s.outside.1.1.2
  have hh := ChapterE.fixedSpaceFamily_map_of_equivariant
    (ParameterComponent.orbitRepresentation s) (sourceStarRepresentation s)
    e.symm.toMonoidHom e.symm.injective (LinearEquiv.refl (ZMod 2) _)
    (by intro x v; change _ = ParameterComponent.orbitRepresentation s (e (e.symm x)) v
        rw [e.apply_symm_apply]; rfl) hf
  have hm : (ParameterComponent.actorImage T H (V.map (MulAut.conj g).toMonoidHom)).map
      e.symm.toMonoidHom =
        ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) := by
    rw [← starOrbitEquiv_actor s.outside.1.1.2, map_map]
    simp [e]
  rwa [hm] at hh


/-- The image of O²(H) is normal in H*, without an ambient normality assumption. -/
instance residualStar_normal : (residualStar T H).Normal := by
  have hn : ((outsideResidual H).subgroupOf H).Normal := by
    change (((pResidual 2 H).map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  exact hn.map (starProjection T H) (QuotientGroup.mk'_surjective _)

/-- The original Sylow supplements O²(H), so H*/K* is a two-group. -/
theorem source_star_residual_quotient_two (hTH : (T : Subgroup G) ≤ H) :
    IsPGroup 2 (Star T H ⧸ residualStar T H) := by
  let P := T.subtype hTH
  let q := starProjection T H
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hgen : residualStar T H ⊔ (P : Subgroup H).map q = ⊤ := by
    have he := congrArg (map q) (pResidual_sup_sylow_eq_top P)
    have hr : (outsideResidual H).subgroupOf H = pResidual 2 H :=
      comap_map_eq_self_of_injective H.subtype_injective _
    simpa only [residualStar, hr, Subgroup.map_sup, map_top_of_surjective q hq] using he
  exact isPGroup_quotient_of_sup_eq_top _ _ (P.isPGroup'.map q) hgen

/-- Faithfulness and the fixed-space family give |A*| ≥ 2ⁿ. -/
theorem selected_star_card_lower (s : Hypothesis1131At D S U₁ H) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞)) :
    Nat.card S.field.Carrier ≤ Nat.card
      (((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) := by
  let := ParameterComponent.omegaOrbit_elementary s
  have hf := selected_star_family s g hg ha hs
  have hr := ChapterE.parameter_le_rank_of_mem_fixedSpaceFamily
    (sourceStarRepresentation s) (sourceStarRepresentation_injective s) hf
  rw [S.field.card_eq]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hr).trans
    (Nat.pow_log_le_self 2 (Nat.card_pos.ne'))

/-- E.3.40 excludes nontrivial action on every normalized odd subgroup. -/
theorem selected_star_centralizes_odd (s : Hypothesis1131At D S U₁ H) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (R : Subgroup (Star T H)) (hR : Odd (Nat.card R))
    (hn : ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ≤
      normalizer (R : Set (Star T H))) :
    ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ≤
      centralizer (R : Set (Star T H)) := by
  let := ParameterComponent.omegaOrbit_elementary s
  exact ChapterE.centralizes_odd_of_mem_fixedSpaceFamily (sourceStarRepresentation s)
    (sourceStarRepresentation_injective s)
    (ChapterE.fixedSpaceFamily_mono _ (by decide : 0 < 2) S.nonbinary
      (selected_star_family s g hg ha hs)) R hR hn
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
