module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointSwap
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointInvolution
public import Theory.GroupTheory.QuaternionResidualSwapJoinEquivalence
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection

/-!
# The ordinary point subgroup inside the doubled source endpoint

The original residual has two commuting SL₂(3) factors and the source module
supplies an involution exchanging them. Comparing that residual with the
literal unitary residual and extending across the involution recognizes
O²(H)V, of order 576, in both source branches. Normality identifies its
intrinsic two-core, so the original V and its exact overlap normalizer are
retained. The second theorem transports this map to the original ambient G.

This is the ordinary normal subamalgam used to construct the doubled
amalgam of Aschbacher--Smith 13.5.17, printed p.922. Extension across the
additional common coset remains with the doubled amalgam assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.UnitaryTwo
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

/-- The normal ordinary point subgroup is recognized in either source branch. -/
theorem source_normal_point_base_unitary :
    let J := pResidual 2 H ⊔ V.subgroupOf H
    ∃ e : J ≃* pointParabolic 1 (Nat.le_refl 1),
      ((V.subgroupOf H).subgroupOf J).map e.toMonoidHom = PointInvolution.pointModule ∧
      (((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf H).subgroupOf J).map
        e.toMonoidHom = (overlap 1 (Nat.le_refl 1)).subgroupOf (pointParabolic 1 (Nat.le_refl 1)) := by
  let J := pResidual 2 H ⊔ V.subgroupOf H
  let P := pointParabolic 1 (Nat.le_refl 1)
  let : J.Normal := normal_point_split_subgroup_normal d hA312 hH hU hn
  obtain ⟨v,hv,hv2,hvr,q,_,c,hs,_,_⟩ := normal_point_swapped_residual d hA312 hH hU hn
  have hvJ : v ∈ J := (show V.subgroupOf H ≤ J from le_sup_right) hv
  obtain ⟨_,_,_,_,_,_,hcJ⟩ := normal_point_split_subgroup d hA312 hH hU hn
  have hcR := (normal_point_residual_geometry d hA312 hH hU hn).1
  obtain ⟨e,he⟩ := c.exists_mulEquiv_subgroup_of_swap PointResidual.projectivePointResidualData
    J le_sup_left (by rw [hcJ,hcR]) v hvJ PointInvolution.involution hv2
    PointInvolution.involution_sq hvr PointInvolution.involution_complement
    hs PointInvolution.involution_swaps_residual.1
    (c.left_model.some.trans PointResidual.projectivePointResidualData.left_model.some.symm)
  let vJ : J := ⟨v,hvJ⟩
  have hQJ : pCore 2 H ≤ J :=
    (normal_point_residual_geometry d hA312 hH hU hn).2.1.trans le_sup_left
  have hcore : (pCore 2 J).map J.subtype = pCore 2 H := by
    rw [← (inferInstance : J.Normal).isSubnormal.pCore_subgroupOf 2,
      map_subgroupOf_eq_of_le hQJ]
  have hfixed : (pCore 2 J ⊓ centralizer ({vJ} : Set J)).map J.subtype =
      pCore 2 H ⊓ centralizer ({v} : Set H) := by
    rw [map_inf _ _ _ J.subtype_injective,hcore,map_subtype_centralizer_singleton]
    change pCore 2 H ⊓ (J ⊓ centralizer ({v} : Set H)) = _
    rw [← inf_assoc,inf_eq_left.mpr hQJ]
  have hV : (V.subgroupOf H).subgroupOf J =
      (pCore 2 J ⊓ centralizer ({vJ} : Set J)) ⊔ zpowers vJ := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le (show V.subgroupOf H ≤ J from le_sup_right),
      Subgroup.map_sup,hfixed,MonoidHom.map_zpowers]
    exact normal_point_module_from_involution d hA312 hH hU hn v hv hv2 hvr
  have hVm : ((V.subgroupOf H).subgroupOf J).map e.toMonoidHom = PointInvolution.pointModule := by
    rw [hV,map_fixed_core_join_zpowers,he,← PointInvolution.pointModule_from_involution]
  refine ⟨e,hVm,?_⟩
  rw [normal_point_borel_intrinsic d hA312 hH hU hn,
    subgroupOf_normalizer_eq (show V.subgroupOf H ≤ J from le_sup_right),
    map_normalizer_eq_of_bijective _ e.bijective,hVm,PointInvolution.pointModule_normalizer]
/-- The same point comparison on the original ambient subgroup, retaining
its module and the intersection with the original full overlap. -/
theorem source_normal_point_base_ambient_unitary :
    let J := (pResidual 2 H).map H.subtype ⊔ V
    ∃ e : J ≃* pointParabolic 1 (Nat.le_refl 1),
      (V.subgroupOf J).map e.toMonoidHom = PointInvolution.pointModule ∧
      ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf J).map
        e.toMonoidHom = (overlap 1 (Nat.le_refl 1)).subgroupOf (pointParabolic 1 (Nat.le_refl 1)) := by
  let J := pResidual 2 H ⊔ V.subgroupOf H
  let K := (pResidual 2 H).map H.subtype ⊔ V
  have hf := (source13_5_7 d hA312 hH).f9Hypothesis
  have hV : V ≤ H := hf.V_le_H
  have hm : J.map H.subtype=K := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hV]
  let j : J ≃* K := (J.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hm)
  obtain ⟨e,heV,heB⟩ := source_normal_point_base_unitary d hA312 hH hU hn
  have ht (A : Subgroup G) : (A.subgroupOf K).map j.symm.toMonoidHom =
      (A.subgroupOf H).subgroupOf J := by
    ext x
    rw [mem_map_equiv]
    rfl
  refine ⟨j.symm.trans e,?_,?_⟩
  · change (V.subgroupOf K).map (e.toMonoidHom.comp j.symm.toMonoidHom) = _
    rw [←map_map,ht,heV]
  · change ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf K).map
      (e.toMonoidHom.comp j.symm.toMonoidHom) = _
    rw [←map_map,ht,heB]

end CFSG.Quasithin.Chapter13.Section05.A5Source
