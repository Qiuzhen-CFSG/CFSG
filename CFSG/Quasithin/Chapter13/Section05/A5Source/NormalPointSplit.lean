module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrders
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.ResidualAlgebra
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The marked residual splitting of the original normal A5 point group

The recognized quaternion residual has order 288 and intersects each two-subgroup
inside O2(H). The original elementary module V supplies an involution outside
that residual. It therefore splits the subgroup O^2(H)V of order 576, which is
normal in H. In the ordinary source branch M=L this subgroup is all of H.

The resulting semidirect-product equivalence fixes the residual and the chosen
involution factor. The common Borel L1T is recovered as N_H(V), so marking V
also retains the exact overlap used by the unitary amalgam. This removes the
splitting premise; comparison of the residual action with the matrix point
parabolic and compatibility with the plane marking remain separate.

Source: Aschbacher--Smith 13.5.15(8) and 13.5.17, printed pp.920--922.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
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

theorem normal_point_residual_geometry :
    Nat.card (pResidual 2 H) = 288 ∧ pCore 2 H ≤ pResidual 2 H ∧
    ∀ A : Subgroup H, IsPGroup 2 A → pResidual 2 H ⊓ A ≤ pCore 2 H := by
  obtain ⟨q,_,⟨r⟩⟩ := normal_point_residual_factors d hA312 hH hU hn
  exact ⟨q.residual_card _ r,q.residual_contains_core _ r,
    fun A hA => q.residual_inf_two_subgroup_le _ r A hA⟩

theorem normal_source_point_involution :
    ∃ v : H, (v : G) ∈ V ∧ v^2=1 ∧ v ∉ pResidual 2 H := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨v,hv,hvq,hv2,_⟩ := source_normal_pair_core d hA312 hH hU hn
  let vH : H := ⟨v,hf.V_le_H hv⟩
  refine ⟨vH,hv,Subtype.ext hv2,?_⟩
  intro hr
  have hp : IsPGroup 2 (V.subgroupOf H) :=
    (IsElementaryAbelian.isPGroup 2 V).comap_of_injective H.subtype H.subtype_injective
  have hc := (normal_point_residual_geometry d hA312 hH hU hn).2.2 (V.subgroupOf H) hp
    (show vH ∈ pResidual 2 H ⊓ V.subgroupOf H from ⟨hr,hv⟩)
  exact hvq (mem_map_of_mem H.subtype hc)


/-- The original elementary module supplies the involution that splits the
order-576 point subgroup over its two-residual. -/
theorem normal_point_split_subgroup :
    ∃ v : H, (v : G) ∈ V ∧ v^2=1 ∧ v ∉ pResidual 2 H ∧
      pResidual 2 H ⊔ zpowers v = pResidual 2 H ⊔ V.subgroupOf H ∧
      Disjoint (pResidual 2 H) (zpowers v) ∧
      Nat.card (pResidual 2 H ⊔ V.subgroupOf H : Subgroup H) = 576 := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨v,hv,hv2,hvr⟩ := normal_source_point_involution d hA312 hH hU hn
  have hgeo := normal_point_residual_geometry d hA312 hH hU hn
  have hseed : V₃.subgroupOf H ≤ pCore 2 H := by
    intro x hx
    have hc : (x : G) ∈ Source.QH H := hf.UH_le_QH (le_conjugateSpanBy _ _ hx)
    exact (show (Source.QH H).subgroupOf H = pCore 2 H from
      comap_map_eq_self_of_injective H.subtype_injective _) ▸ hc
  have hvseed : (v : G) ∉ V₃ := fun hh => hvr (hgeo.2.1 (hseed hh))
  have hV : V₃ ⊔ zpowers (v : G) = V :=
    sup_zpowers_eq_of_relIndex_prime d.third_le Nat.prime_two d.third_index hv hvseed
  have hVh : V₃.subgroupOf H ⊔ zpowers v = V.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,
      map_subgroupOf_eq_of_le (d.third_le.trans hf.V_le_H),
      map_subgroupOf_eq_of_le hf.V_le_H]
    exact hV
  have hj : pResidual 2 H ⊔ zpowers v = pResidual 2 H ⊔ V.subgroupOf H := by
    rw [←hVh,←sup_assoc,sup_eq_left.mpr (hseed.trans hgeo.2.1)]
  have ho : orderOf v=2 := orderOf_eq_prime hv2 (fun he => hvr (he ▸ (pResidual 2 H).one_mem))
  have hd := (pResidual 2 H).disjoint_zpowers_of_prime_order_not_mem v ho hvr
  refine ⟨v,hv,hv2,hvr,hj,hd,?_⟩
  rw [←hj,card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (by rw [(pResidual 2 H).normalizer_eq_top]; exact le_top) hd,
    hgeo.1,Nat.card_zpowers,ho]

theorem normal_ordinary_point_complement (hc : Nat.card H=576) :
    ∃ v : H, (v : G) ∈ V ∧ v^2=1 ∧
      (pResidual 2 H).IsComplement' (zpowers v) := by
  obtain ⟨v,hv,hv2,_,hj,hd,hcJ⟩ := normal_point_split_subgroup d hA312 hH hU hn
  have htop : pResidual 2 H ⊔ zpowers v = ⊤ := by
    apply eq_of_le_of_card_ge le_top
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv,hj,hcJ,hc]
  refine ⟨v,hv,hv2,isComplement'_of_disjoint_and_mul_eq_univ hd ?_⟩
  rw [←Subgroup.normal_mul,htop]
  rfl


/-- The original common Borel is intrinsic in the point endpoint once the
original elementary module is marked. -/
theorem normal_point_borel_intrinsic :
    (residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf H =
      normalizer (V.subgroupOf H : Set H) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  rw [←subgroupOf_normalizer_eq hf.V_le_H,
    normal_module_normalizer_eq_local d hA312 hH hU hn,
    ←normal_local_intersection d hA312 hH hU hn]
  ext x
  exact and_iff_right x.property

/-- The order-576 point subgroup selected by V is normal in H. -/
theorem normal_point_split_subgroup_normal :
    (pResidual 2 H ⊔ V.subgroupOf H).Normal := by
  obtain ⟨_,_,_,_,_,_,hc⟩ := normal_point_split_subgroup d hA312 hH hU hn
  rcases normal_point_card_cases d hA312 hH hU hn with h576 | h1152
  · have he : pResidual 2 H ⊔ V.subgroupOf H = ⊤ := by
      apply eq_of_le_of_card_ge le_top
      rw [Nat.card_congr Subgroup.topEquiv.toEquiv,hc,h576]
    rw [he]
    infer_instance
  · apply normal_of_index_eq_two
    have hh := (pResidual 2 H ⊔ V.subgroupOf H).card_mul_index
    rw [hc,h1152] at hh
    omega

/-- In the ordinary source branch the whole point endpoint splits over its
actual residual. Its exact Borel is retained as the normalizer of the
marked original module in the constructed semidirect product. -/
theorem normal_ordinary_point_semidirect
    (hordinary : L ⊔ (T : Subgroup G) = L) :
    ∃ v : H, (v : G) ∈ V ∧ v^2=1 ∧
      ∃ e : H ≃* (pResidual 2 H) ⋊[
          (pResidual 2 H).normalizerMonoidHom.comp
            (inclusion ((pResidual 2 H).normalizer_eq_top ▸ le_top))] (zpowers v),
        (∀ r : pResidual 2 H, e r = SemidirectProduct.inl r) ∧
        (∀ x : zpowers v, e x = SemidirectProduct.inr x) ∧
        ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf H).map e.toMonoidHom =
          normalizer (((V.subgroupOf H).map e.toMonoidHom) : Set _) := by
  have hc : Nat.card H=576 := by
    rcases normal_local_orders d hA312 hH hU hn with h | h
    · exact h.1
    · have hh := h.2.2
      rw [hordinary,normal_local_card d hA312 hH hU hn] at hh
      contradiction
  obtain ⟨v,hv,hv2,hcomp⟩ := normal_ordinary_point_complement d hA312 hH hU hn hc
  let f := SemidirectProduct.mulEquivSubgroup hcomp
  refine ⟨v,hv,hv2,f.symm,?_,?_,?_⟩
  · intro r
    apply f.injective
    rw [f.apply_symm_apply]
    simp [f]
  · intro x
    apply f.injective
    rw [f.apply_symm_apply]
    simp [f]
  · rw [normal_point_borel_intrinsic d hA312 hH hU hn,
      map_normalizer_eq_of_bijective _ f.symm.bijective]

end CFSG.Quasithin.Chapter13.Section05.A5Source
