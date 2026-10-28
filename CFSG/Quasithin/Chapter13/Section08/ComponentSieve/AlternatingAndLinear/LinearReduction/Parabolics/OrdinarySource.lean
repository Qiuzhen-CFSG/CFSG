module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.LocalAlgebra
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.Flags
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.NaturalSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.CubicOrder
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.FourLift
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.FiveElimination


/-!
# Ordinary source placement in the linear parabolic reduction

The literal residual definition from Notation 13.2.1 supplies
normalization and two-perfectness. The natural-section calculation gives
the intrinsic cubic quotient of that ordinary residual, so the actual
node L₁* (T* ∩ K*) has index
three over the component Sylow. The recognition theorem and invariant
subspace calculation construct a deleted flag in that Sylow's own basis.
Its two-residual is exactly L₁*, not an abstract isomorphic subgroup.

If T* ≤ K*, the whole H* marking extends the prescribed component
marking on every original K representative. It carries (L₁T)*, L₁*,
and T* to the marked minimal parabolic, its embedded O² residual, and
the complete flag. The degree-five specialization has exactly the
subgroup identities consumed by FiveElimination. In degree four the
adjacent-node enlargement lifts to an actual K₁ ≤ K containing L₁,
with K₁T in Hz and K₁/O₂(K₁) ≃ PSL₃(2). Its image is the selected
Levi component, and its quotient map is the geometric block map.
The theta identity excludes containment in M; O₂(H) supplies the
nontrivial two-core. No inference from T* ≤ K* to T ≤ K is used.

These are conditional source deductions for Aschbacher–Smith 13.8.25,
printed p.959 (PDF p.976), combined manuscript of 1 March 2004. The
earlier natural-action data, relative component normality, actual Sylow
subgroup, H = KT, and theta identity remain explicit source inputs.
No residual order, flag position, or local overgroup is assumed in the
assembled results. The parent retains the dimension and case assembly,
including the outer degree-four alternative and case (1) of 13.8.8.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- Source flag and residual deductions from an explicit cubic quotient.
The index and flag are constructed. `source_deleted_basis_flag` below
discharges that quotient premise from the ordinary natural-section data. -/
theorem source_deleted_basis_flag_of_cubic (H K L L₁ T V₁ : Subgroup G)
    (hKH : K ≤ H) (hLK : L₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsSylowIn 2 T H)
    (hdef : L₁ = (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (V₁ : Set G)).subtype)
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hcard : Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (e : (K ⧸ pCore 2 K) ≃* PSL (m + 1)) :
    ∃ (b : Basis m) (i : Fin m),
      sourceNode H K L₁ T = ambientFlagStabilizer (starLinearEquiv H K hKH hK e)
        (deletedFlag hm₀ b i) ∧
      ((Source.starImage H T ⊓ Source.starImage H K).subgroupOf (Source.starImage H K)).map
        (linearModel (starLinearEquiv H K hKH hK e)).toMonoidHom = cutStabilizer b Set.univ ∧
      Source.starImage H T ≤ normalizer (sourceNode H K L₁ T : Set (Source.Hstar H)) ∧
      (pResidual 2 (sourceNode H K L₁ T)).map (sourceNode H K L₁ T).subtype =
        Source.starImage H L₁ := by
  obtain ⟨hp, hn⟩ := notation_residual_inputs L L₁ T V₁ hdef hTV
  obtain ⟨hs, hi⟩ := sourceNode_index_three_of_cubic H K L₁ T hKH hLK hK hT hn hcard
  obtain ⟨b, i, hP, hS⟩ := exists_deleted_basis_flag (Source.starImage H K)
    (Source.starImage H T ⊓ Source.starImage H K) (sourceNode H K L₁ T)
    hm₀ hm₁ (starLinearEquiv H K hKH hK e) hs le_sup_right
    (sourceNode_le_component H K L₁ T hLK) hi
  exact ⟨b, i, hP, hS,
    sourceNode_normalized H K L₁ T (isSylowIn_iff.mp hT).2.1 hKH hKn hn,
    sourceNode_residual H K L₁ T (hLK.trans hKH) hp (isSylowIn_iff.mp hT).1 hn⟩

/-- The whole linear marking extends precisely the supplied component marking. -/
noncomputable def wholeLinearModel (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ T = H) (hs : Source.starImage H T ≤ Source.starImage H K)
    {n : ℕ} [NeZero n] (e : (K ⧸ pCore 2 K) ≃* PSL n) :
    Source.Hstar H ≃* BinaryLinear.GL (Vector n) :=
  (wholeStarLinearEquiv H K T hKH hTH hK hKT hs e).trans (pslEquivLinear n)

theorem wholeLinearModel_mk (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ T = H) (hs : Source.starImage H T ≤ Source.starImage H K)
    {n : ℕ} [NeZero n] (e : (K ⧸ pCore 2 K) ≃* PSL n) (k : K) :
    wholeLinearModel H K T hKH hTH hK hKT hs e
      (QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩) =
        pslEquivLinear n (e (QuotientGroup.mk' (pCore 2 K) k)) := by
  exact congrArg (pslEquivLinear n)
    (wholeStarLinearEquiv_mk H K T hKH hTH hK hKT hs e k)

private theorem whole_model_map_subgroup (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ T = H) (hs : Source.starImage H T ≤ Source.starImage H K)
    {n : ℕ} [NeZero n] (e : (K ⧸ pCore 2 K) ≃* PSL n)
    (P : Subgroup (Source.Hstar H)) (hP : P ≤ Source.starImage H K) :
    P.map (wholeLinearModel H K T hKH hTH hK hKT hs e).toMonoidHom =
      (P.subgroupOf (Source.starImage H K)).map
        (linearModel (starLinearEquiv H K hKH hK e)).toMonoidHom := by
  conv_lhs => rw [← map_subgroupOf_eq_of_le hP, map_map]
  rfl

omit [Finite G] in
theorem sourceNode_eq_star_join (H K L₁ T : Subgroup G)
    (hLH : L₁ ≤ H) (hTH : T ≤ H)
    (hs : Source.starImage H T ≤ Source.starImage H K) :
    sourceNode H K L₁ T = Source.starImage H (L₁ ⊔ T) := by
  rw [sourceNode, inf_eq_left.mpr hs, Source.starImage, Source.starImage,
    ← Subgroup.map_sup, ← subgroupOf_sup hLH hTH]
  rfl

/-- The same whole-group equivalence carries the source parabolic, its
marked residual, and the actual Sylow to their basis-coordinate subgroups. -/
theorem whole_node_markings (H K L₁ T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hLK : L₁ ≤ K)
    (hK : (K.subgroupOf H).IsCComponent) (hKT : K ⊔ T = H)
    (hs : Source.starImage H T ≤ Source.starImage H K)
    {m : ℕ} (hm : 2 ≤ m) (e : (K ⧸ pCore 2 K) ≃* PSL (m + 1))
    (b : Basis m) (i : Fin m)
    (hP : sourceNode H K L₁ T = ambientFlagStabilizer (starLinearEquiv H K hKH hK e)
      (deletedFlag hm b i))
    (hS : ((Source.starImage H T ⊓ Source.starImage H K).subgroupOf (Source.starImage H K)).map
      (linearModel (starLinearEquiv H K hKH hK e)).toMonoidHom = cutStabilizer b Set.univ)
    (hR : (pResidual 2 (sourceNode H K L₁ T)).map (sourceNode H K L₁ T).subtype =
      Source.starImage H L₁) :
    (Source.starImage H (L₁ ⊔ T)).map
        (wholeLinearModel H K T hKH hTH hK hKT hs e).toMonoidHom = cutStabilizer b {i}ᶜ ∧
      (Source.starImage H L₁).map
        (wholeLinearModel H K T hKH hTH hK hKT hs e).toMonoidHom =
          (pResidual 2 (cutStabilizer b {i}ᶜ)).map (cutStabilizer b {i}ᶜ).subtype ∧
      (Source.starImage H T).map
        (wholeLinearModel H K T hKH hTH hK hKT hs e).toMonoidHom = cutStabilizer b Set.univ := by
  have hnode : (sourceNode H K L₁ T).map
      (wholeLinearModel H K T hKH hTH hK hKT hs e).toMonoidHom = cutStabilizer b {i}ᶜ := by
    rw [whole_model_map_subgroup H K T hKH hTH hK hKT hs e _
      (sourceNode_le_component H K L₁ T hLK), hP]
    exact OuterAction.deletedFlag_linear_image hm (starLinearEquiv H K hKH hK e) b i
  refine ⟨?_, ?_, ?_⟩
  · rwa [sourceNode_eq_star_join H K L₁ T (hLK.trans hKH) hTH hs] at hnode
  · rw [← hR, map_embedded_pResidual, hnode]
  · rw [whole_model_map_subgroup H K T hKH hTH hK hKT hs e _ hs]
    simpa only [inf_eq_left.mpr hs] using hS

/-- The precise single-node inputs consumed by the constructed dimension-five
contradiction. Both maps use the prescribed whole-group marking. -/
theorem five_source_markings_of_cubic (H K L L₁ T V₁ : Subgroup G)
    (hKH : K ≤ H) (hLK : L₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (hdef : L₁ = (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (V₁ : Set G)).subtype)
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hcard : Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (e : (K ⧸ pCore 2 K) ≃* PSL 5)
    (hs : Source.starImage H T ≤ Source.starImage H K) :
    ∃ (b : BinaryLinear.FiveFlagGeometry.FiveBasis) (i : Fin 4),
      (Source.starImage H (L₁ ⊔ T)).map
        (wholeLinearModel H K T hKH (isSylowIn_iff.mp hT).2.1 hK hKT hs e).toMonoidHom =
          fiveParabolic b {i} ∧
      (Source.starImage H L₁).map
        (wholeLinearModel H K T hKH (isSylowIn_iff.mp hT).2.1 hK hKT hs e).toMonoidHom =
          fiveNodeResidual b i ∧
      (Source.starImage H T).map
        (wholeLinearModel H K T hKH (isSylowIn_iff.mp hT).2.1 hK hKT hs e).toMonoidHom =
          cutStabilizer b Set.univ := by
  obtain ⟨b, i, hP, hS, _, hR⟩ := source_deleted_basis_flag_of_cubic
    H K L L₁ T V₁ hKH hLK hK hKn hT hdef hTV hcard
    (by decide : 2 ≤ 4) (by decide : 4 ≤ 4) e
  exact ⟨b, i, whole_node_markings H K L₁ T hKH (isSylowIn_iff.mp hT).2.1
    hLK hK hKT hs (by decide) e b i hP hS hR⟩

/-- The index-three input to flag recognition, calculated from the genuine
ordinary natural section and Notation 13.2.1. -/
theorem sourceNode_index_three (H K L L₁ T V V₁ : Subgroup G)
    (d : NaturalSetup L T V V₁)
    (hKH : K ≤ H) (hLK : L₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hT : IsSylowIn 2 T H)
    (hdef : L₁ = (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (V₁ : Set G)).subtype) :
    IsSylowIn 2 (Source.starImage H T ⊓ Source.starImage H K) (Source.starImage H K) ∧
      (Source.starImage H T ⊓ Source.starImage H K).relIndex (sourceNode H K L₁ T) = 3 := by
  exact sourceNode_index_three_of_cubic H K L₁ T hKH hLK hK hT
    (notation_residual_inputs L L₁ T V₁ hdef d.line_stable).2
    (source_residual_quotient_card d L₁ hdef)

/-- Ordinary source placement with its own Sylow basis, T*-normalization,
and marked O² identity. The natural action supplies the cubic order and
the index-three premise; neither the order nor a flag position is assumed. -/
theorem source_deleted_basis_flag (H K L L₁ T V V₁ : Subgroup G)
    (d : NaturalSetup L T V V₁)
    (hKH : K ≤ H) (hLK : L₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsSylowIn 2 T H)
    (hdef : L₁ = (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (V₁ : Set G)).subtype)
    {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (e : (K ⧸ pCore 2 K) ≃* PSL (m + 1)) :
    ∃ (b : Basis m) (i : Fin m),
      sourceNode H K L₁ T = ambientFlagStabilizer (starLinearEquiv H K hKH hK e)
        (deletedFlag hm₀ b i) ∧
      ((Source.starImage H T ⊓ Source.starImage H K).subgroupOf (Source.starImage H K)).map
        (linearModel (starLinearEquiv H K hKH hK e)).toMonoidHom = cutStabilizer b Set.univ ∧
      Source.starImage H T ≤ normalizer (sourceNode H K L₁ T : Set (Source.Hstar H)) ∧
      (pResidual 2 (sourceNode H K L₁ T)).map (sourceNode H K L₁ T).subtype =
        Source.starImage H L₁ := by
  exact source_deleted_basis_flag_of_cubic H K L L₁ T V₁ hKH hLK hK hKn hT
    hdef d.line_stable (source_residual_quotient_card d L₁ hdef) hm₀ hm₁ e

/-- The actual degree-five source markings needed by
`exclude_five_single_node`, with the ordinary cubic-order premise discharged.
The whole-group model agrees with e by `wholeLinearModel_mk`. -/
theorem five_source_markings (H K L L₁ T V V₁ : Subgroup G)
    (d : NaturalSetup L T V V₁)
    (hKH : K ≤ H) (hLK : L₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (hdef : L₁ = (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (V₁ : Set G)).subtype)
    (e : (K ⧸ pCore 2 K) ≃* PSL 5)
    (hs : Source.starImage H T ≤ Source.starImage H K) :
    ∃ (b : BinaryLinear.FiveFlagGeometry.FiveBasis) (i : Fin 4),
      (Source.starImage H (L₁ ⊔ T)).map
        (wholeLinearModel H K T hKH (isSylowIn_iff.mp hT).2.1 hK hKT hs e).toMonoidHom =
          fiveParabolic b {i} ∧
      (Source.starImage H L₁).map
        (wholeLinearModel H K T hKH (isSylowIn_iff.mp hT).2.1 hK hKT hs e).toMonoidHom =
          fiveNodeResidual b i ∧
      (Source.starImage H T).map
        (wholeLinearModel H K T hKH (isSylowIn_iff.mp hT).2.1 hK hKT hs e).toMonoidHom =
          cutStabilizer b Set.univ := by
  exact five_source_markings_of_cubic H K L L₁ T V₁ hKH hLK hK hKn hT hKT
    hdef d.line_stable (source_residual_quotient_card d L₁ hdef) e hs

/-- The inner degree-four source construction. The flag, its residual,
the marked Levi component D, and its actual lift K₁ are all constructed.
K₁T belongs to Hz, and the quotient formula retains the geometric map
through the actual lifted parabolic. The only local source identity taken
as input is the earlier theta conclusion, not a desired overgroup. -/
theorem exists_four_source_local_component (H K L L₁ T V V₁ G₁ M : Subgroup G)
    (d : NaturalSetup L T V V₁)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hKH : K ≤ H) (hLK : L₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (hdef : L₁ = (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (V₁ : Set G)).subtype)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (e : (K ⧸ pCore 2 K) ≃* PSL 4)
    (hs : Source.starImage H T ≤ Source.starImage H K) :
    let eH := wholeLinearModel H K T hKH (isSylowIn_iff.mp hT).2.1 hK hKT hs e
    ∃ (b : Basis 3) (i : Fin 3),
      (Source.starImage H (L₁ ⊔ T)).map eH.toMonoidHom = fourParabolic b {i} ∧
      (Source.starImage H L₁).map eH.toMonoidHom = fourNodeResidual b i ∧
      (Source.starImage H T).map eH.toMonoidHom = cutStabilizer b Set.univ ∧
      let P := fourParabolic b {i, fourAdjacentNode i}
      let Y := modelLift H eH P
      ∃ (D : Subgroup (BinaryLinear.OuterCyclic.LinearGroup 4)) (_hDP : D ≤ P),
        fourNodeResidual b i ≤ D ∧ (D.subgroupOf P).IsCComponent ∧
        (Source.starImage H T).map eH.toMonoidHom ≤ normalizer (D : Set _) ∧
        (Source.starImage H L₁).map eH.toMonoidHom ≤ D ∧
        ∃ (K₁ : Subgroup G) (hK₁Y : K₁ ≤ Y),
          K₁ ≤ K ∧ L₁ ≤ K₁ ∧ T ≤ normalizer (K₁ : Set G) ∧
          Y = K₁ ⊔ T ∧ (K₁.subgroupOf (K₁ ⊔ T)).IsCComponent ∧
          K₁ ⊔ T ∈ Source.Hz L₁ T G₁ M ∧
          (K₁.subgroupOf Y).map (modelLiftMap H eH P) = D.subgroupOf P ∧
          ∃ eK : (K₁ ⧸ pCore 2 K₁) ≃* PSL 3,
            ∀ k : K₁, eK (QuotientGroup.mk' _ k) = fourEnlargedQuotientEquiv b i
              (QuotientGroup.mk' _ (modelLiftMap H eH P (⟨k.val, hK₁Y k.property⟩ : Y))) := by
  let eH := wholeLinearModel H K T hKH (isSylowIn_iff.mp hT).2.1 hK hKT hs e
  obtain ⟨b, i, hP, hS, _, hR⟩ := source_deleted_basis_flag H K L L₁ T V V₁ d
    hKH hLK hK hKn hT hdef (by decide : 2 ≤ 3) (by decide : 3 ≤ 4) e
  obtain ⟨hbase, hresidual, hflag⟩ := whole_node_markings H K L₁ T hKH
    (isSylowIn_iff.mp hT).2.1 hLK hK hKT hs (by decide) e b i hP hS hR
  refine ⟨b, i, hbase, hresidual, hflag, ?_⟩
  exact four_source_local_component H K L₁ T G₁ M hH hKH hK hKn hKT.symm hLK hT
    (notation_residual_inputs L L₁ T V₁ hdef d.line_stable).1
    (source_residual_quotient_card d L₁ hdef) htheta eH b i hbase hresidual hflag
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource

end
