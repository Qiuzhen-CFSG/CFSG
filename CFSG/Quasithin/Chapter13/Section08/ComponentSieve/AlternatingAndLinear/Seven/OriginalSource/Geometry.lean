module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.FirstCase
/-!
# Original-source reciprocal geometry for the seven-point exclusion

The original flag and F.9 hypotheses construct every field of the reciprocal
13.8.18 input at a selected strict pair, including relative endpoint normality,
the actual two-residual, both kernel identities and the subgroup-index
comparison. The marked reciprocal transvection then proves that Vγ* has rank
greater than one; this uses the corrected actor Vβ in its actual local two-core.

The preceding component and F.9 hypotheses retain their source owners. Final
13.8.24 assembly is owned by qt-d-138-linear-seven-source, under the parent
qt-d-138-linear-source. No reciprocal geometry or transvection is assumed.

Source: Aschbacher–Smith 13.8.18 and 13.8.24, printed pp.953,958–959.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open SourceCompletion CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open FieldComponents.HigherFieldReduction.ExternalModules
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]

omit [(V₁.subgroupOf (Source.UH H V₃)).Normal] in
theorem source_reciprocal_inputs
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : PairsBranch.CentralAction.IsSourceAction H V₃ V₁ ρ)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (hcmp : Reorientation.denominatorRank V₃ V₁ c ≤
      rank (Source.starImage H (c.Ugamma V₃))) :
    CriticalReciprocity.Earlier c (sourceOne L T V₁) K V₃ V₁ := by
  let : IsElementaryAbelian 2 V := hF9.elementary
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  have hKH : K ≤ H := hgen ▸ le_sup_left
  let : IsQuasisimple (alternatingGroup (Fin 7)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hqs := IsQuasisimple.of_mulEquiv (LocalGeometry.starAlternatingEquiv H K hKH hK e).symm
  have hg := local_earlierGeometry d hF9 c
  have he := CriticalSource.earlier_inputs d hH hF9 hcentral hcomm ρ hρ
  have hconj := Comparison.component_conjugate H K hKH hN hqs (MulAut.conj (c.gb : G))
  have hγH : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans hg.Vgamma_H
  refine {
    product := hgen
    edge := Comparison.local_edge d hF9
    component_normal := ?_
    component_residual := ?_
    component_quasisimple := ?_
    terminal_core := ?_
    flag := d.seed_le
    V_le := hF9.V_le_H
    line_le := (d.line_le_plane.trans d.plane_le_seed).trans (le_conjugateSpanBy V₃ H)
    line_normalized := hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
    Vgamma_le := hg.Vgamma_H
    core_commutator := hF9.commutator_UH_QH_le_point
    noncentral := he.noncentral
    edge_commutator := c.edge_commutator_le_of_flag V₃ d.seed_le he.flag_index
      he.noncentral he.edge_normalizes
    Dgamma_kernel := hg.Dgamma_kernel
    DH_kernel := hg.DH_kernel
    DH_proper := hDH
    Dgamma_proper := hDγ
    Qgamma_le_edge := he.endpoint_core c
    edge_proper := he.proper_edge c
    comparison := c.index_comparison_of_selected_rank V₃ V₁ hγH hg.Dgamma_kernel hcmp
    line_card := d.line_card }
  · rw [c.vertexGroup_gamma]; exact hconj.1
  · rw [c.vertexGroup_gamma]; exact hconj.2.1
  · rw [c.vertexGroup_gamma]; exact hconj.2.2
  · have hh := (f9_endpoint_edge_cores _ hF9 c hg.length).1
    change Source.VH H V ≤ (vertexGroup _ _ _ c.previous ⊓ vertexGroup _ _ _ c.gamma).pCoreIn 2 at hh
    rw [inf_comm] at hh
    exact hh

omit [(V₁.subgroupOf (Source.UH H V₃)).Normal] in
/-- At the same selected pair, the original reciprocal actor excludes rank
one without assuming absence of transvections everywhere in H*. -/
theorem source_actor_rank_gt_one
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G))
    (hG64 : TransvectionRecognition.Component.RecognitionStep.G64SourceTheorem.{u}
      KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hKT : K ⊔ (T : Subgroup G) = H)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (htheta : sourceOne L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    [Group.IsSolvable (sourceOne L T V₁ ⊔ (T : Subgroup G) : Subgroup G)]
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nonempty ((sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) ≃*
        Multiplicative (Fin 2 → ZMod 3)))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : PairsBranch.CentralAction.IsSourceAction H V₃ V₁ ρ)
    (c : CriticalPair L (T : Subgroup G) H V)
    (r : CriticalReciprocity.Earlier c (sourceOne L T V₁) K V₃ V₁)
    (hpos : 0 < rank (Source.starImage H (c.Ugamma V₃))) :
    1 < rank (Source.starImage H c.Vgamma) := by
  let := vh_elementary d hH
  let : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (Source.starImage H c.Vgamma) :=
    starImage_isElementaryAbelian H c.Vgamma r.Vgamma_le
  have hle : rank (Source.starImage H (c.Ugamma V₃)) ≤ rank (Source.starImage H c.Vgamma) :=
    Nat.log_monotone (Nat.card_le_card_of_injective
      (Subgroup.inclusion (LocalGeometry.starImage_mono H
        (map_mono (conjugateSpanBy_mono d.seed_le le_rfl))))
      (Subgroup.inclusion_injective _))
  by_contra hn
  have hr : rank (Source.starImage H c.Vgamma) = 1 := by omega
  obtain ⟨a, ha, hne, hc⟩ := CriticalReciprocity.marked_transvection_of_rank_one
    c (sourceOne L T V₁) K V₃ V₁ r ρ hρ hr
  let : IsElementaryAbelian 2 (CriticalReciprocity.Vbeta c) := IsElementaryAbelian.map _
  apply no_transvection_actor d earlier localEarlier hG64 hH hKH hK hN hKT e htheta h13 hcover
    ρ hρ (CriticalReciprocity.Vbeta c) (CriticalReciprocity.Vbeta c)
    (CriticalReciprocity.Vbeta_le_H c _ r.edge r.terminal_core) le_rfl
    ⟨1, by
      change (CriticalReciprocity.Vbeta c).conjBy 1 ≤ _
      rw [conjBy_one]
      exact CriticalReciprocity.Vbeta_le_twoCore c _ r.edge r.terminal_core⟩
  exact ⟨a, LocalGeometry.starImage_mono H (CriticalReciprocity.Ubeta_le_Vbeta c V₃ d.seed_le) ha,
    hne, hc⟩
open Reorientation AsymmetricPair
theorem source_transvection_group_actor
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : PairsBranch.CentralAction.IsSourceAction H V₃ V₁ ρ)
    (Q : CenterQuotientAction H (Source.UH H V₃) V₁) (P : Subgroup G)
    (ht : TransvectionGroup Q P) :
    ∃ a ∈ Source.starImage H P, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1 := by
  obtain ⟨t, ht, hn, hT⟩ := ht.nonidentity_actor
  let a := QuotientGroup.mk' (pCore 2 H) t
  have he : (binaryLinear (Q.action t)).toLinearMap = ρ a := by
    ext v
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
    have hv : v = Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) :=
      congrArg Additive.ofMul hu.symm
    rw [hv, hρ]
    change Additive.ofMul (Q.action t (QuotientGroup.mk' _ u)) = _
    rw [Q.apply_mk]
    rfl
  have hnρ : ρ a ≠ LinearMap.id := by
    intro hh
    apply hn
    ext w
    have hw := LinearMap.congr_fun he (Additive.ofMul w)
    rw [hh] at hw
    exact hw
  have hle := LinearEquiv.mem_dilatransvections_iff_finrank.mp
    (LinearEquiv.transvections_subset_dilatransvections hT)
  rw [he] at hle
  have hp : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≠ 0 := by
    intro hz
    exact hnρ (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
  refine ⟨a, ⟨t, ht, rfl⟩, ?_, ?_⟩
  · intro ha
    apply hnρ
    rw [ha, map_one]
    rfl
  · have hc : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1 :=
      Nat.le_antisymm hle (Nat.one_le_iff_ne_zero.mpr hp)
    simpa only [fixedCodim_zpowers_eq_displacement_rank, Module.End.one_eq_id] using hc
open AsymmetricPair SectionActions
/-- Construct the selected strict pair, its complete reciprocal data, and
its large endpoint actor from the original source setup. -/
theorem source_selected_geometry
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G))
    (hG64 : TransvectionRecognition.Component.RecognitionStep.G64SourceTheorem.{u}
      KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hKT : K ⊔ (T : Subgroup G) = H)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (htheta : sourceOne L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    [Group.IsSolvable (sourceOne L T V₁ ⊔ (T : Subgroup G) : Subgroup G)]
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nonempty ((sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) ≃*
        Multiplicative (Fin 2 → ZMod 3)))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : PairsBranch.CentralAction.IsSourceAction H V₃ V₁ ρ) :
    ∃ c : CriticalPair L (T : Subgroup G) H V,
      LocalGeometry.SecondCase H (sourceOne L T V₁) (T : Subgroup G)
        (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma (c.Aone V₁) V₁ ρ ∧
      CriticalReciprocity.Earlier c (sourceOne L T V₁) K V₃ V₁ ∧
      1 < rank (Source.starImage H c.Vgamma) := by
  let := vh_elementary d hH
  have he := CriticalSource.earlier_inputs d hH hF9 hcentral hcomm ρ hρ
  have hedge := Comparison.local_edge d hF9
  have hz := hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  let Q : CenterQuotientAction H (Source.UH H V₃) V₁ := {
    normalizes := le_normalizer_conjugateSpanBy V₃ H
    action := uAction H V₃ V₁ hz
    apply_mk := quotientAction_apply H (Source.UH H V₃) V₁ _ hz }
  let s := CriticalInputs.sourceSection H V₃ V₁ ρ hρ hF9.plus_le_H
    (d.line_le_plane.trans d.plane_le_seed) hF9.H_centralizes
  have hterminal (c : CriticalPair L (T : Subgroup G) H V) : Source.VH H V ≤
      (edgeGroup L (T : Subgroup G) H c.gamma c.previous).pCoreIn 2 := by
    have hh := (f9_endpoint_edge_cores _ hF9 c (he.geometry c).length).1
    change Source.VH H V ≤ (vertexGroup _ _ _ c.previous ⊓ vertexGroup _ _ _ c.gamma).pCoreIn 2 at hh
    rw [inf_comm] at hh
    exact hh
  have hplace (c : CriticalPair L (T : Subgroup G) H V) :
      ∃ y : H, c.Vgamma.map (MulAut.conj (y : G)).toMonoidHom ≤
        (sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2 := by
    obtain ⟨y, _, hy, _⟩ := exists_second_to_base c (sourceOne L T V₁)
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2)
      (by have := (he.geometry c).length; omega) hedge (he.initial_core c) le_rfl
    exact ⟨y, hy⟩
  have hstrict (c : CriticalPair L (T : Subgroup G) H V) :
      Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
    have hg := he.geometry c
    obtain ⟨hb, hγ⟩ := no_critical_transvections d earlier localEarlier hG64 hH hKH hK hN hKT e
      htheta h13 hcover ρ hρ c hedge (hterminal c) hg.Vgamma_H (hplace c)
    have hforbidβ {P : Subgroup G} (hP : P ≤ CriticalReciprocity.Vbeta c)
        (ht : TransvectionGroup Q P) : False := by
      obtain ⟨a, ha, hn, hc⟩ := source_transvection_group_actor ρ hρ Q P ht
      exact hb ⟨a, LocalGeometry.starImage_mono H hP ha, hn, hc⟩
    have hforbidγ (ht : TransvectionGroup Q (c.Ugamma V₃)) : False := by
      obtain ⟨a, ha, hn, hc⟩ := source_transvection_group_actor ρ hρ Q _ ht
      exact hγ ⟨a, LocalGeometry.starImage_mono H
        (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)) ha, hn, hc⟩
    have hγH : c.Ugamma V₃ ≤ H :=
      (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans hg.Vgamma_H
    have hUA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) :=
      ((conjugateSpanBy_mono d.seed_le le_rfl).trans hg.VH_endpoint).trans
        (SectionActions.CriticalPair.normalizes_Aone c V₁ hz)
    have hs : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
      by_contra hn
      have hfull := eq_of_le_of_not_lt (commutatorPreimage_le _ _ _) hn
      rcases transvection_of_Dgamma_eq c V₃ V₁ Q d.seed_le hz d.line_card hγH
        hg.VH_endpoint hUA hg.lines_disjoint he.centralizer (he.failure c) hfull with ht | ht
      · exact hforbidβ (CriticalReciprocity.Ubeta_le_Vbeta c V₃ d.seed_le) ht
      · exact hforbidβ le_rfl ht
    refine ⟨?_, hs⟩
    by_contra hn
    have hfull := eq_of_le_of_not_lt (commutatorPreimage_le _ _ _) hn
    exact hforbidγ (transvection_of_DH_eq_Dgamma_lt c V₃ V₁ Q d.line_card hγH hUA
      hg.lines_disjoint hfull hs)
  obtain ⟨initial, _, _⟩ := (localNaturalSetup d).exists_criticalPair d.abelian_span hF9
  obtain ⟨c, hDH, hDγ, hp, hcmp, hquad⟩ :=
    (localNaturalSetup d).exists_quadratic_selection d.abelian_span hF9 s initial
      (hstrict initial).1 (hstrict initial).2
  have hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
    apply le_antisymm
    · rw [← hKT]
      exact sup_le_sup_left le_sup_right K
    · exact sup_le hKH hH.1.2
  have hr := source_reciprocal_inputs d hH hF9 hgen hK hN e hcentral hcomm ρ hρ
    c hDH hDγ hcmp
  refine ⟨c, ?_, hr, source_actor_rank_gt_one d earlier localEarlier hG64 hH hKH hK hN hKT
    e htheta h13 hcover ρ hρ c hr hp⟩
  exact ⟨hDγ, hDH, hp, hcmp, hquad.1, hquad.2.1, hquad.2.2, hplace c⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
