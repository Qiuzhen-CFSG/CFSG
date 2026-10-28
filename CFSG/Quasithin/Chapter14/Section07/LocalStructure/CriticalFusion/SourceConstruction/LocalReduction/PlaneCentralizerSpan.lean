module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCubic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentEscapeAt
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags.Construction
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneClosure
public import Theory.GroupTheory.Commutator.TwoOrbitSpan
public import Theory.GroupAction.BinaryPointCentralizerGeneration

/-!
# The plane-centralizer orbit obstruction before local recognition

Point-core movement identifies L₂ with the two-residual of the actual
G₂-normal closure of O₂(G₁). Thus G₂ normalizes L₂. If the orbit of V
under I intersect G₂ generated U_I, then L₂ would normalize U_I; together
with L₁T this contradicts the original unique maximal overgroup of LT.

The strict containment descends through the literal point kernel V₁.
The centralizer of the quotient plane is exactly the image of I intersect
G₂, since V₂/V₁ has order two. This proves the centralizer-orbit assertion
of 14.7.37(1) from the point-core movement in 14.7.4(1).

For the normal-point branch, movement is proved using only the earlier
same-G,T structural input: the normal point image is cubic, whereas
13.3.14(c) would force a nontrivial two-core if the plane were fixed.
The guarded original applications discharge this movement premise.
The full binary linear action is then excluded by two-vector transitivity,
which would make that same centralizer orbit generate the whole section.

General point-core movement, the remaining representation alternatives,
and the residual classification through 14.7.52 remain source obligations.
No Data or final residual identification is used here.

Source: Aschbacher--Smith, 14.7.4(1--2), 14.7.37(1--2), printed
pp.1043 and 1059 of refs/quasithin.pdf; 13.3.14(c), pp.891--892.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter12.Section09.NaturalSource
open Chapter14.Section04.LargerDimension.LocalAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem span_plane_residual_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (pResidual 2 (F.P L)).map (F.P L).subtype = F.Li L 2 := by
  have hLT : (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)).map
      (L ⊔ (T : Subgroup G)).subtype = L :=
    embedded_pResidual_join_pGroup L _ ((pResidual_eq_top_iff 2 L).mp h.residual)
      T.isPGroup' (h.sylow_normalizes_at structural)
  have hN : L ⊓ F.Gi 2 ≤ F.P L := by
    intro x hx
    exact ⟨mem_sup_left hx.1,mem_iInf.mpr fun i => mem_iInf.mpr fun hi => by
      have : i = 2 := by omega
      subst i
      exact hx.2⟩
  have hR : (pResidual 2 (F.P L)).map (F.P L).subtype ≤ L ⊓ F.Gi 2 :=
    le_inf ((embedded_pResidual_mono 2 (show F.P L ≤ L ⊔ (T : Subgroup G) from inf_le_left)).trans_eq hLT)
      ((map_subtype_le _).trans (F.P_le_G₂ (by decide) L h.chosen.normalizes))
  simpa [InvariantFlag.Li] using
    (embedded_pResidual_eq_of_le_of_residual_le 2 hN hR).symm

private theorem span_parabolic_quotient_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Nonempty ((F.P L ⧸ pCore 2 (F.P L)) ≃* Equiv.Perm (Fin 3)) := by
  let := h.chosen.elementary
  let f := F.binaryPermutationAction (by decide) L h.chosen.normalizes
  have hf : Function.Surjective f :=
    F.binaryPermutationAction_surjective (by decide) L h.chosen.normalizes (h.full_LT_action_at structural)
  have hk : f.ker = pCore 2 (F.P L) :=
    (F.binaryPermutationAction_ker (by decide) L h.chosen.normalizes).trans
      (F.binaryPlaneAction_ker_eq_twoCore (by decide) L h.chosen.normalizes
        (h.full_LT_action_at structural) (h.centralizer_LT_at structural))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- The full original plane normalizer preserves L₂, by identifying L₂
with the residual of the normal closure of the moving point two-core. -/
theorem plane_normalizer_normalizes_second_residual_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥) :
    F.Gi 2 ≤ normalizer (F.Li L 2 : Set G) := by
  let := h.chosen.elementary
  let R := planeCoreClosure F
  have hRP : F.H.pCoreIn 2 ≤ F.P L := by
    have hQT := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hQT
    have hQT' : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := hQT hx
      exact hy
    exact hQT'.trans (F.binary_sylow_le_P L)
  have hout : ¬ F.H.pCoreIn 2 ≤ (F.P L).pCoreIn 2 := by
    intro hc
    apply hm
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hc.trans (((F.binary_parabolic_core (by decide) L h.chosen.normalizes
      (h.full_LT_action_at structural) (h.centralizer_LT_at structural)).1).ge.trans inf_le_right)
  obtain ⟨e⟩ := span_parabolic_quotient_at h structural (F := F)
  have hgen : R ⊔ (F.P L).pCoreIn 2 = F.P L := by
    rw [show R = conjugateSpanBy (F.H.pCoreIn 2) (F.P L) from
      planeCoreClosure_eq_parabolic_span h F]
    exact (core_hyperplane_and_generation (F.P L) (F.H.pCoreIn 2) hRP
      (isPGroup_pCoreIn 2 F.H) hout e).2
  have hRG : R ≤ F.Gi 2 := (planeCoreClosure_le_parabolic h F).trans
    (F.P_le_G₂ (by decide) L h.chosen.normalizes)
  have hn : F.Gi 2 ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRG).mp (planeCoreClosure_normal h F)
  have hres : (pResidual 2 R).map R.subtype = F.Li L 2 := by
    apply (embedded_pResidual_eq_of_le_of_residual_le 2
      (planeCoreClosure_le_parabolic h F) ?_).trans (span_plane_residual_at h structural)
    let R' := R.subgroupOf (F.P L)
    let : R'.Normal := (normal_subgroupOf_iff_le_normalizer
      (planeCoreClosure_le_parabolic h F)).mpr
        ((F.P_le_G₂ (by decide) L h.chosen.normalizes).trans hn)
    have hs : R' ⊔ pCore 2 (F.P L) = ⊤ := by
      apply map_injective (F.P L).subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (planeCoreClosure_le_parabolic h F),
        ←MonoidHom.range_eq_map,range_subtype]
      exact hgen
    have hp : IsPGroup 2 ((F.P L) ⧸ R') :=
      isPGroup_quotient_of_sup_eq_top _ _ pCore_isPGroup hs
    have hpr : pResidual 2 (F.P L) ≤ R' := sInf_le ⟨inferInstance,hp⟩
    exact (map_mono (f := (F.P L).subtype) hpr).trans_eq
      (map_subgroupOf_eq_of_le (planeCoreClosure_le_parabolic h F))
  rw [←hres]
  exact hn.trans (normalizer_le_normalizer_characteristic_image R (pResidual 2 R))

private theorem span_natural_action_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    NaturalThreeAction L V T := by
  refine ⟨?_,h.sylow_normalizes_at structural,h.chosen.normalizes,?_,?_⟩
  · change (pResidual 2 L).map L.subtype = L
    rw [h.residual,←MonoidHom.range_eq_map,range_subtype]
  · intro a
    obtain ⟨l,hl,he⟩ := h.full_L_action a
    refine ⟨⟨l,hl⟩,?_⟩
    ext v
    rw [Chapter14.Section04.LargerDimension.LocalAction.conjugation_apply]
    exact he v
  · rw [conjugation_ker]
    apply map_injective L.subtype_injective
    simpa only [subgroupOf_map_subtype,inf_comm,pCoreIn] using h.centralizer_L

/-- Before coordinates, even the plane-normalizer orbit of the seed is
proper in the original local span, once the original point core moves V₂. -/
theorem local_plane_normalizer_span_lt_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    conjugateSpanBy V (I ⊓ F.Gi 2) < F.UH I := by
  let := h.chosen.elementary
  let C := I ⊓ F.Gi 2
  have hle : conjugateSpanBy V C ≤ F.UH I := conjugateSpanBy_mono le_rfl inf_le_left
  apply lt_of_le_of_ne hle
  intro he
  have hIU : I ≤ normalizer (F.UH I : Set G) := le_normalizer_conjugateSpanBy V I
  have hL2U : F.Li L 2 ≤ normalizer (F.UH I : Set G) := by
    rw [←he]
    exact TwoOrbitSpan.normalizes_span V C (F.Li L 2)
      (((F.Li_le L 2).trans inf_le_left).trans h.chosen.normalizes)
      (inf_le_right.trans (plane_normalizer_normalizes_second_residual_at h structural hm))
  have hLTU : L ⊔ (T : Subgroup G) ≤ normalizer (F.UH I : Set G) := by
    let := h.chosen.elementary
    have hg := (NaturalFlags.naturalFlagData_of_invariant_flag
      (span_natural_action_at h structural) F 1 (one_mem L)).generated
    rw [←hg]
    exact sup_le (sup_le ((F.Li_one_le_of_mem_Hz hI).trans hIU) hL2U)
      ((F.sylow_le_of_mem_Hz hI).trans hIU)
  have hNM : normalizer (F.UH I : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hJN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN,hJN⟩)
    · exact F.localKernel_UH_isPGroup h.source.simpleQTKE L (normalizer (L : Set G)) I
        (by decide) h.chosen.le_sylow h.chosen.normalizes
        (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩) hI
    · intro hb
      exact h.chosen.ne_bot (le_bot_iff.mp ((le_conjugateSpanBy V I).trans hb.le))
    · exact hLTU
  exact hI.2.2 (hIU.trans hNM)

omit [Finite G] in
private theorem span_tilde_mono {A B : Subgroup G} (hAB : A ≤ B) :
    F.tilde A ≤ F.tilde B := map_mono (comap_mono hAB)

omit [Finite G] in
private theorem span_tilde_injective {A B : Subgroup G}
    (hAH : A ≤ F.H) (hBH : B ≤ F.H)
    (hPA : F.Vi 1 ≤ A) (hPB : F.Vi 1 ≤ B)
    (he : F.tilde A = F.tilde B) : A = B := by
  have he' : A.subgroupOf F.H = B.subgroupOf F.H :=
    map_injective_of_ker_le (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H))
      (by rw [QuotientGroup.ker_mk']; exact comap_mono hPA)
      (by rw [QuotientGroup.ker_mk']; exact comap_mono hPB) he
  simpa only [map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hBH] using
    congrArg (map F.H.subtype) he'

/-- Strictness survives in the source's literal quotient by V₁. -/
theorem local_plane_normalizer_tilde_span_lt_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    F.tilde (conjugateSpanBy V (I ⊓ F.Gi 2)) < F.tilde (F.UH I) := by
  let := h.chosen.elementary
  have hs := local_plane_normalizer_span_lt_at h structural hm I hI
  apply lt_of_le_of_ne (span_tilde_mono hs.le)
  intro he
  exact hs.ne (span_tilde_injective
    (hs.le.trans (F.UH_le_H I hI.2.1)) (F.UH_le_H I hI.2.1)
    ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
    ((F.le_seed 1).trans (le_conjugateSpanBy _ _)) he)

private theorem span_tilde_plane_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    Nat.card (F.tilde (F.Vi 2)) = 2 := by
  let := h.chosen.elementary
  have hPH : F.Vi 2 ≤ F.H := (F.le_seed 2).trans
    ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  let f := F.tildeMap (F.Vi 2) hPH
  have hk : f.ker = (F.Vi 1).subgroupOf (F.Vi 2) := by
    ext v
    rw [MonoidHom.mem_ker, ← Subtype.val_inj]
    change (F.tildeProjection ⟨v, _⟩ = 1) ↔ (v : G) ∈ F.Vi 1
    exact QuotientGroup.eq_one_iff _
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  have he := QuotientGroup.quotientKerEquivOfSurjective f (F.tildeMap_surjective _ _)
  have hker : Nat.card f.ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (F.monotone (by decide : 1 ≤ 2))).toEquiv]
    simpa using F.card 1 (by decide)
  have hplane : Nat.card (F.Vi 2) = 4 := by simpa using F.card 2 (by decide)
  rw [Nat.card_congr he.toEquiv,hker,hplane] at hc
  omega

/-- The quotient-plane centralizer is the literal image of the plane
normalizer. Both uses of the point kernel are retained. -/
theorem local_tilde_plane_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) :
    F.tilde I ⊓ centralizer (F.tilde (F.Vi 2) : Set F.G₁tilde) =
      F.tilde (I ⊓ F.Gi 2) := by
  let := h.chosen.elementary
  let q := F.tildeProjection
  have hPH : F.Vi 2 ≤ F.H := (F.le_seed 2).trans
    ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  have hpre : (F.tilde (F.Vi 2)).comap q = (F.Vi 2).subgroupOf F.H := by
    apply comap_map_eq_self
    change (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H)).ker ≤ _
    rw [QuotientGroup.ker_mk']
    exact comap_mono (F.monotone (by decide : 1 ≤ 2))
  have hN : (normalizer (F.tilde (F.Vi 2) : Set F.G₁tilde)).comap q =
      (F.Gi 2).subgroupOf F.H := by
    have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
    rw [comap_normalizer_eq_of_surjective _ hq,hpre]
    exact (subgroupOf_normalizer_eq hPH).symm
  have hC : normalizer (F.tilde (F.Vi 2) : Set F.G₁tilde) =
      centralizer (F.tilde (F.Vi 2) : Set F.G₁tilde) :=
    le_antisymm (normalizer_le_centralizer_of_card_two _ (span_tilde_plane_card h))
      (Subgroup.centralizer_le_normalizer _)
  rw [hC] at hN
  change (I.subgroupOf F.H).map q ⊓ _ = ((I ⊓ F.Gi 2).subgroupOf F.H).map q
  ext x
  constructor
  · rintro ⟨⟨i,hi,rfl⟩,hx⟩
    have hn : i ∈ (centralizer (F.tilde (F.Vi 2) : Set F.G₁tilde)).comap q := hx
    rw [hN] at hn
    exact ⟨i,⟨hi,hn⟩,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    refine ⟨⟨i,hi.1,rfl⟩,?_⟩
    have hn : i ∈ (F.Gi 2).subgroupOf F.H := hi.2
    rw [←hN] at hn
    exact hn

/-- Source 14.7.37(1), on the actual local section and its plane centralizer. -/
theorem local_plane_centralizer_tilde_span_lt_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    conjugateSpanBy (F.tilde V)
      (F.tilde I ⊓ centralizer (F.tilde (F.Vi 2) : Set F.G₁tilde)) <
        F.tilde (F.UH I) := by
  let := h.chosen.elementary
  have hVH : V ≤ F.H := (le_conjugateSpanBy V F.H).trans F.U_le_H
  have he : conjugateSpanBy (F.tilde V) (F.tilde (I ⊓ F.Gi 2)) =
      F.tilde (conjugateSpanBy V (I ⊓ F.Gi 2)) := by
    change conjugateSpanBy ((V.subgroupOf F.H).map F.tildeProjection)
      (((I ⊓ F.Gi 2).subgroupOf F.H).map F.tildeProjection) = _
    rw [←map_conjugateSpanBy]
    congr 1
    apply map_injective F.H.subtype_injective
    have hCH : I ⊓ F.Gi 2 ≤ F.H := inf_le_left.trans hI.2.1
    have hSH : conjugateSpanBy V (I ⊓ F.Gi 2) ≤ F.H :=
      conjugateSpanBy_le hVH (hCH.trans F.H.le_normalizer)
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hVH,
      map_subgroupOf_eq_of_le hCH,map_subgroupOf_eq_of_le hSH]
  rw [local_tilde_plane_centralizer h I,he]
  exact local_plane_normalizer_tilde_span_lt_at h structural hm I hI

/-- In the original normal-point branch, the point-core movement premise
is discharged before using the centralizer-orbit obstruction. -/
theorem local_plane_centralizer_tilde_span_lt_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    conjugateSpanBy (F.tilde V)
      (F.tilde I ⊓ centralizer (F.tilde (F.Vi 2) : Set F.G₁tilde)) <
        F.tilde (F.UH I) := by
  apply local_plane_centralizer_tilde_span_lt_at h (structural.at T) ?_ I hI
  intro he
  exact plane_moved_of_point_normal h structural hn
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))


/-- Normality at the original point gives movement using only same-G,T structure. -/
theorem plane_moved_of_point_normal_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  let A := (F.Li L 1).subgroupOf F.H
  let : A.Normal := hn
  have he := coreQuotientEquivImage 2 A
  have hc : Nat.card (star F (F.Li L 1)) = 3 := by
    change Nat.card (A.map (QuotientGroup.mk' (pCore 2 F.H))) = 3
    rw [←Nat.card_congr he.toEquiv]
    let e := subgroupOfEquivOfLe (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right)
    let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    rw [Nat.card_congr q.toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hp : IsPGroup 3 (star F (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using hc)
  intro hz
  have hne := Chapter13.Section03.Noncentrality.linearThree_star_core_ne_bot_of_plane_centralized
    h F hz
  have hstar : Chapter13.Section03.Noncentrality.star F.H (F.Li L 1)
      ((F.Li_le L 1).trans inf_le_right) = star F (F.Li L 1) := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact mem_map_of_mem (starMap F) a.property
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  rw [hstar] at hne
  exact hne (le_bot_iff.mp ((le_inf le_rfl le_top).trans
    (pCore_isPGroup.disjoint_of_coprime (hp.to_subgroup ⊤)
      (by decide : Nat.Coprime 2 3)).le_bot))

/-- The normal-point source branch with the actual many-overgroup guard.
No universal structural or local movement premise is introduced. -/
theorem original_plane_centralizer_tilde_span_lt_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    conjugateSpanBy (F.tilde V)
      (F.tilde F.H ⊓ centralizer (F.tilde (F.Vi 2) : Set F.G₁tilde)) <
        F.tilde F.U := by
  exact local_plane_centralizer_tilde_span_lt_at h (structural hmany)
    (plane_moved_of_point_normal_at h (structural hmany) hn) F.H
    (h.point_mem_Hz_at F (previous hmany))

/-- A full natural binary linear action contradicts the source plane orbit.
This uses the literal U_I/V₁ action, so it also applies after any natural
coordinate identification. -/
theorem local_tilde_action_not_surjective_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    ¬ Function.Surjective (F.localTildeAction I hI.2.1) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_UH_elementary h.source.simpleQTKE L
    (normalizer (L : Set G)) I (by decide) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩) hI
  have hVH : V ≤ F.H := (le_conjugateSpanBy V F.H).trans F.U_le_H
  have hPB : F.tilde (F.Vi 2) < F.tilde V := by
    apply lt_of_le_of_ne (span_tilde_mono (F.le_seed 2))
    intro he
    have he' := span_tilde_injective ((F.le_seed 2).trans hVH) hVH
      (F.monotone (by decide : 1 ≤ 2)) (F.le_seed 1) he
    have hc := F.card 2 (by decide)
    rw [he'] at hc
    have hc' : Nat.card V=8 := by simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    omega
  have hn : F.tilde I ≤ normalizer (F.tilde (F.UH I) : Set F.G₁tilde) :=
    F.tilde_normalizes I (F.UH I) (le_normalizer_conjugateSpanBy V I)
  intro hf
  have hfull : Function.Surjective (OddInvolutionFrattini.conjugation (F.tilde I) (F.tilde (F.UH I)) hn) := by
    intro a
    obtain ⟨i,hi⟩ := hf a
    refine ⟨F.tildeMap I hI.2.1 i,?_⟩
    have he : OddInvolutionFrattini.conjugation (F.tilde I) (F.tilde (F.UH I)) hn
        (F.tildeMap I hI.2.1 i) = F.localTildeAction I hI.2.1 i := by
      ext v
      rfl
    exact he.trans hi
  exact (local_plane_centralizer_tilde_span_lt_at h structural hm I hI).ne
    (conjugateSpan_eq_of_full_binary_point_centralizer
      (F.tilde (F.UH I)) (F.tilde V) (F.tilde (F.Vi 2)) (F.tilde I)
      (span_tilde_mono (le_conjugateSpanBy V I)) hPB (span_tilde_plane_card h) hn hfull)

/-- Guarded normal-point application of the natural linear-module exclusion. -/
theorem original_tilde_action_not_surjective_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ¬ Function.Surjective (F.localTildeAction F.H le_rfl) :=
  local_tilde_action_not_surjective_at h (structural hmany)
    (plane_moved_of_point_normal_at h (structural hmany) hn) F.H
    (h.point_mem_Hz_at F (previous hmany))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
