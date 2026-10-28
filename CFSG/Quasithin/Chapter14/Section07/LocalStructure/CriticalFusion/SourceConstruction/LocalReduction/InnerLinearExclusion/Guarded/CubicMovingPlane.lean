module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicMovingPlane
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.CubicActionQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.CubicGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.CubicLocalStructure
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.ExtraspecialCubicGeometry

/-!
# Same-group structural-input version

This proof uses only `Structural1222At` and `Theorem12213At` at the original G,T.
It preserves the literal groups and quotient maps of the source argument below.

# Cubic completions that move the original flag plane

For D = ⟨L₂,Y,T⟩ and E = ⟨V₁^D⟩, assume that the two-perfect cubic
actor Y lies in the original point stabilizer and moves V₂. If its image
normalized the plane residual image modulo C_D(E), it would normalize V₂.
Its fixed line then makes its entire plane action trivial, a contradiction.

The residual obstruction gives the exact solvable action kernel, the full
Goldschmidt quotient intersection and trivial quotient two-core. Every
C-component of D acts faithfully on a nonzero signalizer module. The earlier
faithful classification therefore gives its intrinsic A₅ or L₃(2) quotient.
Its actual action image is a normal component, with the literal residual
orientation and generation alternatives of F.6.10. Point-residual
normalization is not a premise of these moving-plane results.

This is the nonsolvable reduction for the contrary case of 14.7.2(3);
the subsequent model exclusions and solvable contradiction remain separate.
Source: Aschbacher–Smith, 14.5.3–8, printed pp.1013–1015, and 14.7.2,
printed p.1043, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A moving two-perfect actor cannot preserve the plane residual modulo the point-span centralizer. -/
theorem cubic_plane_normalizer_obstruction_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    ¬ Y ≤ normalizer ((F.Li L 2 ⊔ (D ⊓ centralizer (W : Set G)) : Subgroup G) : Set G) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let C := D ⊓ centralizer (W : Set G)
  have hXD : F.Li L 2 ≤ D := by
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  have hplane : F.Vi 2 ≤ W := by
    rw [←plane_eq_point_residual_span h structural]
    exact conjugateSpanBy_mono le_rfl hXD
  have hCplane : C ≤ normalizer (F.Vi 2 : Set G) :=
    (inf_le_right.trans (centralizer_le hplane)).trans (Subgroup.centralizer_le_normalizer _)
  have hspan : conjugateSpanBy (F.Vi 1) (F.Li L 2 ⊔ C) = F.Vi 2 := by
    apply le_antisymm
    · exact conjugateSpanBy_le (F.monotone (by decide : 1 ≤ 2))
        (sup_le ((F.Li_le L 2).trans inf_le_right) hCplane)
    · rw [←plane_eq_point_residual_span h structural]
      exact conjugateSpanBy_mono le_rfl le_sup_left
  change ¬ Y ≤ normalizer ((F.Li L 2 ⊔ C : Subgroup G) : Set G)
  intro hnorm
  apply hm
  apply moving_plane_centralized_of_normalized Y hYH hYp
  change Y ≤ normalizer (F.Vi 2 : Set G)
  rw [←hspan]
  exact normalizes_conjugateSpanBy _ _ Y hYH hnorm

/-- The obstruction in the literal quotient by the centralizer of the original point span. -/
theorem cubic_generated_action_normalizer_obstruction_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    ¬ (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  have hYD : Y ≤ D := le_sup_left.trans le_sup_right
  have hXD : F.Li L 2 ≤ D := by
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  have hWD : W ≤ D := conjugateSpanBy_le_self
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans le_sup_right)))
  have hC : C.map D.subtype = D ⊓ centralizer (W : Set G) := by
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWD]
  change ¬ (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _)
  intro him
  have hpre := map_le_iff_le_comap.mp him
  rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective C),
    comap_map_eq,QuotientGroup.ker_mk'] at hpre
  have hh := (map_mono (f := D.subtype) hpre).trans (le_normalizer_map D.subtype)
  rw [map_subgroupOf_eq_of_le hYD,Subgroup.map_sup,map_subgroupOf_eq_of_le hXD,hC] at hh
  exact cubic_plane_normalizer_obstruction_of_moving_plane h structural Y hYH hm hYp hh

/-- Original cubic completion with a moving plane; no normalization of L₁ is assumed. -/
theorem cubic_generated_action_kernel_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let C := centralizer (W.subgroupOf D : Set D)
    (F.P L).subgroupOf D ⊓ C = pCore 2 D ∧
      (Y ⊔ (T : Subgroup G)).subgroupOf D ⊓ C = pCore 2 D ∧
      Group.IsSolvable C := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  have hWC := (cubic_generated_local_structure h hab structural previous Y hYH he).2.2.2.2
  have hQC : pCore 2 D ≤ centralizer (W.subgroupOf D : Set D) := by
    intro x hx w hw
    apply Subtype.ext
    exact (le_centralizer_iff.mp hWC) (mem_map_of_mem D.subtype hx) w hw
  apply ChapterF.IsGoldschmidtTriple.kernel_intersections_of_residual_escape (cubic_goldschmidt_triple h structural Y hYH he)
    _ hQC
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  rw [hr.1,hr.2]
  exact cubic_generated_action_normalizer_obstruction_of_moving_plane h structural Y hYH hm hYp

/-- Original cubic completion with a moving plane; no normalization of L₁ is assumed. -/
theorem cubic_generated_action_triple_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ((F.P L).subgroupOf D).map q ⊓ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q =
        ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple ((F.P L).subgroupOf D |>.map q)
        ((Y ⊔ (T : Subgroup G)).subgroupOf D |>.map q) ∧
      pCore 2 (D ⧸ C) = ⊥ := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  have hQC : pCore 2 D ≤ C := by
    intro x hx
    have hh := (cubic_generated_action_kernel_of_moving_plane h hab structural previous
      Y hYH hm hYp hYT he).1
    rw [←hh] at hx
    exact hx.2
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  have ho : ¬ ((pResidual 2 ((Y ⊔ (T : Subgroup G)).subgroupOf D)).map
      ((Y ⊔ (T : Subgroup G)).subgroupOf D).subtype).map (QuotientGroup.mk' C) ≤
      normalizer (((pResidual 2 ((F.P L).subgroupOf D)).map
        ((F.P L).subgroupOf D).subtype).map (QuotientGroup.mk' C) : Set _) := by
    rw [hr.1,hr.2]
    exact cubic_generated_action_normalizer_obstruction_of_moving_plane h structural Y hYH hm hYp
  obtain ⟨hi,ht⟩ := ChapterF.IsGoldschmidtTriple.quotient_triple_of_residual_escape
    (cubic_goldschmidt_triple h structural Y hYH he) C hQC ho
  have hinter : (F.P L).subgroupOf D ⊓ (Y ⊔ (T : Subgroup G)).subgroupOf D =
      (T : Subgroup G).subgroupOf D := by
    apply le_antisymm
    · intro x hx
      have hh : (x : G) ∈ F.P L ⊓ F.H :=
        ⟨hx.1,(sup_le hYH (F.invariant 1)) hx.2⟩
      rwa [plane_parabolic_inf_point h structural] at hh
    · intro x hx
      exact ⟨F.binary_sylow_le_P L hx,
        (le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G)) hx⟩
  rw [hinter] at hi
  exact ⟨hi,ht,(cubic_generated_span_reduced h hab structural previous Y hYH he).quotient_pCore_eq_bot⟩

open ChapterA.Section04 Theory.GroupTheory Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- The actual faithful component and its intrinsic quotient in the moving-plane branch. -/
theorem cubic_generated_component_faithful_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    J.map D.subtype ∈ Chapter1.L G (T : Subgroup G) ∧
      IsFaithfulSignalizerType (J.map D.subtype) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let C := centralizer (W.subgroupOf D : Set D)
  let JG := J.map D.subtype
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hJD : JG ≤ D := map_subtype_le J
  have hJDG : JG.subgroupOf D = J := comap_map_eq_self_of_injective D.subtype_injective J
  have hDH : D ∈ Chapter1.H G := by
    intro hz
    apply cubic_generated_core_ne_bot h hab structural previous Y hYH he
    exact ((pCore 2 D).map_eq_bot_iff_of_injective D.subtype_injective).mp hz
  have hJL : JG ∈ Chapter1.L G (T : Subgroup G) := Chapter1.mem_L_of_cComponent hDH
    ⟨T.subtype hTD,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD]⟩
    hJD (hJDG ▸ hJ)
  have hp : IsPPerfect 2 J :=
    (Chapter1.Section02.Adequate.mem_L_isPPerfect hJL).of_surjective
      (J.equivMapOfInjective D.subtype D.subtype_injective).symm.toMonoidHom
      (J.equivMapOfInjective D.subtype D.subtype_injective).symm.surjective
  let : Group.IsSolvable C := (cubic_generated_action_kernel_of_moving_plane h hab structural previous Y hYH hm hYp hYT he).2.2
  have hnot : ¬ J ≤ C := by
    intro hj
    exact hJ.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hj) (inclusion_injective hj))
  have hmod : intrinsicSignalizerModule J ≠ ⊥ := by
    intro hz
    apply hnot
    have hmove : ⁅W.subgroupOf D,J⁆ = ⊥ := by
      apply bot_unique
      exact (commutator_mono
        (cubic_generated_span_reduced h hab structural previous Y hYH he).le_reducedPSubgroup
        le_rfl).trans ((reduced_commutator_le_intrinsicModule J hJ.subnormal hp).trans hz.le)
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hmove)
  refine ⟨hJL,Chapter1.Section02.Adequate.mem_L_isSignalizerType T
    (h.source.simpleQTKE.evenCharacteristic T) hJL,?_⟩
  rw [intrinsicSignalizerModule_map_of_injective D.subtype D.subtype_injective J]
  exact fun hz => hmod (((intrinsicSignalizerModule J).map_eq_bot_iff_of_injective
    D.subtype_injective).mp hz)

open ChapterA.Section04 Theory.GroupTheory Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- The actual faithful component and its intrinsic quotient in the moving-plane branch. -/
theorem cubic_generated_nonsolvable_component_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hns : ¬ Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    ∃ J : Subgroup G, J ≤ D ∧ (J.subgroupOf D).IsCComponent ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧ IsFaithfulSignalizerType J ∧
      (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal ∧
      (Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  obtain ⟨J,hJ⟩ := exists_isCComponent_of_not_isSolvable hns
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_moving_plane h hab structural previous Y hYH hm hYp hYT he J hJ
  obtain ⟨hmodel,hnJ,hmax⟩ := faithful (J.map D.subtype) hJL hJf
  refine ⟨J.map D.subtype,map_subtype_le J,?_,hmax,hJf,hnJ,hmodel⟩
  change ((J.map D.subtype).subgroupOf D).IsCComponent
  simpa only [subgroupOf,comap_map_eq_self_of_injective D.subtype_injective] using hJ

open Chapter14.Section04.LargerDimension.LocalAction.Components Theory.GroupTheory in
/-- The actual component image and residual orientation for a moving cubic actor. -/
theorem cubic_generated_component_action_kernel_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmove : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    (q.subgroupMap J).ker = pCore 2 J ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* J.map q) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  let JG := J.map D.subtype
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_moving_plane h hab structural previous Y hYH hmove hYp hYT he J hJ
  have hm := (faithful JG hJL hJf).1
  let : IsSimpleGroup (JG ⧸ pCore 2 JG) := by
    rcases hm with he | he
    · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact he.some.isSimpleGroup
    · let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
      exact he.some.isSimpleGroup
  let eJ := J.equivMapOfInjective D.subtype D.subtype_injective
  let eQ := QuotientGroup.congr (pCore 2 J) (pCore 2 JG) eJ (pCore_map_iso 2 eJ)
  let : IsSimpleGroup (J ⧸ pCore 2 J) := eQ.isSimpleGroup
  let := hJ.perfect
  have hrad : solvableRadical J = pCore 2 J :=
    PerfectCoreTwoExtension.radical_eq_core
  have htop : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.subgroupOf le_rfl
  let : Group.IsSolvable C := (cubic_generated_action_kernel_of_moving_plane h hab structural previous Y hYH hmove hYp hYT he).2.2
  have hnot : ¬ J ≤ C := by
    intro hj
    exact hJ.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hj) (inclusion_injective hj))
  have hkne : (q.subgroupMap J).ker ≠ ⊤ := by
    intro hz
    apply hnot
    intro x hx
    have hh : (⟨x,hx⟩ : J) ∈ (q.subgroupMap J).ker := hz.symm ▸ mem_top _
    exact (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val hh)
  have hQC : pCore 2 D ≤ C :=
    ((cubic_generated_action_kernel_of_moving_plane h hab structural previous Y hYH hmove hYp hYT he).1.symm.le).trans inf_le_right
  have hk : (q.subgroupMap J).ker = pCore 2 J := by
    apply le_antisymm
    · exact (kernel_le_solvableRadical_of_top_isCComponent htop _ hkne).trans hrad.le
    · rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact (pCore_subnormal_eq_comap 2 hJ.subnormal).le.trans (comap_mono hQC)
  exact ⟨hk,⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective J))⟩⟩

open Chapter14.Section04.LargerDimension.LocalAction.Components Theory.GroupTheory in
/-- The actual component image and residual orientation for a moving cubic actor. -/
theorem cubic_generated_component_action_reduction_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmove : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    J.Normal ∧ IsComponent (D ⧸ C) (J.map q) ∧ (J.map q).Normal ∧
      ((((F.Li L 2).subgroupOf D).map q ≤ J.map q ∧
        J.map q ⊔ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q = ⊤) ∨
       ((Y.subgroupOf D).map q ≤ J.map q ∧
        J.map q ⊔ ((F.P L).subgroupOf D).map q = ⊤)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  let JG := J.map D.subtype
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_moving_plane h hab structural previous Y hYH hmove hYp hYT he J hJ
  have hm := (faithful JG hJL hJf).1
  let : IsSimpleGroup (JG ⧸ pCore 2 JG) := by
    rcases hm with he | he
    · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact he.some.isSimpleGroup
    · let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
      exact he.some.isSimpleGroup
  let eJ := J.equivMapOfInjective D.subtype D.subtype_injective
  let eQ := QuotientGroup.congr (pCore 2 J) (pCore 2 JG) eJ (pCore_map_iso 2 eJ)
  let : IsSimpleGroup (J ⧸ pCore 2 J) := eQ.isSimpleGroup
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_moving_plane h hab structural previous faithful Y hYH hmove hYp hYT he J hJ
  let : IsSimpleGroup (J.map q) := e.symm.isSimpleGroup
  let := hJ.perfect
  let : Group.IsPerfect (J.map q) := Group.IsPerfect.map q
  have hcenter : center (J.map q) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (J.map q)) inferInstance).resolve_right
      (fun hz => Group.IsPerfect.not_isMulCommutative (J.map q) (center_eq_top_iff.mp hz))
  let : IsQuasisimple (J.map q) := ⟨((QuotientGroup.quotientMulEquivOfEq hcenter).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hj : IsComponent (D ⧸ C) (J.map q) :=
    ⟨hJ.subnormal.map (QuotientGroup.mk'_surjective C),inferInstance⟩
  obtain ⟨_,ht,hcore⟩ := cubic_generated_action_triple_of_moving_plane h hab structural previous Y hYH hmove hYp hYT he
  have hSQ := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1
  obtain ⟨hnq,hcases⟩ := ChapterF.SourceAssembly.source_component_reduction
    (ChapterA.Section02.theoremA_knownSimple (G := D)) hSQ q (QuotientGroup.mk'_surjective C)
    ht hcore hj
  let : Group.IsSolvable C := (cubic_generated_action_kernel_of_moving_plane h hab structural previous Y hYH hmove hYp hYT he).2.2
  have hnJ := cComponent_normal_of_quotient_normal hJ C hnq
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  rw [←map_embedded_pResidual,←map_embedded_pResidual,hr.1,hr.2] at hcases
  exact ⟨hnJ,hj,hnq,hcases⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
