module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicActionQuotient
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Centralizing
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Contract
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentReduction
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Faithful components in the original cubic completion

The solvable centralizer C_D(W) cannot contain a C-component. The actual
reduced point span W therefore proves faithfulness in the original local
family. Earlier 14.3.4 supplies the genuine A₅ or PSL₃(2) quotient,
maximality, and relative normality in the Sylow join.

The component's radical is precisely its two-core. Hence its kernel on
W is exactly that two-core, so the model quotient is its literal image
in D/C_D(W). Applying the proved F.6.10 to this action quotient gives
normality in D and the two source orientations for residual containment
and generation. The final application supplies these facts for the
escaping cubic from the actual order-four chief interval.

EarlierFaithfulClassification is the named earlier 14.3.4 input; its
producer and final discharge remain qt-d-1434-source and qt-d-14775-source.
The nonsolvable alternatives still need exclusion to prove 14.5.8 and
complete the containment argument; this module does not assert solvability.
Source: Aschbacher–Smith, 14.5.8, printed pp.1014–1015, using
1.2.6/10, 14.3.4 and F.6.10; 14.7.20, p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open ChapterA.Section04 Theory.GroupTheory in
/-- Every C-component of the original cubic completion belongs to the
faithful local family: its action on the actual reduced point span is
nontrivial because the centralizer is solvable. -/
theorem cubic_generated_component_faithful_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
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
  let : Group.IsSolvable C := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).2.2
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

open ChapterA.Section04 Theory.GroupTheory in
/-- The original full point-normality interface. -/
theorem cubic_generated_component_faithful
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    J.map D.subtype ∈ Chapter1.L G (T : Subgroup G) ∧
      IsFaithfulSignalizerType (J.map D.subtype) := by
  apply cubic_generated_component_faithful_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (Y := Y)
    (hYH := hYH) (hYp := hYp) (hYT := hYT) (hout := hout)
    (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open ChapterA.Section04 Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- In the nonsolvable branch of 14.5.8, the original completion has an
actual faithful C-component with quotient A₅ or PSL₃(2). Only the named
earlier 14.3.4 classification remains explicit. -/
theorem cubic_generated_nonsolvable_component_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
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
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨hmodel,hnJ,hmax⟩ := faithful (J.map D.subtype) hJL hJf
  refine ⟨J.map D.subtype,map_subtype_le J,?_,hmax,hJf,hnJ,hmodel⟩
  change ((J.map D.subtype).subgroupOf D).IsCComponent
  simpa only [subgroupOf,comap_map_eq_self_of_injective D.subtype_injective] using hJ

open ChapterA.Section04 Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- The original full point-normality interface. -/
theorem cubic_generated_nonsolvable_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hns : ¬ Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    ∃ J : Subgroup G, J ≤ D ∧ (J.subgroupOf D).IsCComponent ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧ IsFaithfulSignalizerType J ∧
      (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal ∧
      (Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL)) := by
  apply cubic_generated_nonsolvable_component_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (hns := hns)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open Chapter14.Section04.LargerDimension.LocalAction.Components Theory.GroupTheory in
/-- The selected component has its exact two-core as kernel on W. Thus its
source A₅ or PSL₃(2) quotient is the actual image in D/C_D(W). -/
theorem cubic_generated_component_action_kernel_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
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
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he J hJ
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
  let : Group.IsSolvable C := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).2.2
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
    ((cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).1.symm.le).trans inf_le_right
  have hk : (q.subgroupMap J).ker = pCore 2 J := by
    apply le_antisymm
    · exact (kernel_le_solvableRadical_of_top_isCComponent htop _ hkne).trans hrad.le
    · rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact (pCore_subnormal_eq_comap 2 hJ.subnormal).le.trans (comap_mono hQC)
  exact ⟨hk,⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective J))⟩⟩

open Chapter14.Section04.LargerDimension.LocalAction.Components Theory.GroupTheory in
/-- The original full point-normality interface. -/
theorem cubic_generated_component_action_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
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
  apply cubic_generated_component_action_kernel_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open Chapter14.Section04.LargerDimension.LocalAction.Components Theory.GroupTheory in
/-- The source F.6.10 reduction applies to the actual action image of each
component. It proves normality back in D, and retains the two possible
orientations of residual containment and generation in D/C_D(W). -/
theorem cubic_generated_component_action_reduction_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
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
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he J hJ
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
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
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
  obtain ⟨_,ht,hcore⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have hSQ := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1
  obtain ⟨hnq,hcases⟩ := ChapterF.SourceAssembly.source_component_reduction
    (ChapterA.Section02.theoremA_knownSimple (G := D)) hSQ q (QuotientGroup.mk'_surjective C)
    ht hcore hj
  let : Group.IsSolvable C := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).2.2
  have hnJ := cComponent_normal_of_quotient_normal hJ C hnq
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  rw [←map_embedded_pResidual,←map_embedded_pResidual,hr.1,hr.2] at hcases
  exact ⟨hnJ,hj,hnq,hcases⟩

open Chapter14.Section04.LargerDimension.LocalAction.Components Theory.GroupTheory in
/-- The original full point-normality interface. -/
theorem cubic_generated_component_action_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
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
  apply cubic_generated_component_action_reduction_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04
  Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- The original order-four interval reduces solvability of its cubic
completion to the two actual faithful component models of 14.3.4. -/
theorem extraspecial_four_interval_cubic_component_alternative
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
      Group.IsSolvable D ∨ ∃ J : Subgroup G, ∃ _hJD : J ≤ D,
        (J.subgroupOf D).IsCComponent ∧ (J.subgroupOf D).Normal ∧
        J ∈ Chapter1.LStar G (T : Subgroup G) ∧ IsFaithfulSignalizerType J ∧
        (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal ∧
        (Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
          Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL)) ∧
        (q.subgroupMap (J.subgroupOf D)).ker = pCore 2 (J.subgroupOf D) ∧
        Nonempty ((J ⧸ pCore 2 J) ≃* (J.subgroupOf D).map q) ∧
        Theory.GroupTheory.IsComponent (D ⧸ centralizer (W.subgroupOf D : Set D)) ((J.subgroupOf D).map q) ∧
        ((J.subgroupOf D).map q).Normal ∧
        ((((F.Li L 2).subgroupOf D).map q ≤ (J.subgroupOf D).map q ∧
          (J.subgroupOf D).map q ⊔ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q = ⊤) ∨
         ((Y.subgroupOf D).map q ≤ (J.subgroupOf D).map q ∧
          (J.subgroupOf D).map q ⊔ ((F.P L).subgroupOf D).map q = ⊤)) := by
  classical
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  refine ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,?_⟩
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  by_cases hs : Group.IsSolvable D
  · exact Or.inl hs
  right
  obtain ⟨J,hJD,hJ,hmax,hf,hnJ,hmodel⟩ := cubic_generated_nonsolvable_component
    h hab structural previous faithful hn Y hYH hYp hYT hout he hs
  obtain ⟨hk,⟨e⟩⟩ := cubic_generated_component_action_kernel h hab structural previous faithful hn
    Y hYH hYp hYT hout he (J.subgroupOf D) hJ
  let eJ := subgroupOfEquivOfLe hJD
  let eQ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  obtain ⟨hnD,himage,hnimage,hcases⟩ := cubic_generated_component_action_reduction
    h hab structural previous faithful hn Y hYH hYp hYT hout he (J.subgroupOf D) hJ
  exact ⟨J,hJD,hJ,hnD,hmax,hf,hnJ,hmodel,hk,⟨eQ.symm.trans e⟩,himage,hnimage,hcases⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
