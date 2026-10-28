module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentEscapeAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCubic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.SolvableConclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.SourcePair.Selection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.QuotientAction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ThreeResidualOrbit
public import Theory.SpecificGroups.PSL3.BinaryComparison
public import Theory.GroupTheory.WreathTwoOddCoreImageDichotomy
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Excluding exchanged binary linear-three components

For an actual exchanged PSL₃(2) component, the source three-residual theorem
identifies its entire Sylow orbit with O^{3′}(I). This supplies the genuine
marked pair input, with the original point residual and Sylow subgroup.
The pair's compatible parabolics construct a solvable overgroup whose
intrinsic two-core quotient is S₃ wreath C₂.

Source 14.7.29 makes this overgroup normalize the original point residual.
Its image in the same two-core quotient is therefore normal of order three.
The wreath odd-core kernel dichotomy excludes such a subgroup. Transport
through the exact component quotients proves normality of every original
PSL₃(2) component and membership of KL₁T in the same local family.
This proof uses only the same original group and Sylow hypotheses; it does
not use the universal normal-component theorem or source 14.7.47.

Source: Aschbacher–Smith, the opening case of 14.7.32, printed p.1056,
refs/quasithin.pdf. The marked parabolic construction is shared with
13.8.16(1), but no A₆ flag or theta hypothesis is used here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components
open Swapped

private theorem wreath_normal_cubic_impossible {X : Type*} [Group X] [Finite X]
    (e : X ≃* LinearThree.WreathModel.W) (hc : Nat.card X = 72)
    (A : Subgroup X) [A.Normal] (hA : Nat.card A = 3) : False := by
  have hindex := wreathTwo_oddCore_index_eight ⟨e⟩
  have hcore := (pPrimeCore 2 X).card_mul_index
  rw [hindex,hc] at hcore
  have hcore9 : Nat.card (pPrimeCore 2 X) = 9 := by omega
  let q := QuotientGroup.mk' A
  have hi := A.card_mul_index
  rw [hA,hc] at hi
  have hi24 : A.index = 24 := by omega
  rcases wreathTwo_oddCore_le_ker_or_nine_dvd_range ⟨e⟩ q with h | h
  · rw [QuotientGroup.ker_mk'] at h
    have hd := card_dvd_of_le h
    rw [hcore9,hA] at hd
    norm_num at hd
  · have hr : q.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective A)
    rw [hr,card_top] at h
    change 9 ∣ A.index at h
    rw [hi24] at h
    norm_num at h

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem linearThree_point_parabolic_solvable
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Group.IsSolvable (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) := by
  let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
  let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable (B ⧸ pCore 2 B) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (pointQuotientEquiv_at (F := F) h structural).toMonoidHom)
      (pointQuotientEquiv_at (F := F) h structural).injective
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 B)).mpr ⟨inferInstance,inferInstance⟩

/-- The actual exchanged PSL₃(2) pair in an original reduced local. -/
theorem local_linearThree_sourcePair_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (eK : Chapter13.Section08.Source.starImage I K ≃* Matrix.PSL3Two.PSL)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = I)
    (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K) :
    Nonempty (LinearThree.WreathOvergroup.SourcePair.Input I (F.Li L 1) (T : Subgroup G)
      K (conjugateSpanBy K (T : Subgroup G))) := by
  have hTI := F.sylow_le_of_mem_Hz hI
  have hi : (normalizer (K.subgroupOf I : Set I)).index = 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
      (local_star_sqtk h I hI) hK with hn | hi
    · exact (hmoving (conjugateSpan_eq_of_normal I K T hKI hTI hn)).elim
    · exact hi.1
  obtain ⟨t,ht,htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  let e := (cComponentTwoCoreQuotientEquiv hK).trans eK
  let : IsQuasisimple ((K.subgroupOf I) ⧸ pCore 2 (K.subgroupOf I)) :=
    WholeResidualAssembly.GuardedSource.local_component_twoCore_isQuasisimple h hab structural previous faithful I hI _ hK
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup ((K.subgroupOf I) ⧸ pCore 2 (K.subgroupOf I)) := e.isSimpleGroup
  have hd : 3 ∣ Nat.card ((K.subgroupOf I) ⧸ pCore 2 (K.subgroupOf I)) := by
    rw [Nat.card_congr e.toEquiv,
      ←Nat.card_congr Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.toEquiv,
      Atlas.Comparisons.Exceptional.psl2Seven_card]
    decide
  have hr : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hm : ClassicalGroup.IsPSL ((K.subgroupOf I) ⧸ pCore 2 (K.subgroupOf I)) 2 7 :=
    ⟨ZMod 7,inferInstance,inferInstance,Nat.card_zmod 7,
      ⟨e.trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm⟩⟩
  have he := Chapter1.Section02.nonnormal_component_threeResidual hK hi hd hr
    (.linear_prime 7 (by decide) (by decide) hm)
  have he' := congrArg (map I.subtype) he
  rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hKI,
    ←MonoidHom.range_eq_map,range_subtype] at he'
  have hres : (primeToResidual 3 I).map I.subtype = conjugateSpanBy K (T : Subgroup G) := by
    rw [he',orbit_eq_two_conjugates I K I hKI le_rfl hi (hTI ht) htn,
      orbit_eq_two_conjugates I K T hKI hTI hi ht htn]
  exact ⟨{
    ambientSylow := T
    ambientSylow_eq := rfl
    base_le := sup_le (F.Li_one_le_of_mem_Hz hI) hTI
    component_le := hKI
    component := hK
    quasisimple := (WholeResidualAssembly.GuardedSource.local_component_star_isComponent h hab structural previous faithful I hI _ hK).2
    model := eK
    mover := t
    mover_mem := ht
    mover_not_normalizes := htn
    orbit_index := hi
    orbit_eq := orbit_eq_two_conjugates I K T hKI hTI hi ht htn
    generated := by simpa only [sup_assoc] using hgen.symm
    residual := hres
    seed_twoPerfect := isPPerfect_embedded_pResidual 2 _
    seed_quotient_card := Or.inl (pointResidual_core_quotient_card_at h structural)
    seed_normalized := ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural)
    solvable_base := linearThree_point_parabolic_solvable h structural }⟩

/-- Exchanged PSL₃(2) components contradict the original point cubic in
an actual solvable parabolic overgroup. -/
theorem local_reduced_linearThree_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (eK : Chapter13.Section08.Source.starImage I K ≃* Matrix.PSL3Two.PSL)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = I)
    (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K) : False := by
  obtain ⟨s⟩ := local_linearThree_sourcePair_at h hab structural previous faithful I K hI hKI hK eK hgen hmoving
  let J := s.parabolicPair.overgroup
  have hbase : F.Li L 1 ⊔ (T : Subgroup G) ≤ J := s.parabolicPair_overgroup_spec.1
  have hJH : J ≤ F.H := s.parabolicPair_overgroup_spec.2.1.trans hI.2.1
  have hnorm := WholeResidualAssembly.GuardedSource.point_normalized_solvable_normalizes_point d h hab structural previous faithful earlier
    J hJH s.parabolicPair_overgroup_spec.2.2 (hbase.trans J.le_normalizer)
  let A := (F.Li L 1).subgroupOf J
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hbase)).mpr hnorm
  let B := A.map (QuotientGroup.mk' (pCore 2 J))
  let : B.Normal := (inferInstance : A.Normal).map _ (QuotientGroup.mk'_surjective _)
  let eq := subgroupOfEquivOfLe (le_sup_left.trans hbase : F.Li L 1 ≤ J)
  let eq' := QuotientGroup.congr _ _ eq (pCore_map_iso 2 eq)
  have hB : Nat.card B = 3 := by
    rw [←Nat.card_congr (coreQuotientEquivImage 2 A).toEquiv,
      Nat.card_congr eq'.toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  exact wreath_normal_cubic_impossible s.parabolicPair.overgroupQuotientEquiv
    s.parabolicPair.overgroup_quotient_card B hB


/-- The PSL₃(2) case of 14.7.32, including the literal reduced-local
membership for the now normal component. -/
theorem local_linearThree_normal_and_mem_Hz_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (eK : Chapter13.Section08.Source.starImage I K ≃* Matrix.PSL3Two.PSL) :
    (K.subgroupOf I).Normal ∧
      K ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∈ F.Hz L (normalizer (L : Set G)) := by
  let J := conjugateSpanBy K (T : Subgroup G) ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  have hj := local_component_reduced_mem_Hz_at h structural I hI (K.subgroupOf I) hK
  rw [map_subgroupOf_eq_of_le hKI] at hj
  have hKJ : K ≤ J := (le_conjugateSpanBy _ _).trans le_sup_left
  have hK' := hK.subgroupOf_of_le hKJ hj.2.1
  have hspan : conjugateSpanBy K (T : Subgroup G) = K := by
    by_contra hn
    let e := (componentStarEquiv J K hKJ hK').symm.trans (componentStarEquiv I K hKI hK)
    exact local_reduced_linearThree_impossible_at d h hab structural previous faithful earlier
      J K hj.2.2 hKJ hK' (e.trans eK) rfl hn
  have horbit : (K.subgroupOf I).Normal ∨
      (normalizer (K.subgroupOf I : Set I)).index = 2 :=
    (Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
      (local_star_sqtk h I hI) hK).elim Or.inl (fun hi => Or.inr hi.1)
  refine ⟨normal_of_sylow_span_eq I K T hKI (F.sylow_le_of_mem_Hz hI) horbit hspan, ?_⟩
  simpa only [hspan] using hj.2.2


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment
