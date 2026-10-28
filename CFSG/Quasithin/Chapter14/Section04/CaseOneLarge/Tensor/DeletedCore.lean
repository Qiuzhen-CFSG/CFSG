module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedResidualSource
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.Components.Selection
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ReducedDetection
public import CFSG.Quasithin.Chapter13.Section01.LocalModelRigidity
public import Theory.GroupTheory.ReducedNormal.SylowCenter
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.SpecificGroups.PSL3Two.Parabolics.SolvableOvergroups
/-!
# Closing the nontrivial-core alternative of the deleted tensor case

A proper local overcomponent of H∞ moves the original flag point: otherwise
its perfectness would place it inside H∞. The point lies in the actual
reduced subgroup of its Sylow join, so this movement proves faithfulness.
The earlier 14.3.4 classification and the proved 13.1.2(5) model rigidity
therefore make H∞ maximal in the original local family.

The local containment theorem now forces H∞ normal in every overgroup of
T with nontrivial two-core. The deleted-tensor orbit obstruction excludes
any such overgroup containing I₂. In particular both G₀ = ⟨I₂,H∞⟩ and G₀T
have trivial two-core. The core-free amalgam exclusion is a separate step.
The only classification input is the existing earlier-source contract owned
by qt-d-1434-source; no new recognition or geometry callback is introduced.

Source: Aschbacher--Smith 14.4.10(3), printed p.1011; B.2.14, A.4.8,
1.2.4, 13.1.2(5), and 14.3.4(1--2).
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction.Components
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Point movement detects the intrinsic module of every proper local overcomponent. -/
theorem source_tensor_strict_overcomponent_faithful
    (d : Counterexample T L) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) {C : Subgroup G}
    (hC : C ∈ Chapter1.L G (T : Subgroup G)) (hlt : component F.H < C) :
    IsFaithfulSignalizerType C := by
  let := chosen.elementary
  have hmove : ¬ C ≤ centralizer (F.Vi 1 : Set G) := by
    intro hc
    let := Chapter1.mem_L_isPerfect hC
    have hCH : C ≤ F.H := hc.trans (Subgroup.centralizer_le_normalizer _)
    exact (not_le_of_gt hlt) (le_map_solvableResidual_of_isPerfect C F.H hCH)
  let J := C ⊔ (T : Subgroup G)
  let S : Sylow 2 J := T.subtype le_sup_right
  have hchar : centralizer (pCore 2 J : Set J) ≤ pCore 2 J :=
    Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (d.qtke.evenCharacteristic T)
        ⟨hC.2.2, show (T : Subgroup G) ≤ J from le_sup_right⟩)
  have hZT : F.Vi 1 ≤ (T : Subgroup G) := (F.le_seed 1).trans chosen.le_sylow
  have hTZ : (T : Subgroup G) ≤ centralizer (F.Vi 1 : Set G) :=
    (F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  have hZR : (F.Vi 1).subgroupOf J ≤ reducedTwoSubgroup J := by
    intro z hz
    apply sylow_omegaCenter_le_reduced S hchar
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hZT hz, ?_, ?_⟩
    · intro t ht
      exact Subtype.ext ((hTZ ht z hz).symm)
    · exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (z : G) (F.le_seed 1 hz))
  have hnon : ⁅reducedTwoSubgroup J, C.subgroupOf J⁆ ≠ ⊥ := by
    intro he
    apply hmove
    intro c hc z hz
    let zJ : J := ⟨z, (show (T : Subgroup G) ≤ J from le_sup_right) (hZT hz)⟩
    let cJ : J := ⟨c, (show C ≤ J from le_sup_left) hc⟩
    exact (congrArg Subtype.val
      (commutator_eq_bot_iff_le_centralizer.mp he (hZR (show zJ ∈ (F.Vi 1).subgroupOf J from hz))
        cJ hc)).symm
  exact ⟨Chapter1.Section02.Adequate.mem_L_isSignalizerType T
    (d.qtke.evenCharacteristic T) hC,
    Chapter3.RadicalCentralization.intrinsicModule_ne_bot_of_reduced_action
      C J le_sup_left hC.1.subnormal (Chapter1.Section02.Adequate.mem_L_isPPerfect hC) hnon⟩

/-- The marked tensor residual is maximal in the original Sylow local family. -/
theorem source_tensor_component_maximal
    (d : Counterexample T L) (chosen : ChosenModule T L V)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    component F.H ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hK := source_tensor_component_local chosen F c
  refine ⟨hK, ?_⟩
  intro C hC hKC
  by_cases he : component F.H = C
  · exact he.symm
  have hf := source_tensor_strict_overcomponent_faithful d chosen F hC
    (lt_of_le_of_ne hKC he)
  have hmodels := (classification C hC hf).1
  have hsolv : SolvableSylowOvergroups (coreQuotient C) := by
    rcases hmodels with he | he
    · obtain ⟨e⟩ := he
      intro S P _ hp
      exact alternatingGroup.isSolvable_subgroup_of_equiv_five e P hp
    · obtain ⟨e⟩ := he
      exact SolvableSylowOvergroups.of_equiv e Matrix.PSL3Two.solvableSylowOvergroups
  exact (Chapter13.Section01.LocalModelRigidity.local_eq_of_solvableSylowOvergroups
    hC hK hKC hsolv).symm

/-- The maximal tensor component is normal in every local overgroup of T. -/
theorem source_tensor_component_normal_in_local_overgroup
    (d : Counterexample T L) (chosen : ChosenModule T L V)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    {J : Subgroup G} (hKJ : component F.H ≤ J) (hTJ : (T : Subgroup G) ≤ J)
    (hcore : J.pCoreIn 2 ≠ ⊥) : ((component F.H).subgroupOf J).Normal := by
  have hmax := source_tensor_component_maximal d chosen classification F c
  have hlocal : (component F.H).subgroupOf J ∈ Chapter1.L J (T.subgroupOf J) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTJ hKJ).mp ⟨hKJ, hmax.1⟩
  have hnorm : ((T.subtype hTJ : Sylow 2 J) : Subgroup J) ≤
      normalizer ((component F.H).subgroupOf J : Set J) := by
    rw [← subgroupOf_normalizer_eq hKJ]
    exact subgroupOf_mono J ((F.invariant 1).trans
      (F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (solvableResidual F.H))))
  obtain ⟨C, ⟨hC, hKC, hnC⟩, _⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk d.qtke hcore)
      (T.subtype hTJ) hlocal hnorm
  let C' := C.map J.subtype
  have hC'J : C' ≤ J := map_subtype_le _
  have hmap : C'.subgroupOf J = C := comap_map_eq_self_of_injective J.subtype_injective C
  have hc : (C'.subgroupOf J).IsCComponent := hmap.symm ▸ hC
  have hK : component F.H ≤ C' := by
    simpa only [map_subgroupOf_eq_of_le hKJ] using map_mono (f := J.subtype) hKC
  have he : C' = component F.H := hmax.2 C'
    (Chapter1.mem_L_of_cComponent hcore
      ⟨T.subtype hTJ, map_subgroupOf_eq_of_le hTJ⟩ hC'J hc) hK
  have hn : (C'.subgroupOf J).Normal := hmap.symm ▸ hnC
  simpa only [he] using hn

/-- The deleted tensor marking excludes a nontrivial core in every overgroup
of the original T, I₂ and H∞. -/
theorem source_tensor_deleted_overgroup_core_eq_bot (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent)
    {J : Subgroup G} (hKJ : component F.H ≤ J) (hTJ : (T : Subgroup G) ≤ J)
    (hIJ : F.I₂ L ≤ J) : J.pCoreIn 2 = ⊥ := by
  by_contra hcore
  exact (source_tensor_deleted_no_small_component_orbit d earlier hq chosen structural
    alternatives F hne g hgP hgH c hdel hIJ hKJ).1
    (source_tensor_component_normal_in_local_overgroup d chosen classification F c hKJ hTJ hcore)

/-- The literal G₀T is core-free, with the original Sylow subgroup retained. -/
theorem source_tensor_deleted_sylow_join_core_eq_bot (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    (A5.generated F.H (F.I₂ L) ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥ :=
  source_tensor_deleted_overgroup_core_eq_bot d earlier hq chosen structural alternatives
    classification F hne g hgP hgH c hdel (le_sup_right.trans le_sup_left) le_sup_right
    (le_sup_left.trans le_sup_left)

/-- The nontrivial-core alternative for the source's literal G₀ is impossible. -/
theorem source_tensor_deleted_generated_core_eq_bot (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    (A5.generated F.H (F.I₂ L)).pCoreIn 2 = ⊥ := by
  by_contra hcore
  obtain ⟨C, hlt, _, _, _, hC⟩ := source_tensor_deleted_strict_component
    d earlier hq chosen structural alternatives F hne g hgP hgH c hdel hcore
  exact hlt.ne' ((source_tensor_component_maximal d chosen classification F c).2 C hC hlt.le)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
