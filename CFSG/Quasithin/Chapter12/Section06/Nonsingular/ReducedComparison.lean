module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ReducedAction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ComponentCentralizer
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The component centralizer on the original reduced point module

The image of L_v on R₂(G_v) has kernel exactly O₂(L_v), through the
literal quotient by C_{G_v}(R₂(G_v)). An element centralizing this image
therefore acts trivially on L_v/O₂(L_v). Its full preimage is contained
in the original quotient-action centralizer, whose order is prime to three.
Thus the component centralizer in the reduced action has no three-part.
The adequate B.5.6 alternatives therefore select the quasisimple row, and
the actual order 360 excludes every reducible B.5.1 row. This proves that
[R₂(G_v),L_v] is Irr⁺ at the original preferred escaping point. Identifying
it with the original V_v remains a separate comparison.

Source: Aschbacher--Smith, Lemma12.6.11, printed p.825.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The reduced-action marking retains the literal kernel in L_v. -/
theorem SourceHypothesis.reduced_point_actor_kernel
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G)) :
    let A := Gv (v : G)
    let B := (Lv L (v : G)).subgroupOf A
    ((ChapterB.InternalThompsonAction.actionMk (reducedTwoSubgroup A)).subgroupMap B).ker =
      pCore 2 B := by
  let A := Gv (v : G)
  let U := reducedTwoSubgroup A
  let B := (Lv L (v : G)).subgroupOf A
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  let eB := subgroupOfEquivOfLe (Lv_le_Gv L (v : G))
  have hB : B.map A.subtype = Lv L (v : G) := map_subgroupOf_eq_of_le (Lv_le_Gv L (v : G))
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let eQ : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans e
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eQ.symm
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply bot_unique
    intro x hx
    have hc : eQ x ∈ center (alternatingGroup (Fin 6)) := by
      rw [mem_center_iff] at hx ⊢
      intro y
      obtain ⟨z,rfl⟩ := eQ.surjective y
      simpa only [map_mul] using congrArg eQ (hx z)
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hc
    exact mem_bot.mpr (eQ.injective (hc.trans eQ.map_one.symm))
  have hm : ⁅U,B⁆ ≠ ⊥ := by
    intro hz
    apply H.reduced_point_moved D v hv hn
    have hh := congrArg (map A.subtype) hz
    rwa [map_commutator,hB,Subgroup.map_bot] at hh
  exact reduced_quasisimple_subgroupMap_ker U B isPReduced_reducedPSubgroup hz hm

/-- The centralizer of the actual A₆ image has order prime to three. -/
theorem SourceHypothesis.reduced_point_actor_centralizer_three_free
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G)) :
    let A := Gv (v : G)
    let U := reducedTwoSubgroup A
    let B := ((Lv L (v : G)).subgroupOf A).map
      (ChapterB.InternalThompsonAction.actionMk U)
    Nat.Coprime 3 (Nat.card (centralizer (B : Set (ChapterB.InternalThompsonAction.ActionQuotient U)))) := by
  let A := Gv (v : G)
  let U := reducedTwoSubgroup A
  let X := (Lv L (v : G)).subgroupOf A
  let q := ChapterB.InternalThompsonAction.actionMk U
  let B := X.map q
  let C := centralizer (B : Set (ChapterB.InternalThompsonAction.ActionQuotient U))
  let P := C.comap q
  have hX : X.map A.subtype = Lv L (v : G) := map_subgroupOf_eq_of_le (Lv_le_Gv L (v : G))
  have hker := H.reduced_point_actor_kernel D v hv hn
  have hP : P.map A.subtype ≤ A ⊓ coreQuotientCentralizer (Lv L (v : G)) := by
    rintro _ ⟨g,hg,rfl⟩
    refine ⟨g.property,(mem_coreQuotientCentralizer_iff _ _).mpr ⟨hn g.property,?_⟩⟩
    intro l hl
    let l' : X := ⟨⟨l,Lv_le_Gv L (v : G) hl⟩,hl⟩
    have hcomm : ⁅g,(l' : A)⁆ ∈ X := by
      change ((⁅g,(l' : A)⁆ : A) : G) ∈ Lv L (v : G)
      exact (le_normalizer_iff_commutator_le_right.mp hn)
        (commutator_mem_commutator g.property hl)
    have hzero : q ⁅g,(l' : A)⁆ = 1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.mp hg (q l') (mem_map_of_mem q l'.property)).symm
    have hk : (⟨⁅g,(l' : A)⁆,hcomm⟩ : X) ∈ pCore 2 X := by
      rw [←hker]
      exact Subtype.ext hzero
    have hc : ⁅g,(l' : A)⁆ ∈ X.pCoreIn 2 := mem_map_of_mem X.subtype hk
    have hh := mem_map_of_mem A.subtype hc
    rw [map_pCoreIn_of_injective 2 X A.subtype A.subtype_injective,hX] at hh
    exact hh
  have hcardP : Nat.Coprime 3 (Nat.card P) := by
    have hh := (H.nonsingular_quotient_centralizer_three_free D v hv).coprime_dvd_right
      (card_dvd_of_le hP)
    rwa [card_map_of_injective A.subtype_injective] at hh
  exact hcardP.coprime_dvd_right (card_dvd_of_surjective (q.subgroupComap C)
    (q.subgroupComap_surjective_of_surjective C (QuotientGroup.mk'_surjective _)))
end CFSG.Quasithin.Chapter12.Section06

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal reduced L_v-moved space is Irr⁺. The classifier's product
and outer rows are excluded using the original three-free centralizer. -/
theorem SourceHypothesis.reduced_point_moved_irrPlus
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G)) :
    let A := Gv (v : G)
    let U := reducedTwoSubgroup A
    let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
    let ρ := ChapterB.InternalThompsonAction.action U
    let B := ((Lv L (v : G)).subgroupOf A).map
      (ChapterB.InternalThompsonAction.actionMk U)
    B ≤ offenderSubgroup ρ →
    ChapterB.SourceInduction.AdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype) →
    IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B) := by
  let A := Gv (v : G)
  let U := reducedTwoSubgroup A
  let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
  let ρ := ChapterB.InternalThompsonAction.action U
  let q := ChapterB.InternalThompsonAction.actionMk U
  let X := (Lv L (v : G)).subgroupOf A
  let B := X.map q
  let J := offenderSubgroup ρ
  change B ≤ J → ChapterB.SourceInduction.AdequateAlternative (ρ.comp J.subtype) →
    IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B)
  intro hBJ hclass
  let C := B.subgroupOf J
  let : X.Normal := normal_subgroupOf_of_le_normalizer hn
  let : B.Normal := (inferInstance : X.Normal).map q (QuotientGroup.mk'_surjective _)
  let : C.Normal := inferInstance
  obtain ⟨e⟩ := H.reduced_point_actor D v hv hn
  let eC : C ≃* alternatingGroup (Fin 6) := (subgroupOfEquivOfLe hBJ).trans e
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv eC.symm
  have hC : IsComponent J C := ⟨(inferInstance : C.Normal).isSubnormal,inferInstance⟩
  have hc : Nat.Coprime 3 (Nat.card (centralizer (C : Set J))) := by
    have hle : (centralizer (C : Set J)).map J.subtype ≤
        centralizer (B : Set (ChapterB.InternalThompsonAction.ActionQuotient U)) := by
      rintro _ ⟨g,hg,rfl⟩ b hb
      exact congrArg J.subtype (mem_centralizer_iff.mp hg ⟨b,hBJ hb⟩ hb)
    have hh := (H.reduced_point_actor_centralizer_three_free D v hv hn).coprime_dvd_right
      (card_dvd_of_le hle)
    rwa [card_map_of_injective J.subtype_injective] at hh
  obtain ⟨_,⟨c⟩⟩ := hclass.quasisimple_of_component_three_free_centralizer hC hc
  have hcard : Nat.card C = 360 := by
    rw [Nat.card_congr eC.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hi := c.card360_moved_irrPlus hcard
  rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBJ] at hi
  exact (IsIrrPlus.subgroupOf_iff ρ B J hBJ _).mp hi

/-- Apply the row comparison to the already constructed preferred-point FF
action. The target remains its literal commutator space, not a new constituent. -/
theorem SourceHypothesis.exists_preferred_reduced_point_irrPlus
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      (Lv L (w : G) = Kv (w : G) →
        let A := Gv (w : G)
        let U := reducedTwoSubgroup A
        let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
        let ρ := ChapterB.InternalThompsonAction.action U
        let B := ((Lv L (w : G)).subgroupOf A).map
          (ChapterB.InternalThompsonAction.actionMk U)
        U.map A.subtype ≤ Rv T L (w : G) ∧
        ¬ ((Vv L V (w : G)).subgroupOf A).Normal ∧
        IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B)) := by
  obtain ⟨w,hw,he,hs,hi,hc⟩ :=
    H.exists_preferred_reduced_point_classification D hTV hTI v hv he
  refine ⟨w,hw,he,hs,hi,fun heq => ?_⟩
  have hn : Gv (w : G) ≤ normalizer (Lv L (w : G) : Set G) := by
    rw [heq]
    exact (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _)
  obtain ⟨hU,hW,_,hB,_,hclass⟩ := hc heq
  exact ⟨hU,hW,H.reduced_point_moved_irrPlus D w hw hn hB hclass⟩
end CFSG.Quasithin.Chapter12.Section06
