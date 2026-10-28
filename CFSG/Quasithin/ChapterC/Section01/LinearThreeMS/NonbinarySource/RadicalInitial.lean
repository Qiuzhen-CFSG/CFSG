module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.RadicalGeometry
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SylowInitialQuotient
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NoncoreOffenders
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NaturalBlock

/-!
# The doubled initial branch and complete central-core alternatives

The actual initial source either has natural-module order or has a doubled
natural moved section whose component is the whole offender group. In the
latter branch, MS3 supplies a maximum elementary subgroup of the original
radical that is a genuine best offender. Restricting the supplied Sylow to
the component and applying the common-axis exclusion proves the literal
radical inequality through the faithful initial quotient. No exception at
field four or whole-core recognition hypothesis is needed for this step.

A doubled model on the original initial commutator has order 2^(6n), so
cannot have natural order 2^(3n). Consequently the previously recognized
central-core branch now supplies every clause of C.1.34(1) or (2), including
the actual Sylow radical inequality. Abelianity of O₂(KR) suffices for that
branch; abelianity of Q alone is not asserted to suffice. The remaining
noncentral whole central/Frattini sections are not classified here.

The original Chapter4 nonblock and Chapter11 point applications are in
NonblockMSClassification and PointApplication.
Source: Aschbacher--Smith C.1.34, printed pp.136--137, especially the proof
of case (2); B.5.1 and the larger-field module splitting used there.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.RadicalInitial
open Chapter1.RadicalExclusions.ModelReduction.FullSieve SourceInterface
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion

/-- The full nonbinary source has natural moved-space order, or a doubled
moved module with the entire offender group as its component. -/
theorem source_natural_card_or_double
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) {B : Subgroup X} [IsQuasisimple B]
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ B)
    (hsq : IsSQTK KnownSimple.IsKnownSimple X) (hff : IsFFModule ρ)
    (E : BinaryField) (hn : 1 < E.degree) (mark : B ≃* SL(3,E.Carrier)) :
    Nat.card c.sectionData.space.toSubmodule = 2^(3*E.degree) ∨
      B = ⊤ ∧ ∃ D : BinaryField, D.degree = E.degree ∧
        IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp B.subtype) D 3 2 := by
  cases c.clause_one with
  | irreducible hi hf hirr _ _ =>
    have hff' : IsFFModule c.sectionData.action := by
      obtain ⟨A,hA⟩ := hff
      exact ⟨A,IrreducibleBranch.moved_offender c.sectionData hA⟩
    have hq : quadraticRatio c.sectionData.action ≤ 2 :=
      ((isFFModule_iff_quadraticRatio_le_one _).mp hff').trans (by norm_num)
    let hsource : ChapterK.Linear.Recognition.SourceHypothesis KnownSimple.IsKnownSimple
        c.sectionData.action B :=
      ⟨inferInstance,inferInstance,hsq,c.fitting_eq.symm,inferInstance,hf,hirr,
        (cubicRatio_le_quadraticRatio _).trans hq⟩
    let : IsSimpleGroup PSL(3,E.Carrier) := Atlas.psl_simple_high_rank 3 (by decide)
    let : Nontrivial SL(3,E.Carrier) := (Matrix.PSL3.projection_surjective E.Carrier).nontrivial
    obtain ⟨d⟩ := ChapterK.Linear.Recognition.SourceFF.naturalSourceInput_of_quotient_ff
      hsource (B := E)
      (IsQuasisimple.centralQuotientEquiv mark.toMonoidHom mark.surjective) hff'
    have hsplit := ExtensionConsequences.linearThree_large_isCompl c.sectionData hi E hn d.natural
    have hz : Representation.invariants (c.sectionData.space.toRepresentation.comp B.subtype) = ⊥ := by
      apply bot_unique
      intro v hv
      apply Subtype.ext
      exact (disjoint_iff.mp hsplit.disjoint).le
        ⟨v.property,fun g => congrArg Subtype.val (hv g)⟩
    let b := ExtensionConsequences.actionSymm (ExtensionConsequences.movedQuotientEquiv c.sectionData hz)
    left
    rw [Nat.card_congr (b.linearEquiv.trans d.natural.linearEquiv).toEquiv]
    rw [Nat.card_fun,Nat.card_fin,E.card_eq,←pow_mul]
    congr 1
    omega
  | doubleThree D hw a _ _ =>
    exact Or.inr ⟨hw,D,(linearThree_degree_eq E D (mark.symm.trans a.groupEquiv)).symm,⟨a⟩⟩
  | naturalDual d hd _ ha =>
    obtain ⟨a⟩ := ha
    exact (no_linearThree_binary_equiv E hd (mark.symm.trans a.groupEquiv)).elim
  | repeatedNatural d r hd _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact (no_linearThree_binary_equiv E hd (mark.symm.trans a.groupEquiv)).elim

variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
include h hn
local notation "J" => (K ⊔ R : Subgroup G)

/-- The initial moved group has the natural-module order, or the actual
radical inequality holds for every eligible Sylow, including at field four. -/
theorem initial_order_or_radical_inequalities :
    Nat.card (initialMoved K R) = 2^(3*n) ∨
      ∀ S : Subgroup G, Chapter1.IsSylowIn 2 S J → R ≤ S →
        MSNotCentralizerCore K R S := by
  let ρ := centralOmegaRepresentation K R
  let O := offenderSubgroup ρ
  let : O.Normal := offenderSubgroup_normal ρ
  let B := (centralOmegaComponent K R).subgroupOf O
  let c := Classical.choice (centralOmega_source_conclusion h hn).2
  have hBO := (centralOmega_source_conclusion h hn).1
  let e := Classical.choice h.model
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let E : BinaryField := { Carrier := F, degree := n, degree_pos := by omega, card_eq := h.field_card }
  let mark : B ≃* SL(3,E.Carrier) :=
    (subgroupOfEquivOfLe hBO).trans (centralOmegaFullEquiv h hn e)
  let := centralOmegaComponent_quasisimple h hn
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hBO).symm
  have hff : IsFFModule (ρ.comp O.subtype) := by
    obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp (centralOmega_isFF h hn)
    exact ⟨A.subgroupOf O,(hA.subgroupOf ρ (hA.le_offenderSubgroup ρ)).isOffender _⟩
  rcases source_natural_card_or_double (ρ.comp O.subtype) c
    ((centralOmega_actor_sqtk h hn).subgroup O) hff E hn mark with hc | ⟨hw,D,hd,⟨a⟩⟩
  · left
    let M := (⁅centralOmegaLayer K R,K.subgroupOf J⁆ : Subgroup J)
    let : IsElementaryAbelian 2 M := IsElementaryAbelian.of_le (commutator_le_left _ _)
    have he : M.map (J).subtype = initialMoved K R := by
      rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left)]
      rfl
    have hs : c.sectionData.space.toSubmodule = subspaceCommutator ρ ⊤ (centralOmegaComponent K R) := by
      rw [c.sectionData.space_eq,moved,subspaceCommutator_comp_map,
        map_subgroupOf_eq_of_le hBO]
    let b := (NormalElementaryQuotient.movedEquiv (centralOmegaLayer K R) (centralOmegaProjection K R)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (K.subgroupOf J)).trans
        (LinearEquiv.ofEq _ _ hs.symm)
    have hcard : Nat.card (initialMoved K R) = Nat.card c.sectionData.space.toSubmodule := by
      rw [←he,card_map_of_injective (J).subtype_injective]
      exact (Nat.card_congr (Additive.toMul : Additive M ≃ M)).symm.trans
        (Nat.card_congr b.toEquiv)
    exact hcard.trans hc
  · right
    intro S hS hRS
    obtain ⟨P,hP⟩ := hS
    have hPS : (P : Subgroup J) = S.subgroupOf J := by
      rw [←hP]
      exact (comap_map_eq_self_of_injective (J).subtype_injective _).symm
    let q := centralOmegaProjection K R
    let S' := P.mapSurjective (QuotientGroup.mk'_surjective (centralOmegaKernel K R))
    have hS' : (S' : Subgroup (CentralOmegaActor K R)) = (S.subgroupOf J).map q := by
      change (P : Subgroup J).map q = _
      rw [hPS]
    have hRS' : (R.subgroupOf J).map q ≤ S' := by
      rw [hS']
      exact map_mono (comap_mono hRS)
    obtain ⟨A,hA,_,_,_,hAI⟩ := NoncoreOffenders.coreOmega_bestOffenders h hn (R.subgroupOf J) le_rfl
    let t : O ≃* B := ((MulEquiv.subgroupCongr hw).trans topEquiv).symm
    let aO : ActionEquiv c.sectionData.space.toRepresentation (repeated (linearNatural D 3) 2) :=
      ⟨t.trans a.groupEquiv,a.linearEquiv,fun g v => a.intertwines (t g) v⟩
    have hsplit : c.sectionData.space.toSubmodule ⊔ Representation.invariants (ρ.comp O.subtype) = ⊤ :=
      (ExtensionConsequences.doubleThree_large_isCompl c.sectionData D (hd.symm ▸ hn) hw a).sup_eq_top
    have he := RadicalGeometry.radical_ne_fixerCore_of_double D ρ O c.sectionData.space aO hsplit
      S' ((R.subgroupOf J).map q) hRS' hAI (map_mono hA.1) (hAI.le_offenderSubgroup ρ)
    rw [hS'] at he
    exact (SylowInitial.notCentralizerCore_iff_initial_action h hn ⟨P,hP⟩).mpr he

/-- A doubled section on the literal initial moved group supplies the full
radical inequality; no actor placement or core-comparison premise remains. -/
theorem notCentralizerCore_of_initial_doubled
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (initialMoved K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    MSNotCentralizerCore K R S := by
  rcases initial_order_or_radical_inequalities h hn with hc | hr
  · rw [HasSectionModel,bot_subgroupOf] at hm
    obtain ⟨_,_,_,_,b,_⟩ := hm
    have hd : Nat.card (initialMoved K R) = 2^(6*n) := by
      rw [Nat.card_congr (QuotientGroup.quotientBot.symm.trans b).toEquiv]
      change Nat.card ((Fin 3 → F) × (Fin 3 → F)) = _
      rw [Nat.card_prod,Nat.card_fun,Nat.card_fin,h.field_card,←pow_mul,←pow_add]
      congr 1
      omega
    have he := Nat.pow_right_injective (by decide : 1 < (2:ℕ)) (hc.symm.trans hd)
    omega
  · exact hr S hS hRS

/-- C.1.34 is complete when the whole commutator core centralizes the original
two-core. The doubled row now includes its actual Sylow radical inequality. -/
theorem moduleAlternatives_of_central
    (hz : msQ K R ≤ centralizer ((K ⊔ R).pCoreIn 2 : Set G))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F), MSModuleAlternatives K R S n F e := by
  obtain ⟨e,he⟩ := block_or_doubled_msQ_of_central h hn hz
  refine ⟨e,?_⟩
  rcases he with he | he
  · exact Or.inl he
  · refine Or.inr (Or.inl ⟨he,?_⟩)
    apply notCentralizerCore_of_initial_doubled h hn e _ hS hRS
    simpa only [msQ_eq_initialMoved_of_central h hn hz] using he

/-- In particular, an abelian join two-core supplies complete source
alternatives, retaining the original field and quotient marking. -/
theorem moduleAlternatives_of_abelian_joinCore
    (hc : IsMulCommutative ((K ⊔ R).pCoreIn 2))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F), MSModuleAlternatives K R S n F e :=
  moduleAlternatives_of_central h hn
    (msQ_le_joinCore.trans (le_centralizer_iff_isMulCommutative.mpr hc)) hS hRS
end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.RadicalInitial
