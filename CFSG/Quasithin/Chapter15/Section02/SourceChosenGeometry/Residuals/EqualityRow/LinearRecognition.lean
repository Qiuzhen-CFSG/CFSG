module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearModule
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingReductions
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Recognition

/-!
# Original-U recognition without the partner residual identity

The original reduced module U lies in R = O₂(M ∩ I) and is fully moved by
its selected component. C.2.7 therefore applies on that literal carrier.
The faithful component image is compared to X/O₂(X) by the original core
quotient map, so B.5 classifies the canonical conjugation action itself.
The four binary alternatives retain their original group and module markings.

Source: Aschbacher--Smith C.2.7, B.5.1 and 15.2.23, pp.1116--1117.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRow.Linear
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B0 I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : ResidualInput hsource H B0)
include d

/-- The original M₁ stays in the same partner intersection. -/
theorem M1_le_partner_intersection
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hXI : X ≤ I) :
    M1 X ⁅V,B0⁆ ≤ Mc ⊓ I :=
  le_inf (inf_le_right.trans ((d.plane_centralizer_le_intersection hI).trans inf_le_left))
    (inf_le_left.trans hXI)

private theorem radical_le_S (hI : PlaneEscapes Mc ⁅V,B0⁆ I) :
    (M ⊓ I).pCoreIn 2 ≤ planeSylow T ⁅V,B0⁆ := by
  have hS : planeSylow T ⁅V,B0⁆ ≤ M ⊓ I :=
    le_inf (inf_le_left.trans hsource.maximal.1.2)
      ((le_sup_right.trans (d.residual_sup_planeSylow_le_for_blocks hI)).trans inf_le_right)
  obtain ⟨P,hP⟩ := Chapter1.IsSylowIn.restrict (d.sylow_in_escape_for_blocks hI) hS inf_le_right
  exact (pCoreIn_le_sylow (M ⊓ I) P).trans_eq hP

theorem U_le_intersection_radical (hI : PlaneEscapes Mc ⁅V,B0⁆ I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I) :
    U X ⁅V,B0⁆ ≤ (M ⊓ I).pCoreIn 2 := by
  have hQS : I.pCoreIn 2 ≤ planeSylow T ⁅V,B0⁆ := d.core_le_plane hI
  have hQNI : I.pCoreIn 2 ≤ M ⊓ I :=
    le_inf (hQS.trans (inf_le_left.trans hsource.maximal.1.2)) (pCoreIn_le 2 I)
  have hcore : I.pCoreIn 2 ≤ (M ⊓ I).pCoreIn 2 := by
    simpa only [inf_eq_right.mpr hQNI] using inf_pCoreIn_le_of_le 2
      (inf_le_right : M ⊓ I ≤ I)
  have hUQ : U X ⁅V,B0⁆ ≤ I.pCoreIn 2 := fun u hu =>
    ((mem_omegaOneCenterAmbient_iff _ u).mp (U_le_omegaCore d hI hfit hXI hu)).1
  exact hUQ.trans hcore

private theorem original_U_normalized (hI : PlaneEscapes Mc ⁅V,B0⁆ I)
    (hn : I ≤ normalizer (X : Set G)) :
    X ⊔ (M ⊓ I).pCoreIn 2 ≤ normalizer (U X ⁅V,B0⁆ : Set G) := by
  let R := (M ⊓ I).pCoreIn 2
  have hRX : R ≤ normalizer (X : Set G) :=
    ((pCoreIn_le 2 _).trans inf_le_right).trans hn
  have hRZ : R ≤ centralizer ((⁅V,B0⁆ : Subgroup G) : Set G) := (radical_le_S d hI).trans inf_le_right
  have hRW := normalizes_conjugateSpanBy ⁅V,B0⁆ X R
    (hRZ.trans (Subgroup.centralizer_le_normalizer _)) hRX
  have hJW : X ⊔ R ≤ normalizer (conjugateSpanBy ⁅V,B0⁆ X : Set G) :=
    sup_le (le_normalizer_conjugateSpanBy _ _) hRW
  have hJX : X ⊔ R ≤ normalizer (X : Set G) := sup_le X.le_normalizer hRX
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅conjugateSpanBy ⁅V,B0⁆ X,X⁆).map (MulAut.conj g).toMonoidHom = _
  have hw : (conjugateSpanBy ⁅V,B0⁆ X).map (MulAut.conj g).toMonoidHom =
      conjugateSpanBy ⁅V,B0⁆ X := mem_normalizer_iff_map_conj_eq.mp (hJW hg)
  have hx : X.map (MulAut.conj g).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp (hJX hg)
  rw [map_commutator,hw,hx]
  rfl

private theorem X_moves_original_U (hI : PlaneEscapes Mc ⁅V,B0⁆ I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc) :
    ¬ X ≤ centralizer (U X ⁅V,B0⁆ : Set G) := by
  intro hc
  apply hout
  apply (show X ≤ M1 X ⁅V,B0⁆ from ?_).trans
    ((M1_le_partner_intersection d hI hXI).trans inf_le_left)
  rw [← U_seed_centralizer d hI hfit hXI hn]
  exact le_inf le_rfl (hc.trans (centralizer_le inf_le_left))

/-- The actual original U is a reduced, noncentral C.2.7 module. -/
theorem U_reduced_in_component_radical
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hi : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X) :
    let J := X ⊔ (M ⊓ I).pCoreIn 2
    let W := (U X ⁅V,B0⁆).subgroupOf J
    IsPReduced 2 W ∧ W ≤ ((M ⊓ I).pCoreIn 2).subgroupOf J ∧
      ⁅W,X.subgroupOf J⁆ ≠ ⊥ := by
  let R := (M ⊓ I).pCoreIn 2
  let J := X ⊔ R
  let W := (U X ⁅V,B0⁆).subgroupOf J
  let X0 := X.subgroupOf J
  have hUR : U X ⁅V,B0⁆ ≤ R := U_le_intersection_radical d hI hfit hXI
  have hUJ : U X ⁅V,B0⁆ ≤ J := hUR.trans le_sup_right
  let : W.Normal := normal_subgroupOf_of_le_normalizer (original_U_normalized d hI hn)
  let := U_elementary d hI hfit hXI
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hUJ
  let : X0.Normal := normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hi.normalizes)
  let C := centralizer (W : Set J)
  have hXC : ¬ X0 ≤ C := by
    intro hc
    apply X_moves_original_U d hI hfit hXI hn hout
    intro x hx u hu
    exact congrArg J.subtype (hc (show (⟨x,mem_sup_left hx⟩ : J) ∈ X0 from hx)
      ⟨u,hUJ hu⟩ hu)
  have hm : ⁅W,X0⁆ ≠ ⊥ := by
    rw [commutator_comm,ne_eq,commutator_eq_bot_iff_le_centralizer]
    exact hXC
  have hQR : J.pCoreIn 2 ≤ R := by
    let hiJ := ChapterC.C27Source.source_join_input hi
    exact ChapterC.C27Source.source_joinCore_le_radical hiJ
  have hQZ : ⁅V,B0⁆ ≤ centralizer (J.pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp (hQR.trans ((radical_le_S d hI).trans inf_le_right))
  have hWQ : conjugateSpanBy ⁅V,B0⁆ X ≤ centralizer (J.pCoreIn 2 : Set G) :=
    conjugateSpanBy_le hQZ
      ((le_sup_left.trans J.le_normalizer).trans
        ((normalizer_le_normalizer_characteristic_image J (pCore 2 J)).trans
          (normalizer_le_normalizer_centralizer _)))
  have hQC : pCore 2 J ≤ C := by
    intro x hx u hu
    exact Subtype.ext ((hWQ (U_le_span X ⁅V,B0⁆ hu) x (mem_map_of_mem J.subtype hx)).symm)
  let e : X0 ≃* X := subgroupOfEquivOfLe (show X ≤ J from le_sup_left)
  let := hi.quasisimple
  let : IsQuasisimple (X0 ⧸ pCore 2 X0) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hgen : X0 ⊔ R.subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show X ≤ J from le_sup_left)
      (show R ≤ J from le_sup_right),subgroupOf_self]
  have hred := (QuasisimpleKernel.normal_kernel_structure X0 (R.subgroupOf J) C
    (hi.component.2.subgroupOf_of_le le_sup_left hi.join_le)
    ((isPGroup_pCoreIn 2 (M ⊓ I)).comap_subtype) hgen hQC hXC).2
  exact ⟨⟨inferInstance,inferInstance,hred⟩,fun _ hu => hUR hu,hm⟩

/-- C-component perfectness makes the original commutator fully moved. -/
theorem U_fully_moved
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hX : X ∈ Chapter1.cComponentsIn I) : ⁅U X ⁅V,B0⁆,X⁆ = U X ⁅V,B0⁆ := by
  let e := subgroupOfEquivOfLe hX.1
  let := hX.2.perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hp : IsPPerfect 2 X := by
    intro N hN hpN
    let := hN
    let : Group.IsNilpotent (X ⧸ N) := hpN.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
  let := d.plane_span_elementary hI hfit hX.1
  exact commutator_isPPerfect_idempotent X (conjugateSpanBy ⁅V,B0⁆ X) hp
    (IsElementaryAbelian.isPGroup 2 _) (le_normalizer_conjugateSpanBy _ _)

/-- All six B.5.1 conclusions on the original U, before the binary row sieve.
The only change of carrier is restriction along its literal inclusion in XR. -/
theorem U_source_classification
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hi : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X) :
    let J := X ⊔ (M ⊓ I).pCoreIn 2
    let W := (U X ⁅V,B0⁆).subgroupOf J
    let hr := (U_reduced_in_component_radical d hI hfit hXI hn hout hi).1
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    (X.subgroupOf J).map q ≤ B ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) (((X.subgroupOf J).map q).subgroupOf B)) := by
  dsimp only
  have h := U_reduced_in_component_radical d hI hfit hXI hn hout hi
  let := h.1.normal
  let := h.1.elementary
  exact ChapterC.C27Source.moved_section_on_reduced_submodule hi _ h.1 h.2.1 h.2.2


/-- The B.5 moved space is the whole original U under its literal inclusion. -/
theorem original_movedSection_eq_top
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hi : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X) :
    let J := X ⊔ (M ⊓ I).pCoreIn 2
    let W := (U X ⁅V,B0⁆).subgroupOf J
    let hr := (U_reduced_in_component_radical d hI hfit hXI hn hout hi).1
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ∀ B : Subgroup (J ⧸ centralizer (W : Set J)),
    (X.subgroupOf J).map q ≤ B →
    ∀ s : MovedSection (ρ.comp B.subtype) (((X.subgroupOf J).map q).subgroupOf B),
      s.space.toSubmodule = ⊤ := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B hB s
  have hUR : U X ⁅V,B0⁆ ≤ (M ⊓ I).pCoreIn 2 := U_le_intersection_radical d hI hfit hXI
  have hUJ : U X ⁅V,B0⁆ ≤ J := hUR.trans le_sup_right
  have hm : ⁅W,X.subgroupOf J⁆ = W := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUJ,
      map_subgroupOf_eq_of_le (show X ≤ J from le_sup_left),
      U_fully_moved d hI hfit hi.component]
  rw [s.space_eq,moved,subspaceCommutator_comp_map,
    map_subgroupOf_eq_of_le hB,
    ←NormalElementaryQuotient.commutatorSpace_eq W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _),
    NormalElementaryQuotient.commutatorSpace,hm]
  ext v
  exact iff_of_true v.toMul.property Submodule.mem_top

/-- Identify the canonical original action with its faithful C.2.7 image.
The quotient comparison is checked on each original element of X. -/
def original_component_actionEquiv
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n) :
    letI := U_elementary d hI hfit b.source.component.1
    let J := X ⊔ (M ⊓ I).pCoreIn 2
    let W := (U X ⁅V,B0⁆).subgroupOf J
    let hr := (U_reduced_in_component_radical d hI hfit b.source.component.1 hn hout b.source).1
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ActionEquiv (U_representation d hI hfit b.source.component.1 hn)
      (ρ.comp ((X.subgroupOf J).map q).subtype) := by
  let hXI := b.source.component.1
  let := U_elementary d hI hfit hXI
  let J := X ⊔ (M ⊓ I).pCoreIn 2
  let W := (U X ⁅V,B0⁆).subgroupOf J
  have h := U_reduced_in_component_radical d hI hfit hXI hn hout b.source
  let := h.1.normal
  let := h.1.elementary
  let q := QuotientGroup.mk' (centralizer (W : Set J))
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let : IsSimpleGroup (X ⧸ pCore 2 X) := b.coreQuotient_simple
  let eQ := ChapterC.C27Source.coreQuotientEquiv_reducedSubmodule b.source W h.1 h.2.2
  have hUJ : U X ⁅V,B0⁆ ≤ J :=
    (U_le_intersection_radical d hI hfit hXI).trans le_sup_right
  let eu := (subgroupOfEquivOfLe hUJ).symm
  let a : Additive (U X ⁅V,B0⁆) ≃ₗ[ZMod 2] Additive W := {
    eu.toAdditive with
    map_smul' := fun c v => map_smul (eu.toMonoidHom.toAdditive.toZModLinearMap 2) c v }
  refine ⟨eQ,a,?_⟩
  intro g u
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) g
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  change (((U_representation d hI hfit hXI hn) (QuotientGroup.mk' (pCore 2 X) x) u).toMul : G) = _
  rw [U_representation_apply]
  change _ = ((ρ (eQ (QuotientGroup.mk' (pCore 2 X) x)) (a u)).toMul.val : G)
  rw [ChapterC.C27Source.coreQuotientEquiv_reducedSubmodule_mk]
  have he := NormalElementaryQuotient.representation_apply W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (⟨x,mem_sup_left x.property⟩ : J) (a u)
  exact (congrArg J.subtype he).symm

/-- The exact original-U classification, with no row-recognition premise. -/
theorem moduleRow_of_binaryBranch
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n) :
    letI := U_elementary d hI hfit b.source.component.1
    ModuleRow (U_representation d hI hfit b.source.component.1 hn) := by
  let hXI := b.source.component.1
  let := U_elementary d hI hfit hXI
  let J := X ⊔ (M ⊓ I).pCoreIn 2
  let W := (U X ⁅V,B0⁆).subgroupOf J
  have h := U_reduced_in_component_radical d hI hfit hXI hn hout b.source
  let := h.1.normal
  let := h.1.elementary
  let q := QuotientGroup.mk' (centralizer (W : Set J))
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let B := offenderSubgroup ρ
  let L := ((X.subgroupOf J).map q).subgroupOf B
  obtain ⟨hB,⟨c⟩⟩ := U_source_classification d hI hfit hXI hn hout b.source
  let e0 := original_component_actionEquiv d hI hfit hn hout b
  let e1 := subgroupOfActionEquiv ρ hB
  let eL := e0.groupEquiv.trans e1.groupEquiv
  obtain ⟨ep,_⟩ := b.parabolic
  let mark := b.coreStarEquiv.trans (ep.trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by rcases b.degree with rfl | rfl <;> decide)))
  have hm := BinaryActor.movedCase b.degree
    (BinaryActor.actionCase _ b.degree (eL.symm.trans mark) c.clause_one)
  have hUtop : c.sectionData.space.toSubmodule = ⊤ :=
    original_movedSection_eq_top d hI hfit hXI hn hout b.source B hB c.sectionData
  let e := (e0.trans e1).trans (movedTopActionEquiv c.sectionData hUtop)
  exact moduleRow_of_binary_moved_equiv c.sectionData b.degree hm e




end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRow.Linear
