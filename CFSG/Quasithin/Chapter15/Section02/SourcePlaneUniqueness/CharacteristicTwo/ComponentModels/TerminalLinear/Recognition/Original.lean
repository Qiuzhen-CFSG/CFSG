module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.SeedCentralizer
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.ReducedSubmoduleClassification
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# Applying C.2.7 to the original commutator module

The original U lies in the radical of M ∩ I, is normalized by XR, and is
not centralized by X. The two-core of XR centralizes the seed ZS and hence
its X-orbit span. The quasisimple normal-kernel theorem makes the faithful
XR-action on U reduced. C.2.7 therefore supplies a best offender and all
B.5.1 conclusions on this actual carrier. Perfectness of X also proves
[U,X] = U, so no unrelated star-module summand is substituted for U.

Source: Aschbacher--Smith C.2.7(2), B.5.1 and 15.2.23, pp.146,94,1116--1117.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

private theorem radical_le_S (hI : PlaneEscapes Mc ZS I) :
    (M ⊓ I).pCoreIn 2 ≤ planeSylow T ZS := by
  have hS : planeSylow T ZS ≤ M ⊓ I :=
    le_inf (inf_le_left.trans hsource.maximal.1.2)
      ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right)
  obtain ⟨P,hP⟩ := Chapter1.IsSylowIn.restrict (d.sylow_in_escape hI) hS inf_le_right
  exact (pCoreIn_le_sylow (M ⊓ I) P).trans_eq hP

theorem U_le_intersection_radical (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I) :
    U X ZS ≤ (M ⊓ I).pCoreIn 2 := by
  have hQS : I.pCoreIn 2 ≤ planeSylow T ZS := d.core_le_plane hI
  have hQNI : I.pCoreIn 2 ≤ M ⊓ I :=
    le_inf (hQS.trans (inf_le_left.trans hsource.maximal.1.2)) (pCoreIn_le 2 I)
  have hcore : I.pCoreIn 2 ≤ (M ⊓ I).pCoreIn 2 := by
    simpa only [inf_eq_right.mpr hQNI] using inf_pCoreIn_le_of_le 2
      (inf_le_right : M ⊓ I ≤ I)
  have hUQ : U X ZS ≤ I.pCoreIn 2 := fun u hu =>
    ((mem_omegaOneCenterAmbient_iff _ u).mp (U_le_omegaCore d hI hfit hXI hu)).1
  exact hUQ.trans hcore

private theorem original_U_normalized (hI : PlaneEscapes Mc ZS I)
    (hn : I ≤ normalizer (X : Set G)) :
    X ⊔ (M ⊓ I).pCoreIn 2 ≤ normalizer (U X ZS : Set G) := by
  let R := (M ⊓ I).pCoreIn 2
  have hRX : R ≤ normalizer (X : Set G) :=
    ((pCoreIn_le 2 _).trans inf_le_right).trans hn
  have hRZ : R ≤ centralizer (ZS : Set G) := (radical_le_S d hI).trans inf_le_right
  have hRW := normalizes_conjugateSpanBy ZS X R
    (hRZ.trans (Subgroup.centralizer_le_normalizer _)) hRX
  have hJW : X ⊔ R ≤ normalizer (conjugateSpanBy ZS X : Set G) :=
    sup_le (le_normalizer_conjugateSpanBy _ _) hRW
  have hJX : X ⊔ R ≤ normalizer (X : Set G) := sup_le X.le_normalizer hRX
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅conjugateSpanBy ZS X,X⁆).map (MulAut.conj g).toMonoidHom = _
  have hw : (conjugateSpanBy ZS X).map (MulAut.conj g).toMonoidHom =
      conjugateSpanBy ZS X := mem_normalizer_iff_map_conj_eq.mp (hJW hg)
  have hx : X.map (MulAut.conj g).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp (hJX hg)
  rw [map_commutator,hw,hx]
  rfl

private theorem X_moves_original_U (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc) :
    ¬ X ≤ centralizer (U X ZS : Set G) := by
  intro hc
  apply hout
  apply (show X ≤ M1 X ZS from ?_).trans
    ((M1_le_partner_intersection d hI hXI).trans inf_le_left)
  rw [← U_seed_centralizer d hI hfit hXI hn]
  exact le_inf le_rfl (hc.trans (centralizer_le inf_le_left))

/-- The actual original U is a reduced, noncentral C.2.7 module. -/
theorem U_reduced_in_component_radical
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hi : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X) :
    let J := X ⊔ (M ⊓ I).pCoreIn 2
    let W := (U X ZS).subgroupOf J
    IsPReduced 2 W ∧ W ≤ ((M ⊓ I).pCoreIn 2).subgroupOf J ∧
      ⁅W,X.subgroupOf J⁆ ≠ ⊥ := by
  let R := (M ⊓ I).pCoreIn 2
  let J := X ⊔ R
  let W := (U X ZS).subgroupOf J
  let X0 := X.subgroupOf J
  have hUR : U X ZS ≤ R := U_le_intersection_radical d hI hfit hXI
  have hUJ : U X ZS ≤ J := hUR.trans le_sup_right
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
  have hQZ : ZS ≤ centralizer (J.pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp (hQR.trans ((radical_le_S d hI).trans inf_le_right))
  have hWQ : conjugateSpanBy ZS X ≤ centralizer (J.pCoreIn 2 : Set G) :=
    conjugateSpanBy_le hQZ
      ((le_sup_left.trans J.le_normalizer).trans
        ((normalizer_le_normalizer_characteristic_image J (pCore 2 J)).trans
          (normalizer_le_normalizer_centralizer _)))
  have hQC : pCore 2 J ≤ C := by
    intro x hx u hu
    exact Subtype.ext ((hWQ (U_le_span X ZS hu) x (mem_map_of_mem J.subtype hx)).symm)
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
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hX : X ∈ Chapter1.cComponentsIn I) : ⁅U X ZS,X⁆ = U X ZS := by
  let e := subgroupOfEquivOfLe hX.1
  let := hX.2.perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hp : IsPPerfect 2 X := by
    intro N hN hpN
    let := hN
    let : Group.IsNilpotent (X ⧸ N) := hpN.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
  let := d.plane_span_elementary hI hfit hX.1
  exact commutator_isPPerfect_idempotent X (conjugateSpanBy ZS X) hp
    (IsElementaryAbelian.isPGroup 2 _) (le_normalizer_conjugateSpanBy _ _)

/-- Apply the actual C.2.7 offender theorem to the original U. -/
theorem U_radical_bestOffender
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hi : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X) :
    let J := X ⊔ (M ⊓ I).pCoreIn 2
    let W := (U X ZS).subgroupOf J
    let hr := (U_reduced_in_component_radical d hI hfit hXI hn hout hi).1
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    ∃ A ∈ elementaryAbelianMaxSubgroups (((M ⊓ I).pCoreIn 2).subgroupOf J),
      IsBestOffender (NormalElementaryQuotient.representation W q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) (A.map q) := by
  dsimp only
  have h := U_reduced_in_component_radical d hI hfit hXI hn hout hi
  let := h.1.normal
  let := h.1.elementary
  exact ChapterC.C27Source.best_offender_on_reduced_submodule hi _ h.1 h.2.1 h.2.2

/-- All six B.5.1 conclusions on the original U, before the binary row sieve.
The only change of carrier is restriction along its literal inclusion in XR. -/
theorem U_source_classification
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hi : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X) :
    let J := X ⊔ (M ⊓ I).pCoreIn 2
    let W := (U X ZS).subgroupOf J
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

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
