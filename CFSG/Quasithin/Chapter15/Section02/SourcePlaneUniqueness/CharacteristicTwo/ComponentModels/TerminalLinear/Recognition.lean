module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Recognition.Original
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Recognition.Core
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Recognition.Rows
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.ReducedSubmoduleMarking
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Exterior.Action
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# B.5.1 recognition on the original terminal module

The C.2.7 reduced-submodule classifier applies to the original
U = [⟨ZS^X⟩,X]. Its moved space is the entire U because [U,X] = U.
The component image is identified with X/O₂(X) by the actual quotient map;
on every element, the resulting representation is the canonical conjugation
action already used by the terminal exclusions. The binary B.5 classifier
therefore constructs ModuleRow on this representation without a recognition
premise. Applying the completed exclusions leaves degree-five repeated-natural
with its literal M₁ point-parabolic and K_I/O₂(K_I) ≅ SL₄(2) markings.

The degree-five minimal-parabolic exclusion remains with this terminal owner.
The earlier component-residual identity, K containment, S₃-square quotient and
T-irreducibility are retained with qt-e-152-char2-component-models and
qt-e-152-small-parabolic, for final discharge by qt-e-152-plane-uniqueness.
No legacy SmallActionCaseII field is used.

Source: Aschbacher--Smith C.2.7(2),(3)(h), B.5.1, and 15.2.23, pp.1116--1117.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

/-- The B.5 moved space is the whole original U under its literal inclusion. -/
theorem original_movedSection_eq_top
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
    ∀ B : Subgroup (J ⧸ centralizer (W : Set J)),
    (X.subgroupOf J).map q ≤ B →
    ∀ s : MovedSection (ρ.comp B.subtype) (((X.subgroupOf J).map q).subgroupOf B),
      s.space.toSubmodule = ⊤ := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B hB s
  have hUR : U X ZS ≤ (M ⊓ I).pCoreIn 2 := U_le_intersection_radical d hI hfit hXI
  have hUJ : U X ZS ≤ J := hUR.trans le_sup_right
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
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n) :
    letI := U_elementary d hI hfit b.source.component.1
    let J := X ⊔ (M ⊓ I).pCoreIn 2
    let W := (U X ZS).subgroupOf J
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
  let W := (U X ZS).subgroupOf J
  have h := U_reduced_in_component_radical d hI hfit hXI hn hout b.source
  let := h.1.normal
  let := h.1.elementary
  let q := QuotientGroup.mk' (centralizer (W : Set J))
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let : IsSimpleGroup (X ⧸ pCore 2 X) := b.coreQuotient_simple
  let eQ := ChapterC.C27Source.coreQuotientEquiv_reducedSubmodule b.source W h.1 h.2.2
  have hUJ : U X ZS ≤ J :=
    (U_le_intersection_radical d hI hfit hXI).trans le_sup_right
  let eu := (subgroupOfEquivOfLe hUJ).symm
  let a : Additive (U X ZS) ≃ₗ[ZMod 2] Additive W := {
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
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n) :
    letI := U_elementary d hI hfit b.source.component.1
    ModuleRow (U_representation d hI hfit b.source.component.1 hn) := by
  let hXI := b.source.component.1
  let := U_elementary d hI hfit hXI
  let J := X ⊔ (M ⊓ I).pCoreIn 2
  let W := (U X ZS).subgroupOf J
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


/-- The literal terminal consumer now constructs its original-U row input.
Only the degree-five repeated-natural branch remains, with both original markings. -/
theorem remaining_repeatedNatural_of_binaryBranch
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hirr : IsSmallActionIrreducible (T : Subgroup G) (smallActionK H)) :
    letI := U_elementary d hI hfit b.source.component.1
    let σ := U_representation d hI hfit b.source.component.1 hn
    Nonempty ((KI X ZS ⧸ pCore 2 (KI X ZS)) ≃* SL(4,ZMod 2)) ∧
      ∃ r : ℕ, 0 < r ∧ r ≤ 4 ∧
        ∃ e : ActionEquiv σ (repeated (linearNatural BinaryField.two 5) r),
        ∃ v : Fin 5 → ZMod 2, v ≠ 0 ∧
          (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
            e.groupEquiv.toMonoidHom = MulAction.stabilizer SL(5,ZMod 2) v := by
  let := U_elementary d hI hfit b.source.component.1
  exact remaining_repeatedNatural_of_source d hI hfit b.source.component.1 hn hout
    hX hKX hpair hirr (moduleRow_of_binaryBranch d hI hfit hn hout b)

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
