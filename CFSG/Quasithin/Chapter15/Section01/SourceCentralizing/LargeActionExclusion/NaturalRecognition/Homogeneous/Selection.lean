module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.SeedSylow

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.MovedSpace
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.Orthogonal.SixSpace
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.Orthogonal.SevenCover
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.Exterior
/-!
# Selecting the original natural moved module

The B.5 alternatives on the literal component are exhausted using the
original seed-core offender: the orthogonal six-space and its seven-cover,
both exterior powers, and the natural-plus-dual row are impossible. The
repeated-natural row has multiplicity one. Cohomological splitting transports
the remaining natural central quotient to the actual moved space.

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterB.QuasisimpleSource
open Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource.SourceCompletion
open ChapterB.QuasisimpleSource.ExtensionConsequences
private noncomputable def splitMovedEquiv
    {D A : Type*} [Group D] [AddCommGroup A] [Module (ZMod 2) A]
    {ρ : Representation (ZMod 2) D A} {L : Subgroup D}
    (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L)) :
    ActionEquiv (s.action.comp L.subtype) (s.space.toRepresentation.comp L.subtype) := by
  have hz : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact (disjoint_iff.mp hc.disjoint).le ⟨v.property,fun g => congrArg Subtype.val (hv g)⟩
  exact ⟨MulEquiv.refl _,s.central.toSubmodule.quotEquivOfEqBot hz, fun g v => by
    induction v using Submodule.Quotient.induction_on with | _ v => rfl⟩

variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Literal recognized-component application, retaining both plane sizes. -/
theorem HasExchangedLinearSource.original_natural_of_actionCase
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (_hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (_hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hne : M ≠ Mc) (_hfull : V = localModule T M)
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      ∀ n : ℕ, (n = 4 ∨ n = 5) →
      BinaryActor.ActionCase (ρ.comp B.subtype) K c.sectionData n →
      Nonempty (ActionEquiv (c.sectionData.space.toRepresentation.comp K.subtype)
        (linearNatural BinaryField.two n)) := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c n hn hc
  have hcase := hc
  cases hc with
  | naturalDual hK hnat =>
    exact (d.exchanged_U_not_naturalPlusDual s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht htS c n hn hK hnat).elim
  | repeatedNatural r hp hb hK hnat =>
    exact (s.repeated_natural_multiplicity_one hG hM hu h t ht htS
      c n r hn hK hp hb hnat).2
  | irreducible hi hf hir hs he =>
    cases hs with
    | natural hg e hr =>
      have hsplit := binaryLinear_isCompl c.sectionData hi
        (by rcases hn with rfl | rfl <;> decide) e
      let q := splitMovedEquiv c.sectionData hsplit
      exact ⟨(actionSymm q).trans e⟩
    | orthogonal hd hg hK e ho hr =>
      rcases BinaryActor.orthogonal_moved_model c.sectionData hi e with hm | hm
      · exact (s.original_not_orthogonal_six hG _hempty hM _hmany _hJ hu
          _hne _hfull h t ht htS c hm).elim
      · exact (s.original_not_seven_cover hG _hempty hM _hmany _hJ hu
          _hne _hfull h t ht htS c hm).elim
    | symmetricEight hd hw e hr =>
      rcases BinaryActor.orthogonal_moved_model c.sectionData hi (markedRestriction e) with hm | hm
      · exact (s.original_not_orthogonal_six hG _hempty hM _hmany _hJ hu
          _hne _hfull h t ht htS c hm).elim
      · exact (s.original_not_seven_cover hG _hempty hM _hmany _hJ hu
          _hne _hfull h t ht htS c hm).elim
    | exterior hd hg hK em hdq ho hr =>
      subst n
      have hsplit := exteriorFive_isCompl c.sectionData
        ⟨hi,hf,hir,.exteriorFive hg hK em hdq ho hr,he⟩ em hdq
      let q := splitMovedEquiv c.sectionData hsplit
      let a := actionSymm q
      exact (s.original_exterior_false hG _hempty hM _hmany _hJ hu _hne _hfull h
        t ht htS c hcase (irreducible_of_equiv a hir)
        (q.linearEquiv.finrank_eq.symm.trans hdq) em).elim

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
