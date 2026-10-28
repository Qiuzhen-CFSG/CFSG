module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Offender
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.ReducedSubmoduleClassification
/-!
# Full B5 for the original Case-I module U

The actual same-marker U is reduced, lies in Q1 and is moved by L. Applying
the reduced-submodule C27 theorem yields the full B5 action conclusion on
its literal centralizer quotient. The moved section keeps the original L
image rather than replacing it by an abstract carrier.

Source: Aschbacher--Smith C.2.7 and 15.1.27--28, pp.146,1102--1103.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
/-- The best offender acts on the original U=<Z2^L> under its literal quotient map. -/
theorem U_moved_section (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.U_reduced_on_LQ1 s hG hM hu h hi hf t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    (d.L.subgroupOf J).map q ≤ B ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) (((d.L.subgroupOf J).map q).subgroupOf B)) := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  have hUJ : d.U t ≤ J := (d.U_le_Q1 s hG hM hu h hi hf t ht).trans le_sup_right
  have hm : ⁅W,d.L.subgroupOf J⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hUJ,
      map_subgroupOf_eq_of_le (show d.L ≤ J from le_sup_left),Subgroup.map_bot] at hh
    exact d.Z2_not_centralizes_L s hM hu h t ht htS
      ((le_conjugateSpanBy _ _).trans (commutator_eq_bot_iff_le_centralizer.mp hh))
  exact moved_section_on_reduced_submodule hi W hr
    (comap_mono (d.U_le_Q1 s hG hM hu h hi hf t ht)) hm
end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
