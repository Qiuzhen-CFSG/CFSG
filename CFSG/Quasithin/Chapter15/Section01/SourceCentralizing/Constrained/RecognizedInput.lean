module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.MarkedImage
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.ModelExclusions

/-!
# Constrained input on the same recognized source component

For the chosen Nine marker, fixed-plane noncentrality contradicts the
ordinary component centralizer calculation in every recognized small binary
row. Thus that very component is constrained. Its original source controls
supply C.2.7, and its concrete model supplies the cubic Facts. The resulting
marked B5 action on U retains no independent fitting or C.2.7 assumption.

Source: Aschbacher--Smith 15.1.25--28, printed pp.1102--1103.
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

/-- The same Nine marker rules out the ordinary branch of the recognized binary rows. -/
theorem NineSource.constrained_of_small_binary_model {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (he : SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L)) :
    generalizedFitting d.L = pCore 2 d.L := by
  rcases d.ordinary_or_constrained s.odd_core with hc | hfitting
  · exfalso
    let := s.quasisimple
    let := h.elementary
    have hf := facts_of_small_binary_model he
    have hcentral := d.ordinary_small_binary_model_centralizer hG hM.1.2 hu h hc
      s.odd_core s.component_sylow he s.cubic_escape
    have hY := (d.source_cubic_component hG h hf).2
    have hYR : d.nineCubic ≤ d.nineResidual := map_mono (le_pResidual_of_isPPerfect _
      (isPPerfect_primeToResidual 3 2 (by decide)))
    have hVT : V ≤ (T : Subgroup G) := by
      let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
      let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
      have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
        (T.subtype hM.1.2)
      simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
        map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
    have hplane : d.nineFixedPlane ≤ d.S ⊓ centralizer (d.nineCubic : Set G) :=
      le_inf (le_inf (inf_le_left.trans hVT)
        (inf_le_left.trans (V.le_centralizer.trans
          (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))))
        (inf_le_right.trans (centralizer_le hYR))
    have hcentral' : d.S ⊓ centralizer (d.nineCubic : Set G) =
        d.S ⊓ centralizer (d.L : Set G) := by
      dsimp only [nineCubic]
      rw [hY]
      exact hcentral
    exact s.fixed_noncentral hf ((hplane.trans hcentral'.le).trans inf_le_right)
  · exact hfitting

/-- Recognition discharges both the fitting equality and the C.2.7 input. -/
theorem NineSource.c27Input_of_small_binary_model {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (he : SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L)) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L :=
  s.c27Input hG h (facts_of_small_binary_model he)
    (s.constrained_of_small_binary_model hG hM hu h he)

/-- The recognized source model supplies all inputs to the marked B5 action
on the literal original U. -/
theorem NineSource.small_binary_moved_section {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (he : SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let hi := s.c27Input_of_small_binary_model hG hM hu h he
    let hf := facts_of_small_binary_model he
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
        (ρ.comp B.subtype) (((d.L.subgroupOf J).map q).subgroupOf B)) ∧
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* (((d.L.subgroupOf J).map q).subgroupOf B)) :=
  d.U_marked_moved_section s hG hM hu h
    (s.c27Input_of_small_binary_model hG hM hu h he)
    (facts_of_small_binary_model he) t ht htS

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
