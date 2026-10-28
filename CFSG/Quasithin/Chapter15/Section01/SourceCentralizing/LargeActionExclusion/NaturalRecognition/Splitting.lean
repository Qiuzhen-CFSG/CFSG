module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.MovedModule

/-!
# The full Sylow supplement and the moved module

Sylow averaging splits U as UL C_U(LS) for both exchanged source rows.
It supplies fixed representatives for every seed element, and shows that
the moved module retains the same LS-centralizer quotient. The sum is
not asserted to be direct before the natural action has been established.

Source: Aschbacher--Smith B.2.14 and 15.1.27--28, pp.78,1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem exchanged_U_eq_span_LS (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    conjugateSpanBy (d.Z2 t) (d.L ⊔ d.S) = d.U t := by
  let := s.quasisimple
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((le_centralizer_iff.mp (d.exchanged_Z2_le_centralizer_S s t ht)).trans
      (Subgroup.centralizer_le_normalizer _))
    (d.S_le_G1.trans (d.G1_normalizes_L hG h hf))

theorem exchanged_U_commutator_LS (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    ⁅d.U t,d.L ⊔ d.S⁆ = d.UL t := by
  let := s.quasisimple
  let D := d.L ⊔ d.S
  have hZD : d.Z2 t ≤ D := (le_conjugateSpanBy _ _).trans
    ((d.exchanged_U_le_Q1 s hG hM hu h hi hf t ht).trans ((d.exchanged_Q1_le_S s hu).trans le_sup_right))
  have hh := commutator_conjugateSpan_eq_of_fixed_supplement
    (d.Z2 t) D D d.L d.S hZD le_sup_left le_sup_right D.le_normalizer
    (sup_le d.L.le_normalizer (d.S_le_G1.trans (d.G1_normalizes_L hG h hf)))
    le_sup_left le_rfl (d.exchanged_Z2_le_centralizer_S s t ht)
  rwa [d.exchanged_U_eq_span_LS s hG h hf t ht] at hh

/-- The fixed factor is fixed by the original full Sylow supplement as well as L. -/
theorem exchanged_U_split_LS (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    d.U t = d.UL t ⊔ (d.U t ⊓ centralizer ((d.L ⊔ d.S : Subgroup G) : Set G)) := by
  have he := d.exchanged_U_eq_span_LS s hG h hf t ht
  let := d.exchanged_U_elementary s hG hM hu h hi hf t ht
  let : IsElementaryAbelian 2 (conjugateSpanBy (d.Z2 t) (d.L ⊔ d.S)) := he.symm ▸ inferInstance
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict (show d.S ≤ d.L ⊔ d.S from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  have hs := conjugateSpan_split_of_sylow_fixed P (hP.symm ▸ d.exchanged_Z2_le_centralizer_S s t ht)
  rw [he,d.exchanged_U_commutator_LS s hG hM hu h hi hf t ht] at hs
  exact hs

/-- The source's original splitting with the L-fixed factor. -/
theorem exchanged_U_split (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    d.U t = d.UL t ⊔ (d.U t ⊓ centralizer (d.L : Set G)) := by
  apply le_antisymm
  · exact (d.exchanged_U_split_LS s hG hM hu h hi hf t ht).le.trans
      (sup_le_sup le_rfl (inf_le_inf_left _ (centralizer_le (show d.L ≤ d.L ⊔ d.S from le_sup_left))))
  · exact sup_le (le_normalizer_iff_commutator_le_left.mp
      (le_normalizer_conjugateSpanBy (d.Z2 t) d.L)) inf_le_left

/-- The original seed has an LS-fixed representative modulo UL. -/
theorem exchanged_Z2_fixed_coset (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) {z : G} (hz : z ∈ d.Z2 t) :
    ∃ u ∈ d.UL t, u * z ∈ d.U t ⊓ centralizer ((d.L ⊔ d.S : Subgroup G) : Set G) := by
  have he := d.exchanged_U_eq_span_LS s hG h hf t ht
  let := d.exchanged_U_elementary s hG hM hu h hi hf t ht
  let : IsElementaryAbelian 2 (conjugateSpanBy (d.Z2 t) (d.L ⊔ d.S)) := he.symm ▸ inferInstance
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict (show d.S ≤ d.L ⊔ d.S from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  have hs := conjugateSpan_fixed_coset_of_sylow P
    (hP.symm ▸ d.exchanged_Z2_le_centralizer_S s t ht) hz
  rw [he,d.exchanged_U_commutator_LS s hG hM hu h hi hf t ht] at hs
  exact hs

/-- Moving by L loses no element of the original full LS action. -/
theorem exchanged_UL_LS_centralizer_eq (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    let J := d.L ⊔ d.S
    centralizer ((d.UL t).subgroupOf J : Set J) =
      centralizer ((d.U t).subgroupOf J : Set J) := by
  intro J
  have hUJ : d.U t ≤ J := (d.exchanged_U_le_Q1 s hG hM hu h hi hf t ht).trans
    ((d.exchanged_Q1_le_S s hu).trans le_sup_right)
  apply le_antisymm
  · intro x hx
    have hfix : d.U t ≤ centralizer ({(x : G)} : Set G) := by
      rw [d.exchanged_U_split_LS s hG hM hu h hi hf t ht]
      apply sup_le
      · intro u huU
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hx ⟨u,hUJ (d.UL_le_U t huU)⟩ huU))
      · intro u huU
        exact mem_centralizer_singleton_iff.mpr (huU.2 x x.property).symm
    intro u huU
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hfix huU))
  · exact centralizer_le (show (d.UL t).subgroupOf J ≤ (d.U t).subgroupOf J from
      comap_mono (d.UL_le_U t))

/-- The source moved subgroup is reduced on the same full actor LS. -/
theorem exchanged_UL_reduced (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    IsPReduced 2 ((d.UL t).subgroupOf (d.L ⊔ d.S)) := by
  let J := d.L ⊔ d.S
  let W := (d.UL t).subgroupOf J
  let hr := d.exchanged_U_reduced s hG hM hu h hi hf t ht
  let := hr.normal
  let := hr.elementary
  have hn : J ≤ normalizer (d.UL t : Set G) := by
    rw [←d.exchanged_U_commutator_LS s hG hM hu h hi hf t ht]
    exact normalizer_commutator_ge_right _ _
  let : W.Normal := normal_subgroupOf_of_le_normalizer hn
  refine ⟨inferInstance,IsElementaryAbelian.of_le
    (show W ≤ (d.U t).subgroupOf J from comap_mono (d.UL_le_U t)),?_⟩
  let e := QuotientGroup.quotientMulEquivOfEq (d.exchanged_UL_LS_centralizer_eq s hG hM hu h hi hf t ht)
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso 2 e]
  exact hr.quotient_pCore_eq_bot

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
