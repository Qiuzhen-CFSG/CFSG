module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Splitting

/-!
# The original moved module retains the full LS action

The proved decomposition U = UL C_U(LS) identifies the literal LS-centralizers
of U and UL. Consequently UL is reduced under the same original LS actor.
This supplies the moved-module clause of B.2.14 used before 15.1.27, retaining
the original subgroup and its quotient map.

Source: Aschbacher--Smith B.2.14 and 15.1.27, printed pp.78,1102--1103.
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

theorem UL_le_U (d : CaseIComponentData T M Mc V) (t : G) : d.UL t ≤ d.U t :=
  le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy (d.Z2 t) d.L)

/-- Moving by L loses no element of the original full LS action. -/
theorem UL_LS_centralizer_eq (d : CaseIComponentData T M Mc V) (s : d.NineSource)
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
  have hUJ : d.U t ≤ J := (d.U_le_Q1 s hG hM hu h hi hf t ht).trans
    ((d.Q1_le_S s hu).trans le_sup_right)
  apply le_antisymm
  · intro x hx
    have hfix : d.U t ≤ centralizer ({(x : G)} : Set G) := by
      rw [d.U_split_LS s hG hM hu h hi hf t ht]
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
theorem UL_reduced (d : CaseIComponentData T M Mc V) (s : d.NineSource)
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
  let hr := d.U_reduced s hG hM hu h hi hf t ht
  let := hr.normal
  let := hr.elementary
  have hn : J ≤ normalizer (d.UL t : Set G) := by
    rw [←d.U_commutator_LS s hG hM hu h hi hf t ht]
    exact normalizer_commutator_ge_right _ _
  let : W.Normal := normal_subgroupOf_of_le_normalizer hn
  refine ⟨inferInstance,IsElementaryAbelian.of_le
    (show W ≤ (d.U t).subgroupOf J from comap_mono (d.UL_le_U t)),?_⟩
  let e := QuotientGroup.quotientMulEquivOfEq (d.UL_LS_centralizer_eq s hG hM hu h hi hf t ht)
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso 2 e]
  exact hr.quotient_pCore_eq_bot

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
