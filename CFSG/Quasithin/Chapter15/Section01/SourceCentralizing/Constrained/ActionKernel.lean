module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.RecognizedInput
public import Theory.GroupTheory.ReducedNormal.QuasisimpleKernel

/-!
# The original LS action kernel on U

The original reduced module detects the centerless component quotient. Since
S is a two-group supplement, the full LS-centralizer of U is exactly O2(LS).
This supplies the literal faithful action used in the parabolic comparison
of 15.1.27--28, without an independent kernel premise.
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

/-- The source's actual LS-centralizer quotient removes precisely O2(LS). -/
theorem U_LS_centralizer_eq_pCore (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.S
    centralizer ((d.U t).subgroupOf J : Set J) = pCore 2 J := by
  intro J
  let W := (d.U t).subgroupOf J
  let K := d.L.subgroupOf J
  let hr := d.U_reduced s hG hM hu h hi hf t ht
  let := hr.normal
  let := hi.quasisimple
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le d.L.le_normalizer (d.S_le_G1.trans (d.G1_normalizes_L hG h hf)))
  let eK : K ≃* d.L := subgroupOfEquivOfLe (show d.L ≤ J from le_sup_left)
  have hmap : (pCore 2 K).map eK = pCore 2 d.L := pCore_map_iso 2 eK
  let e0 := QuotientGroup.congr _ _ eK hmap
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e0.symm
  have hz : center (K ⧸ pCore 2 K) = ⊥ := (Facts.of_equiv e0 hf).1
  have hUJ : d.U t ≤ J := (d.U_le_Q1 s hG hM hu h hi hf t ht).trans
    ((d.Q1_le_S s hu).trans le_sup_right)
  have hm : ⁅W,K⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hUJ,
      map_subgroupOf_eq_of_le (show d.L ≤ J from le_sup_left),Subgroup.map_bot] at hh
    exact d.Z2_not_centralizes_L s hM hu h t ht htS
      ((le_conjugateSpanBy _ _).trans (commutator_eq_bot_iff_le_centralizer.mp hh))
  have hp : IsPGroup 2 (d.S.subgroupOf J) := (T.isPGroup'.to_le d.S_le_T).comap_subtype
  have hs : d.S.subgroupOf J ⊔ K = ⊤ := by
    rw [←subgroupOf_sup (show d.S ≤ J from le_sup_right)
      (show d.L ≤ J from le_sup_left),sup_comm d.S d.L,subgroupOf_self]
  exact reduced_quasisimple_centralizer_eq_pCore W K hr hz hm
    (quotient_isPGroup_of_sup_eq_top _ K hp hs)

/-- The kernel conclusion from the recognized original component has no
separate constrained-input or cubic-Facts assumption. -/
theorem NineSource.small_binary_action_kernel {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (he : SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.S
    centralizer ((d.U t).subgroupOf J : Set J) = pCore 2 J :=
  d.U_LS_centralizer_eq_pCore s hG hM hu h
    (s.c27Input_of_small_binary_model hG hM hu h he)
    (facts_of_small_binary_model he) t ht htS

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
