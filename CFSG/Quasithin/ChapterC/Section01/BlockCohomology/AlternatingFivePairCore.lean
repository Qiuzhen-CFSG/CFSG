module
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation
public import Theory.ElementaryAbelian.Join

/-!
# The two-core split for commuting alternating-five blocks

Apply the alternating-five C.1.13(c) splitting first to the ambient two-core
and then to its centralizer of the first block. Commutation puts the second
block's elementary layer inside that centralizer. The result expresses the
two-core as the two original block layers and the common fixed factor.
When that factor is trivial, the two-core is elementary abelian.

This is the core calculation at the start of the zero-centralizer branch of
10.2.1. Source: Aschbacher–Smith C.1.13(c), pp.124–125, and10.2.1,p.742.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The ambient two-core splits over the two literal block layers. -/
theorem alternatingFive_pair_core_split
    (A B : Subgroup G) (hA : IsBlock A) (hB : IsBlock B)
    (ha : IsAlternatingBlock A 5) (hb : IsAlternatingBlock B 5)
    (hc : ⁅A,B⁆ = ⊥) :
    pCore 2 G = (blockU A).map A.subtype ⊔ (blockU B).map B.subtype ⊔
      (pCore 2 G ⊓ centralizer ((A ⊔ B : Subgroup G) : Set G)) := by
  let Q := pCore 2 G
  let P := Q ⊓ centralizer (A : Set G)
  have hAQ : A ≤ normalizer (Q : Set G) := le_normalizer_of_normal
  have hBQ : B ≤ normalizer (Q : Set G) := le_normalizer_of_normal
  have huA : (blockU A).map A.subtype ≤ Q :=
    (map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hA.subnormal)
  have huB : (blockU B).map B.subtype ≤ Q :=
    (map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hB.subnormal)
  have hcommA : ⁅A,Q⁆ ≤ A.pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal A Q hA.subnormal
      hA.short.twoPerfect pCore_isPGroup hAQ).trans (map_mono blockU_le_core)
  have hsplitA : Q = (blockU A).map A.subtype ⊔ P :=
    ha.two_subgroup_eq_module_sup_centralizer pCore_isPGroup hAQ huA hcommA
  have hBA : B ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hBP : B ≤ normalizer (P : Set G) :=
    (le_inf hBQ ((hBA.trans (centralizer_le_normalizer _)).trans
      (normalizer_le_normalizer_centralizer A))).trans inf_normalizer_le_normalizer_inf
  have huBP : (blockU B).map B.subtype ≤ P :=
    le_inf huB ((map_subtype_le _).trans hBA)
  have hpP : IsPGroup 2 P := pCore_isPGroup.to_le inf_le_left
  have hcommB : ⁅B,P⁆ ≤ B.pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal B P hB.subnormal
      hB.short.twoPerfect hpP hBP).trans (map_mono blockU_le_core)
  have hsplitB := hb.two_subgroup_eq_module_sup_centralizer hpP hBP huBP hcommB
  have hcent : centralizer ((A ⊔ B : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
    apply le_antisymm
      (le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
        (centralizer_le (show B ≤ A ⊔ B from le_sup_right)))
    exact le_centralizer_iff.mpr
      (sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right))
  calc
    Q = (blockU A).map A.subtype ⊔ P := hsplitA
    _ = (blockU A).map A.subtype ⊔ ((blockU B).map B.subtype ⊔
        (P ⊓ centralizer (B : Set G))) := congrArg (_ ⊔ ·) hsplitB
    _ = _ := by simp only [P, Q, hcent, inf_assoc, sup_assoc]

/-- A trivial common fixed factor makes the ambient core elementary. -/
theorem alternatingFive_pair_core_elementary
    (A B : Subgroup G) (hA : IsBlock A) (hB : IsBlock B)
    (ha : IsAlternatingBlock A 5) (hb : IsAlternatingBlock B 5)
    (hc : ⁅A,B⁆ = ⊥)
    (hz : pCore 2 G ⊓ centralizer ((A ⊔ B : Subgroup G) : Set G) = ⊥) :
    IsElementaryAbelian 2 (pCore 2 G) := by
  rw [alternatingFive_pair_core_split A B hA hB ha hb hc, hz, sup_bot_eq]
  let := ha.2.1.elementary.map A.subtype
  let := hb.2.1.elementary.map B.subtype
  apply IsElementaryAbelian.sup_of_le_centralizer
  exact (map_subtype_le _).trans
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (centralizer_le (map_subtype_le _)))

end CFSG.Quasithin.ChapterC
