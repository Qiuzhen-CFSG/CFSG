module
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalNormalReduction
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreInRestriction
/-!
# The literal E.2.8 core placement for an outside qrc module

The source proof of 3.1.6(i) applies E.2.13 with `H ∩ M` as its maximal
subgroup. The module is in that subgroup's two-core before the E.2.13 action
is formed. This is a separate transport fact: it uses the characteristic-two
local core of `M`, the qrc identity `O₂(M₀)=C_T(V)`, and restriction of a prime
core to `H ∩ M`; it does not assume that `H ∩ M` normalizes `V`.

Source: Aschbacher--Smith, proof of Theorem 3.1.6, printed pp.573--574;
A.1.6 and B.6.8.5.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The qrc module lies in the ambient maximal two-core. -/
theorem QrcHypotheses.module_le_maximal_core
    (h : QrcHypotheses T M M₀ H V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) : V ≤ M.pCoreIn 2 := by
  have hCM : M ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T)
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1, h.sylow_le.trans h.left_le⟩
  have hc : M.pCoreIn 2 ≤ centralizer (V : Set G) := by
    have hr := twoCore_le_of_sylow_le T h.sylow_le h.left_le
    rw [h.core_eq_centralizer] at hr
    exact hr.trans inf_le_right
  exact (le_inf (h.module_le.trans h.left_le) (le_centralizer_iff.mp hc)).trans hCM

/-- The qrc module lies in the two-core of the source maximal subgroup `H ∩ M`.
No normalizer hypothesis on `H ∩ M` is used. -/
theorem QrcHypotheses.module_le_intersection_core
    (h : QrcHypotheses T M M₀ H V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) : V ≤ (H ⊓ M).pCoreIn 2 := by
  have hVH : V ≤ H := h.module_le_sylow.trans h.right_mem.1.1.2
  exact (le_inf (le_inf hVH (h.module_le.trans h.left_le))
    (h.module_le_maximal_core hG hM)).trans (inf_pCoreIn_le_of_le 2 inf_le_right)

/-- Intrinsic form used by the E.2.13 witness constructors. -/
theorem QrcHypotheses.intrinsic_module_le_maximal_core
    (h : QrcHypotheses T M M₀ H V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤) :
    V.subgroupOf H ≤
      (ChapterB.minimalParabolicMax (T.subtype h.right_mem.1.1.2) hp).pCoreIn 2 := by
  rw [h.intrinsic_maximal_eq_intersection hp,
    pCoreIn_subgroupOf 2 _ _ inf_le_left]
  exact subgroupOf_mono H (h.module_le_intersection_core hG hM)

end CFSG.Quasithin.Chapter3
