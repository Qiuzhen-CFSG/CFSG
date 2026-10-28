module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients

/-!
# A common Sylow subgroup and fixed-point geometry in M₂₂

The intersection of the pair and three-pair partition stabilizers has order
128, so it is an actual Sylow two-subgroup. We also include the kernel of the
five-hexad action into M₂₂ and record its order and relative normality.
A subgroup normalizer preserves the common fixed points in the degree-22
action. This turns fixed-point calculations into local-overgroup bounds.

These interfaces support the even-characteristic calculation for M₂₂ in
Aschbacher–Smith, Theorem 0.1.2(5), printed pp.3–4 (also pp.481–482).
They do not assert the remaining finite fixed-point or centralizer calculations.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22EvenGeometry
open Subgroup M22ValueBound.Concrete
open scoped Pointwise

/-- The actual common Sylow of the pair and three-pair partition stabilizers. -/
noncomputable def sylow : Sylow 2 M22 :=
  Sylow.ofCard (first ⊓ second) (by
    rw [PartitionStructure.intersection_card, m22_order]
    decide +kernel)

@[simp] theorem sylow_coe : (sylow : Subgroup M22) = first ⊓ second := rfl

theorem sylow_card : Nat.card sylow = 128 := PartitionStructure.intersection_card

/-- Common fixed points of an actual subgroup in the natural action. -/
noncomputable def commonFixedPoints (R : Subgroup M22) : Finset (Fin 22) := by
  classical
  exact Finset.univ.filter fun a => ∀ r ∈ R, r • a = a

@[simp] theorem mem_commonFixedPoints (R : Subgroup M22) (a : Fin 22) :
    a ∈ commonFixedPoints R ↔ ∀ r ∈ R, r • a = a := by
  classical
  simp only [commonFixedPoints, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Conjugating the subgroup transports its fixed points, hence its normalizer
preserves their full set. No normality in the ambient simple group is assumed. -/
theorem normalizer_le_fixedPoints_stabilizer (R : Subgroup M22) :
    normalizer (R : Set M22) ≤ MulAction.stabilizer M22 (commonFixedPoints R) := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a ha
  apply (mem_commonFixedPoints R _).mpr
  intro r hr
  have hv := (mem_normalizer_iff.mp ((normalizer (R : Set M22)).inv_mem hg) r).mp hr
  have hf := (mem_commonFixedPoints R a).mp ha _ hv
  have he := congrArg (fun b : Fin 22 => g • b) hf
  simpa only [inv_inv, mul_smul, smul_inv_smul] using he

/-- The kernel of the five-hexad action, embedded in the original M₂₂. -/
noncomputable def pairKernel : Subgroup M22 := pairAction.ker.map first.subtype

theorem pairKernel_le : pairKernel ≤ first := map_subtype_le _

theorem pairKernel_card : Nat.card pairKernel = 16 :=
  (card_subtype _ _).trans pairAction_ker_card

theorem pairKernel_ne_bot : pairKernel ≠ ⊥ := by
  intro he
  have hc := pairKernel_card
  rw [he, card_bot] at hc
  norm_num at hc

theorem pairKernel_isTwoGroup : IsPGroup 2 pairKernel :=
  IsPGroup.of_card (n := 4) pairKernel_card

/-- Normality of the kernel is relative to the pair stabilizer. -/
theorem first_le_pairKernel_normalizer : first ≤ normalizer (pairKernel : Set M22) := by
  intro g hg
  apply le_normalizer_map first.subtype
  refine ⟨⟨g, hg⟩, ?_, rfl⟩
  rw [normalizer_eq_top]
  exact mem_top _

theorem pairKernel_normal : (pairKernel.subgroupOf first).Normal :=
  (normal_subgroupOf_iff_le_normalizer pairKernel_le).mpr first_le_pairKernel_normalizer

/-- The chosen ambient subgroup really is the image of the intrinsic two-core. -/
theorem pairKernel_eq_twoCore_image : pairKernel = (pCore 2 first).map first.subtype := by
  rw [pairKernel, pairAction_ker_eq_twoCore]

end Sporadic.Mathieu.M22EvenGeometry
