module

public import Theory.GroupAction.FourGroupCoreAction
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction

/-!
# Fixed point cores in the four-group action

The two fixed subgroups are normal two-subgroups of the four-group
centralizer. Their join is their literal product, is normal in the generated
group and in the four-group normalizer, and contains every commutator of the
centralizer with the generated group. All normality is relative to the stated
local overgroup. The join lies in the generated group's two-core, which in turn
lies in the action kernel.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), A.1.14(1), printed p.23.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace FourGroupCorePair
variable {G : Type*} [Group G] {V : Subgroup G} {v₁ v₂ : G}

theorem centralizer_le_normalizer_pointCore {v : G} (hv : v ∈ V) :
    centralizer (V : Set G) ≤ normalizer (core v : Set G) := by
  have hC : centralizer (V : Set G) ≤ centralizer ({v} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hv)
  apply hC.trans
  simpa only [core, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    using (pCore 2 (centralizer ({v} : Set G))).le_normalizer_map
      (centralizer ({v} : Set G)).subtype

theorem centralizer_le_normalizer_pointKernel {v : G} (hv : v ∈ V) :
    centralizer (V : Set G) ≤ normalizer (pointKernel V v : Set G) :=
  (le_inf (centralizer_le_normalizer_pointCore hv)
    (centralizer (V : Set G)).le_normalizer).trans inf_normalizer_le_normalizer_inf

theorem pointKernel_normal {v : G} (hv : v ∈ V) :
    ((pointKernel V v).subgroupOf (centralizer (V : Set G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
    (centralizer_le_normalizer_pointKernel hv)

theorem pointKernel_isPGroup (V : Subgroup G) (v : G) : IsPGroup 2 (pointKernel V v) :=
  (isPGroup_pCoreIn 2 (centralizer ({v} : Set G))).to_le inf_le_left

variable (h : FourGroupCorePair V v₁ v₂)
include h

omit h in
theorem kernelJoin_le_centralizer : kernelJoin V v₁ v₂ ≤ centralizer (V : Set G) :=
  sup_le inf_le_right inf_le_right

omit h in
theorem kernelJoin_le_generated : kernelJoin V v₁ v₂ ≤ generated v₁ v₂ :=
  sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

theorem centralizer_le_normalizer_kernelJoin :
    centralizer (V : Set G) ≤ normalizer (kernelJoin V v₁ v₂ : Set G) :=
  (le_inf (centralizer_le_normalizer_pointKernel h.mem₁)
    (centralizer_le_normalizer_pointKernel h.mem₂)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem kernelJoin_normal_centralizer :
    ((kernelJoin V v₁ v₂).subgroupOf (centralizer (V : Set G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer kernelJoin_le_centralizer).mpr
    h.centralizer_le_normalizer_kernelJoin

theorem kernelJoin_isPGroup : IsPGroup 2 (kernelJoin V v₁ v₂) :=
  (pointKernel_isPGroup V v₁).to_sup_of_normal_right' (pointKernel_isPGroup V v₂)
    (inf_le_right.trans (centralizer_le_normalizer_pointKernel h.mem₂))

theorem mem_kernelJoin_iff (x : G) : x ∈ kernelJoin V v₁ v₂ ↔
    ∃ a ∈ pointKernel V v₁, ∃ b ∈ pointKernel V v₂, a * b = x := by
  constructor
  · intro hx
    let C := centralizer (V : Set G)
    let K₁ := (pointKernel V v₁).subgroupOf C
    let K₂ := (pointKernel V v₂).subgroupOf C
    let : K₂.Normal := pointKernel_normal h.mem₂
    have hxC : x ∈ C := kernelJoin_le_centralizer hx
    have hx' : (⟨x, hxC⟩ : C) ∈ K₁ ⊔ K₂ := by
      rw [← subgroupOf_sup (show pointKernel V v₁ ≤ C from inf_le_right)
        (show pointKernel V v₂ ≤ C from inf_le_right)]
      exact hx
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp hx'
    exact ⟨a, ha, b, hb, congrArg Subtype.val hab⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

omit h in
theorem normalizer_le_normalizer_fixed :
    normalizer (V : Set G) ≤ normalizer (centralizer (V : Set G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (V : Set G))).mp
    inferInstance

omit h in
theorem centralizer_commutator_core_le {v : G} (hv : v ∈ V)
    (hn : core v ≤ normalizer (V : Set G)) :
    ⁅centralizer (V : Set G), core v⁆ ≤ pointKernel V v :=
  le_inf (le_normalizer_iff_commutator_le_right.mp
    (centralizer_le_normalizer_pointCore hv))
    (le_normalizer_iff_commutator_le_left.mp (hn.trans normalizer_le_normalizer_fixed))

theorem generated_le_normalizer_kernelJoin :
    generated v₁ v₂ ≤ normalizer (kernelJoin V v₁ v₂ : Set G) := by
  apply sup_le
  · apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono kernelJoin_le_centralizer le_rfl).trans
      ((centralizer_commutator_core_le h.mem₁ h.core_le_normalizer₁).trans le_sup_left)
  · apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono kernelJoin_le_centralizer le_rfl).trans
      ((centralizer_commutator_core_le h.mem₂ h.core_le_normalizer₂).trans le_sup_right)

theorem kernelJoin_normal_generated :
    ((kernelJoin V v₁ v₂).subgroupOf (generated v₁ v₂)).Normal :=
  (normal_subgroupOf_iff_le_normalizer kernelJoin_le_generated).mpr
    h.generated_le_normalizer_kernelJoin

theorem kernelJoin_le_twoCore : kernelJoin V v₁ v₂ ≤ (generated v₁ v₂).pCoreIn 2 :=
  le_pCoreIn_of_normalizes h.kernelJoin_isPGroup kernelJoin_le_generated
    h.generated_le_normalizer_kernelJoin

theorem centralizer_commutator_generated_le :
    ⁅centralizer (V : Set G), generated v₁ v₂⁆ ≤ kernelJoin V v₁ v₂ := by
  rw [commutator_comm]
  have h₁ : core v₁ ≤ commutatorPreimage (generated v₁ v₂)
      (centralizer (V : Set G)) (kernelJoin V v₁ v₂) := by
    apply le_commutatorPreimage le_sup_left
    rw [commutator_comm]
    exact (centralizer_commutator_core_le h.mem₁ h.core_le_normalizer₁).trans le_sup_left
  have h₂ : core v₂ ≤ commutatorPreimage (generated v₁ v₂)
      (centralizer (V : Set G)) (kernelJoin V v₁ v₂) := by
    apply le_commutatorPreimage le_sup_right
    rw [commutator_comm]
    exact (centralizer_commutator_core_le h.mem₂ h.core_le_normalizer₂).trans le_sup_right
  exact (commutator_mono (sup_le h₁ h₂) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ h.generated_le_normalizer_kernelJoin)

theorem kernelJoin_normal_normalizer [Finite G] :
    ((kernelJoin V v₁ v₂).subgroupOf (normalizer (V : Set G))).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    (kernelJoin_le_generated.trans h.generated_le_normalizer)).mpr
  rw [h.normalizer_eq_sup_centralizer]
  exact sup_le h.generated_le_normalizer_kernelJoin h.centralizer_le_normalizer_kernelJoin

theorem twoCore_le_action_ker [Finite G] : pCore 2 (generated v₁ v₂) ≤ h.action.ker := by
  let := h.four
  exact IsKleinFour.twoCore_le_ker_of_surjective V h.action h.action_surjective

theorem twoCore_le_generated_inf_centralizer [Finite G] :
    (generated v₁ v₂).pCoreIn 2 ≤ generated v₁ v₂ ⊓ centralizer (V : Set G) := by
  apply le_inf (pCoreIn_le 2 _)
  have hh := map_mono (f := (generated v₁ v₂).subtype) h.twoCore_le_action_ker
  rw [h.action_ker, subgroupOf_map_subtype] at hh
  exact hh.trans inf_le_left
end FourGroupCorePair
