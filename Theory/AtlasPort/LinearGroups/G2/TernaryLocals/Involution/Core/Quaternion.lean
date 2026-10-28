module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Core.Action
public import Theory.PGroupCore
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# A normal quaternion two-subgroup of the generated ternary local group

The actual quaternion elements define commuting homomorphisms from Q₈.
Their product image is therefore a two-group. The five generators normalize
both quaternion images, as verified by their action on the three octonion
generators. Thus this product image is normal relative to `generated`, and
its intrinsic copy lies in the two-core. No group-order calculation is used.

Source application: Aschbacher–Smith, I.4(G1), printed p.417, and Main Theorem
0.1.2(4), pp.3–4 (also pp.481–482). See Core.Action for coordinate attribution.
-/

@[expose] public section

namespace Atlas.G2.TernaryLocals.Involution.CoreCalculation
open Atlas.SplitOctonion
set_option maxRecDepth 100000

/-- The two concrete quaternion homomorphisms. Injectivity is not needed here. -/
def qhom (s : Bool) : QuaternionGroup 2 →* P where
  toFun := qmap s
  map_one' := by change quaternionI s ^ 0 = 1; exact pow_zero _
  map_mul' a b := by
    apply local_ext
    intro i j
    change (qmap s (a*b)).val.val (marks i) j =
      (qmap s a).val.val ((qmap s b).val.val (marks i)) j
    simp only [qmap_apply]
    exact (by decide +kernel : ∀ s (a b : QuaternionGroup 2) i j,
      qApply s (a*b) (marks i) j = qApply s a (qApply s b (marks i)) j) s a b i j

theorem qhom_apply (s : Bool) (q : QuaternionGroup 2) (x : Carrier K) :
    (qhom s q).val.val x = qApply s q x := qmap_apply s q x

theorem qhom_commute (a b : QuaternionGroup 2) : Commute (qhom false a) (qhom true b) := by
  apply local_ext
  intro i j
  change (qhom false a).val.val ((qhom true b).val.val (marks i)) j =
    (qhom true b).val.val ((qhom false a).val.val (marks i)) j
  simp only [qhom_apply]
  exact (by decide +kernel : ∀ (a b : QuaternionGroup 2) i j,
    qApply false a (qApply true b (marks i)) j =
    qApply true b (qApply false a (marks i)) j) a b i j

def productHom : QuaternionGroup 2 × QuaternionGroup 2 →* P :=
  (qhom false).noncommCoprod (qhom true) qhom_commute

/-- The central product of the two concrete quaternion images. -/
def quaternionSubgroup : Subgroup P := productHom.range

theorem quaternionSubgroup_eq : quaternionSubgroup = (qhom false).range ⊔ (qhom true).range :=
  MonoidHom.noncommCoprod_range _ _ _

theorem quaternionSubgroup_isPGroup : IsPGroup 2 quaternionSubgroup := by
  have hp : IsPGroup 2 (QuaternionGroup 2 × QuaternionGroup 2) := by
    apply IsPGroup.of_card (n := 6)
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
  exact hp.of_surjective productHom.rangeRestrict productHom.rangeRestrict_surjective

theorem qhom_mem_generated (s : Bool) (q : QuaternionGroup 2) : qhom s q ∈ generated := by
  cases q with
  | a i => exact generated.pow_mem (quaternionI_mem s) _
  | xa i =>
    exact generated.mul_mem (quaternionJ_mem s) (generated.pow_mem (quaternionI_mem s) _)

theorem quaternionSubgroup_le_generated : quaternionSubgroup ≤ generated := by
  rintro _ ⟨⟨a,b⟩,rfl⟩
  exact generated.mul_mem (qhom_mem_generated false a) (qhom_mem_generated true b)

theorem generator_normalizes_factor (i : Fin 5) (s : Bool) :
    generator i ∈ Subgroup.normalizer ((qhom s).range : Set P) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨q,rfl⟩
  have h : ∀ i s (q : QuaternionGroup 2), ∃ r : QuaternionGroup 2, ∀ k j,
      genApply i (qApply s q (marks k)) j = qApply s r (genApply i (marks k)) j := by
    decide +kernel
  obtain ⟨r,hr⟩ := h i s q
  refine ⟨r, ?_⟩
  have he : generator i * qhom s q = qhom s r * generator i := by
    apply local_ext
    intro k j
    change (generator i).val.val ((qhom s q).val.val (marks k)) j =
      (qhom s r).val.val ((generator i).val.val (marks k)) j
    simpa only [gen_apply, qhom_apply] using hr k j
  rw [he, mul_inv_cancel_right]

theorem generated_normalizes_quaternionSubgroup :
    generated ≤ Subgroup.normalizer (quaternionSubgroup : Set P) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  rw [quaternionSubgroup_eq]
  exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _
    ⟨generator_normalizes_factor i false, generator_normalizes_factor i true⟩

/-- The quaternion subgroup viewed intrinsically in the root-generated group. -/
def intrinsicQuaternion : Subgroup generated := quaternionSubgroup.subgroupOf generated

instance intrinsicQuaternion_normal : intrinsicQuaternion.Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer generated_normalizes_quaternionSubgroup

theorem intrinsicQuaternion_isPGroup : IsPGroup 2 intrinsicQuaternion :=
  quaternionSubgroup_isPGroup.comap_subtype

theorem intrinsicQuaternion_le_pCore : intrinsicQuaternion ≤ pCore 2 generated :=
  le_sSup ⟨intrinsicQuaternion_normal, intrinsicQuaternion_isPGroup⟩

theorem quaternionI_mem_subgroup (s : Bool) : quaternionI s ∈ quaternionSubgroup := by
  rw [quaternionSubgroup_eq]
  have h : qhom s (.a 1) = quaternionI s := pow_one _
  rw [← h]
  cases s
  · exact Subgroup.mem_sup_left ⟨_,rfl⟩
  · exact Subgroup.mem_sup_right ⟨_,rfl⟩

theorem quaternionJ_mem_subgroup (s : Bool) : quaternionJ s ∈ quaternionSubgroup := by
  rw [quaternionSubgroup_eq]
  have h : qhom s (.xa 0) = quaternionJ s := by
    change quaternionJ s * quaternionI s ^ 0 = quaternionJ s
    simp
  rw [← h]
  cases s
  · exact Subgroup.mem_sup_left ⟨_,rfl⟩
  · exact Subgroup.mem_sup_right ⟨_,rfl⟩

theorem centralSign_mem_subgroup : centralSign ∈ quaternionSubgroup := by
  rw [← quaternionI_sq false]
  exact quaternionSubgroup.pow_mem (quaternionI_mem_subgroup false) 2

end Atlas.G2.TernaryLocals.Involution.CoreCalculation
