module
public import Theory.Mathieu.M12.SmallParabolicPair
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.QuaternionCentralProductFactorNormality

/-!
# Recognition data for the actual first parabolic of M₁₂

The marked involution generates the center of its centralizer. Its two-core
is self-centralizing, hence is the generalized Fitting subgroup. The actual
cubic fixes precisely the marked involution in that core. Both quaternion
factors are normal in the first parabolic, and they exhaust its quaternion
subgroups. These calculations supply the local inputs for I.4.6 directly
from the marked M₁₂ amalgam in source 14.2.22.

The fixed subgroup calculation uses the existing Q₈ × Q₈ coordinate cover;
only its 64 coordinate pairs are checked.

Source: Aschbacher–Smith, I.4.6, printed p.417, and 14.2.22, printed p.988.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M12SmallPair.RecognitionLocal

/-- The original point inside its actual first parabolic. -/
def point : firstParabolic := ⟨z, core_le_firstParabolic z_mem_core⟩

theorem point_order : orderOf point = 2 :=
  (Subgroup.orderOf_coe point).symm.trans z_order

theorem point_central : point ∈ center firstParabolic := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)

theorem first_center : center firstParabolic = zpowers point := by
  apply le_antisymm
  · intro x hx
    have hc : (x : M12) ∈ firstParabolic ⊓ centralizer (core : Set M12) := by
      refine ⟨x.property, ?_⟩
      intro q hq
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨q, core_le_firstParabolic hq⟩)
    rw [firstParabolic_centralizer_core] at hc
    have him : (zpowers point).map firstParabolic.subtype = distinguished := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [← him] at hc
    obtain ⟨y,hy,he⟩ := hc
    have hyx : y = x := Subtype.ext he
    exact hyx ▸ hy
  · exact zpowers_le.mpr point_central

/-- The marked two-core is self-centralizing. -/
theorem core_selfCentralizing : centralizer (pCore 2 firstParabolic : Set firstParabolic) ≤
    pCore 2 firstParabolic := by
  intro x hx
  have hc : (x : M12) ∈ firstParabolic ⊓ centralizer (core : Set M12) := by
    refine ⟨x.property, ?_⟩
    intro q hq
    have hq' : (⟨q, core_le_firstParabolic hq⟩ : firstParabolic) ∈ pCore 2 firstParabolic := by
      rw [← core_subgroupOf_eq_pCore]
      exact hq
    exact congrArg Subtype.val (hx _ hq')
  rw [firstParabolic_centralizer_core] at hc
  rw [← core_subgroupOf_eq_pCore]
  exact distinguished_le_natural.trans natural_le_core hc

theorem fitting_eq_core : generalizedFitting firstParabolic = pCore 2 firstParabolic :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2 core_selfCentralizing

/-- The model cubic as an intrinsic element. -/
def cubic : firstParabolic := ⟨cubicActor, cubicActor_mem⟩

theorem cubic_order : orderOf cubic = 3 :=
  (Subgroup.orderOf_coe cubic).symm.trans cubicActor_order

def cubicSylow : Sylow 3 firstParabolic := Sylow.ofCard (zpowers cubic) (by
  rw [Nat.card_zpowers, cubic_order, card_firstParabolic]
  decide +kernel)

private theorem cubic_fixed_coordinates :
    ∀ q r : QuaternionGroup 2,
      cubicActor * (leftEmbedding q * rightEmbedding r) =
        (leftEmbedding q * rightEmbedding r) * cubicActor →
      leftEmbedding q * rightEmbedding r = 1 ∨ leftEmbedding q * rightEmbedding r = z := by
  decide +kernel

theorem cubic_fixed_core :
    pCore 2 firstParabolic ⊓ centralizer (cubicSylow : Set firstParabolic) = zpowers point := by
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    rw [← core_subgroupOf_eq_pCore] at hx
    obtain ⟨q,r,he⟩ := (mem_core x).mp hx
    have hcomm : cubicActor * (x : M12) = (x : M12) * cubicActor :=
      congrArg Subtype.val (hc cubic (mem_zpowers cubic))
    rw [← he] at hcomm
    rcases cubic_fixed_coordinates q r hcomm with h | h
    · exact (show x = 1 from Subtype.ext (he.symm.trans h)) ▸ (zpowers point).one_mem
    · exact (show x = point from Subtype.ext (he.symm.trans h)) ▸ mem_zpowers point
  · apply zpowers_le.mpr
    refine ⟨?_, ?_⟩
    · rw [← core_subgroupOf_eq_pCore]
      exact z_mem_core
    · intro x _
      exact mem_center_iff.mp point_central x

/-- Both actual factors are normal, and they exhaust the quaternion subgroups. -/
theorem quaternion_normal (R : Subgroup core) (hR : Nonempty (R ≃* QuaternionGroup 2)) :
    ((R.map core.subtype).subgroupOf firstParabolic).Normal := by
  rcases (coreQuaternionData.quaternion_subgroup_iff R).mp hR with rfl | rfl
  · rw [leftFactor_core_image]
    exact (normal_subgroupOf_iff_le_normalizer
      ((show leftFactor ≤ core from le_sup_left).trans core_le_firstParabolic)).mpr
      firstParabolic_normalizes_left
  · rw [rightFactor_core_image]
    exact (normal_subgroupOf_iff_le_normalizer
      ((show rightFactor ≤ core from le_sup_right).trans core_le_firstParabolic)).mpr
      firstParabolic_normalizes_right

/-- Intrinsic quaternion subgroups are normal in the full first parabolic. -/
theorem quaternion_normal_core (R : Subgroup (pCore 2 firstParabolic))
    (hR : Nonempty (R ≃* QuaternionGroup 2)) :
    (R.map (pCore 2 firstParabolic).subtype).Normal := by
  let S := R.map firstCoreEquiv.toMonoidHom
  have hS : Nonempty (S ≃* QuaternionGroup 2) :=
    ⟨(firstCoreEquiv.subgroupMap R).symm.trans hR.some⟩
  have he : ((S.map core.subtype).subgroupOf firstParabolic) =
      R.map (pCore 2 firstParabolic).subtype := by
    apply map_injective firstParabolic.subtype_injective
    rw [map_subgroupOf_eq_of_le
      (show S.map core.subtype ≤ firstParabolic from fun _ hx => by
        obtain ⟨x,_,rfl⟩ := hx
        exact core_le_firstParabolic x.property)]
    change (R.map firstCoreEquiv.toMonoidHom).map core.subtype = _
    rw [map_map,map_map]
    congr 1
    exact MonoidHom.ext firstCoreEquiv_apply
  exact he ▸ quaternion_normal S hS

end Sporadic.Mathieu.M12SmallPair.RecognitionLocal
