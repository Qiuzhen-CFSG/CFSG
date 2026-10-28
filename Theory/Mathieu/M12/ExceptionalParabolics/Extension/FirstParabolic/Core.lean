module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.Order

/-!
# The concrete nonsplit quaternion extension

Adjoining the certified factor-swap lift to the original quaternion product
adds exactly one coset. The resulting actual subgroup has order 64 and is a
two-group. Its intersection with the inner group is the original order-32
core. Every square-one element belongs to that inner core: none occurs in
the outer coset. The equivalence with the existing split model's order-32
quaternion core retains both factors and the original central involution.

The normal form uses only the lift's proved square and conjugation relations;
the outside-coset square calculation uses the checked degree-24 coordinates.
Identification with the intrinsic two-core of the entire first parabolic is
a further local calculation.

Source: Aschbacher--Smith, E.2.16, F.1.12(I)(13), and 14.2.21,
printed pp.228, 263, 988, `refs/quasithin.pdf`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic

attribute [local irreducible] leftI leftJ rightI rightJ

theorem quaternionCore_eq_closure : quaternionCore =
    Subgroup.closure ({leftI,leftJ,rightI,rightJ} : Set Carrier) := by
  let K := Subgroup.closure ({leftI,leftJ,rightI,rightJ} : Set Carrier)
  have hi : leftI ∈ K := Subgroup.subset_closure (by simp)
  have hj : leftJ ∈ K := Subgroup.subset_closure (by simp)
  have hi' : rightI ∈ K := Subgroup.subset_closure (by simp)
  have hj' : rightJ ∈ K := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · apply sup_le
    · rintro _ ⟨q,rfl⟩
      cases q with
      | a n => exact K.pow_mem hi n.val
      | xa n => exact K.mul_mem hj (K.pow_mem hi n.val)
    · rintro _ ⟨q,rfl⟩
      cases q with
      | a n => exact K.pow_mem hi' n.val
      | xa n => exact K.mul_mem hj' (K.pow_mem hi' n.val)
  · apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl | rfl | rfl)
    · apply (show leftFactor ≤ quaternionCore from le_sup_left)
      exact ⟨QuaternionGroup.a 1, by simp [leftLift, quaternionWord, ZMod.val_one_eq_one_mod]⟩
    · apply (show leftFactor ≤ quaternionCore from le_sup_left)
      exact ⟨QuaternionGroup.xa 0, by simp [leftLift, quaternionWord]⟩
    · apply (show rightFactor ≤ quaternionCore from le_sup_right)
      exact ⟨QuaternionGroup.a 1, by simp [rightLift, quaternionWord, ZMod.val_one_eq_one_mod]⟩
    · apply (show rightFactor ≤ quaternionCore from le_sup_right)
      exact ⟨QuaternionGroup.xa 0, by simp [rightLift, quaternionWord]⟩

theorem splitQuaternionCoreEquiv_left (m : InnerModel) (q : QuaternionGroup 2) :
    (splitQuaternionCoreEquiv m ⟨QuaternionSwapModel.leftEmbedding q,
      (show QuaternionSwapModel.leftFactor ≤ QuaternionSwapModel.QK from le_sup_left)
        ⟨q,rfl⟩⟩ : Carrier) = leftLift q := by
  change m.embedding (M12SmallPair.SwapCoreCoordinates.coreEquiv _ : M12) = _
  rw [M12SmallPair.SwapCoreCoordinates.coreEquiv_left, map_leftLift]

theorem splitQuaternionCoreEquiv_right (m : InnerModel) (q : QuaternionGroup 2) :
    (splitQuaternionCoreEquiv m ⟨QuaternionSwapModel.rightEmbedding q,
      (show QuaternionSwapModel.rightFactor ≤ QuaternionSwapModel.QK from le_sup_right)
        ⟨q,rfl⟩⟩ : Carrier) = rightLift q := by
  change m.embedding (M12SmallPair.SwapCoreCoordinates.coreEquiv _ : M12) = _
  rw [M12SmallPair.SwapCoreCoordinates.coreEquiv_right, map_rightLift]

theorem splitQuaternionCoreEquiv_marked (m : InnerModel) :
    (splitQuaternionCoreEquiv m ⟨QuaternionSwapModel.z, QuaternionSwapModel.Z_le_QK
      ((QuaternionSwapModel.mem_Z _).mpr (Or.inr rfl))⟩ : Carrier) = z := by
  change m.embedding (M12SmallPair.SwapCoreCoordinates.coreEquiv _ : M12) = _
  rw [M12SmallPair.SwapCoreCoordinates.coreEquiv_marked]
  exact map_z m.embedding m.embedding_originalA m.embedding_originalB

theorem z_ne_one : z ≠ 1 := by
  intro h
  have hv := congrArg (fun g : Carrier => g.val) h
  exact (by decide +kernel : zPerm ≠ 1) (z_val.symm.trans hv)
theorem z_square : z ^ 2 = 1 := by
  apply Subtype.ext
  change z.val ^ 2 = 1
  exact (congrArg (fun p : Equiv.Perm (Fin 24) => p^2) z_val).trans
    (by decide +kernel : zPerm^2 = 1)

attribute [local irreducible] z nonsplitSwap leftLift rightLift

theorem orderOf_nonsplitSwap : orderOf nonsplitSwap = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · simpa only [pow_one, nonsplitSwap_square] using z_ne_one
  · change nonsplitSwap ^ (2*2) = 1
    rw [pow_mul, nonsplitSwap_square, z_square]

theorem mem_zpowers_nonsplitSwap (g : Carrier) :
    g ∈ Subgroup.zpowers nonsplitSwap ↔
      g = 1 ∨ g = nonsplitSwap ∨ g = z ∨ g = z * nonsplitSwap := by
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_nonsplitSwap]
  have h3 : nonsplitSwap ^ 3 = z * nonsplitSwap := by
    rw [show 3 = 2+1 from rfl, pow_succ, nonsplitSwap_square]
  have hr : Finset.range 4 = {0,1,2,3} := by decide
  rw [hr]
  simp only [Finset.image_insert, Finset.image_singleton, Finset.mem_insert,
    Finset.mem_singleton, pow_zero, pow_one, nonsplitSwap_square, h3]

theorem nonsplitSwap_normalizes_quaternionCore :
    nonsplitSwap ∈ Subgroup.normalizer (quaternionCore : Set Carrier) := by
  have hl : leftFactor.map (MulAut.conj nonsplitSwap).toMonoidHom = rightFactor := by
    rw [leftFactor, rightFactor, ← MonoidHom.range_comp]
    congr 1
    apply MonoidHom.ext
    intro q
    exact nonsplitSwap_left q
  have hr : rightFactor.map (MulAut.conj nonsplitSwap).toMonoidHom = leftFactor := by
    rw [leftFactor, rightFactor, ← MonoidHom.range_comp]
    congr 1
    apply MonoidHom.ext
    intro q
    exact nonsplitSwap_right q
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change quaternionCore.map (MulAut.conj nonsplitSwap).toMonoidHom = quaternionCore
  rw [quaternionCore, Subgroup.map_sup, hl, hr, sup_comm]


theorem outerCore_normalizes_quaternionCore :
    outerCore ≤ Subgroup.normalizer (quaternionCore : Set Carrier) :=
  sup_le quaternionCore.le_normalizer
    (Subgroup.zpowers_le.mpr nonsplitSwap_normalizes_quaternionCore)

instance quaternionCore_normal_outerCore : (quaternionCore.subgroupOf outerCore).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show quaternionCore ≤ outerCore from le_sup_left)).mpr outerCore_normalizes_quaternionCore

theorem nonsplitSwap_not_mem_quaternionCore (m : InnerModel) :
    nonsplitSwap ∉ quaternionCore := fun h =>
  nonsplitSwap_not_mem_inner (quaternionCore_le_inner m h)

/-- Two cosets of the original quaternion product, with the nonsplit lift retained. -/
theorem mem_outerCore (m : InnerModel) (g : Carrier) :
    g ∈ outerCore ↔ g ∈ quaternionCore ∨ ∃ q ∈ quaternionCore, q * nonsplitSwap = g := by
  change g ∈ (↑(quaternionCore ⊔ Subgroup.zpowers nonsplitSwap) : Set Carrier) ↔ _
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (Subgroup.zpowers_le.mpr nonsplitSwap_normalizes_quaternionCore)]
  constructor
  · rintro ⟨q,hq,t,ht,rfl⟩
    rcases (mem_zpowers_nonsplitSwap t).mp ht with rfl | rfl | rfl | rfl
    · exact Or.inl (by simpa using hq)
    · exact Or.inr ⟨q,hq,rfl⟩
    · exact Or.inl (quaternionCore.mul_mem hq (z_mem_quaternionCore m))
    · exact Or.inr ⟨q*z,quaternionCore.mul_mem hq (z_mem_quaternionCore m),mul_assoc _ _ _⟩
  · rintro (hg | ⟨q,hq,rfl⟩)
    · exact ⟨g,hg,1,(Subgroup.zpowers _).one_mem,mul_one g⟩
    · exact ⟨q,hq,nonsplitSwap,Subgroup.mem_zpowers _,rfl⟩

/-- Unique coset coordinates for the actual subgroup generated by the lift. -/
def outerNormalForm (a : quaternionCore × Bool) : outerCore :=
  if a.2 then ⟨a.1.val * nonsplitSwap,
    outerCore.mul_mem ((show quaternionCore ≤ outerCore from le_sup_left) a.1.property)
      ((show Subgroup.zpowers nonsplitSwap ≤ outerCore from le_sup_right)
        (Subgroup.mem_zpowers nonsplitSwap))⟩
  else ⟨a.1.val, (show quaternionCore ≤ outerCore from le_sup_left) a.1.property⟩

theorem outerNormalForm_bijective (m : InnerModel) : Function.Bijective outerNormalForm := by
  have hsep (q r : quaternionCore) : q.val ≠ r.val * nonsplitSwap := by
    intro h
    apply nonsplitSwap_not_mem_quaternionCore m
    have hh := quaternionCore.mul_mem (quaternionCore.inv_mem r.property) q.property
    rw [h, inv_mul_cancel_left] at hh
    exact hh
  constructor
  · rintro ⟨q,b⟩ ⟨r,c⟩ h
    have hv := congrArg (fun x : outerCore => x.val) h
    cases b <;> cases c
    · have hh : q.val = r.val := hv
      exact congrArg (fun x : quaternionCore => (x,false)) (Subtype.ext hh)
    · exact False.elim (hsep q r hv)
    · exact False.elim (hsep r q hv.symm)
    · have hh : q.val * nonsplitSwap = r.val * nonsplitSwap := hv
      exact congrArg (fun x : quaternionCore => (x,true)) (Subtype.ext (mul_right_cancel hh))
  · intro x
    rcases (mem_outerCore m x.val).mp x.property with hx | ⟨q,hq,hq'⟩
    · exact ⟨(⟨x,hx⟩,false),rfl⟩
    · exact ⟨(⟨q,hq⟩,true),Subtype.ext hq'⟩

theorem card_outerCore (m : InnerModel) : Nat.card outerCore = 64 := by
  rw [← Nat.card_eq_of_bijective outerNormalForm (outerNormalForm_bijective m),
    Nat.card_prod, card_quaternionCore m]
  norm_num [Nat.card_eq_fintype_card]

theorem outerCore_isPGroup (m : InnerModel) : IsPGroup 2 outerCore :=
  IsPGroup.of_card (n := 6) (card_outerCore m)


section
set_option maxRecDepth 100000

/-- Every element in the outer coset has nonidentity square. -/
theorem nonsplit_coset_square_ne_one (q r : QuaternionGroup 2) :
    (leftLift q * rightLift r * nonsplitSwap)^2 ≠ 1 := by
  intro h
  have hv := congrArg (fun g : Carrier => g.val) h
  unfold leftLift rightLift nonsplitSwap at hv
  change ((quaternionWord leftI leftJ q).val *
    (quaternionWord rightI rightJ r).val * nonsplitSwapPerm)^2 = 1 at hv
  rw [quaternionWord_left_val, quaternionWord_right_val] at hv
  have hn : ∀ q r : QuaternionGroup 2,
      (quaternionPerm leftIPerm leftJPerm q *
        quaternionPerm rightIPerm rightJPerm r * nonsplitSwapPerm)^2 ≠ 1 := by
    decide +kernel
  exact hn q r hv
end

/-- In particular there is no swapping involution in this order-64 subgroup. -/
theorem outerCore_square_one_mem_quaternionCore (m : InnerModel)
    (x : Carrier) (hx : x ∈ outerCore) (hsq : x^2 = 1) : x ∈ quaternionCore := by
  rcases (mem_outerCore m x).mp hx with hx | ⟨q,hq,rfl⟩
  · exact hx
  · obtain ⟨a,b,rfl⟩ := (mem_quaternionCore m q).mp hq
    exact False.elim (nonsplit_coset_square_ne_one a b hsq)


theorem outerCore_le_firstParabolic (m : InnerModel) : outerCore ≤ firstParabolic :=
  sup_le (quaternionCore_le_firstParabolic m)
    (Subgroup.zpowers_le.mpr nonsplitSwap_mem_firstParabolic)

/-- Its intersection with the marked inner subgroup is exactly the original core. -/
theorem outerCore_inf_inner (m : InnerModel) : outerCore ⊓ inner = quaternionCore := by
  apply le_antisymm
  · intro x hx
    rcases (mem_outerCore m x).mp hx.1 with h | ⟨q,hq,rfl⟩
    · exact h
    · have hh := inner.mul_mem (inner.inv_mem (quaternionCore_le_inner m hq)) hx.2
      rw [inv_mul_cancel_left] at hh
      exact False.elim (nonsplitSwap_not_mem_inner hh)
  · exact le_inf (show quaternionCore ≤ outerCore from le_sup_left) (quaternionCore_le_inner m)

end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
