module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.Core

/-!
# The center and square-one geometry of the nonsplit core

The actual order-64 subgroup has center exactly the original marked involution.
Its square-one elements are the twenty in the original quaternion central product;
the split quaternion-swap model has twenty-eight. Thus these groups are not
isomorphic. A faithful central cyclic factor of order four is also impossible.

Center calculations use the published permutation tables. The square-one counts
are kernel-checked on the split model's 128-element cover, then transported only
along the checked equivalence of the order-32 quaternion cores.

Sources: Aschbacher--Smith, E.2.16 and F.1.12(I)(13), printed pp.228 and 263,
and 14.2.21, printed p.988, refs/quasithin.pdf. In the central-product convention
of E.2.16, the printed C4 * Q8² assertion is incompatible with this concrete core;
the obstruction here is a theorem about central C4 embeddings, not a group label.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

attribute [local irreducible] leftI leftJ rightI rightJ z nonsplitSwap

theorem mem_distinguished (x : Carrier) : x ∈ distinguished ↔ x = 1 ∨ x = z := by
  have ho : orderOf z = 2 := orderOf_eq_prime z_square z_ne_one
  change x ∈ Subgroup.zpowers z ↔ _
  rw [mem_zpowers_iff_mem_range_orderOf, ho]
  have hr : Finset.range 2 = {0,1} := by decide
  rw [hr]
  simp

theorem card_distinguished : Nat.card distinguished = 2 := by
  have he : (distinguished : Set Carrier) = {1,z} := by
    ext x
    exact (mem_distinguished x).trans (by simp)
  rw [← SetLike.coe_sort_coe, he, Nat.card_coe_set_eq]
  exact Set.ncard_pair z_ne_one.symm

theorem leftLift_mem_quaternionCore (q : QuaternionGroup 2) : leftLift q ∈ quaternionCore :=
  (show leftFactor ≤ quaternionCore from le_sup_left) ⟨q,rfl⟩
theorem rightLift_mem_quaternionCore (q : QuaternionGroup 2) : rightLift q ∈ quaternionCore :=
  (show rightFactor ≤ quaternionCore from le_sup_right) ⟨q,rfl⟩

def outerLeft : QuaternionGroup 2 →* outerCore :=
  leftLift.codRestrict outerCore (fun q => (show quaternionCore ≤ outerCore from le_sup_left) (leftLift_mem_quaternionCore q))
def outerRight : QuaternionGroup 2 →* outerCore :=
  rightLift.codRestrict outerCore (fun q => (show quaternionCore ≤ outerCore from le_sup_left) (rightLift_mem_quaternionCore q))
def outerSwap : outerCore := ⟨nonsplitSwap, (show Subgroup.zpowers nonsplitSwap ≤ outerCore from le_sup_right) (Subgroup.mem_zpowers _)⟩

def coordinate (q r : QuaternionGroup 2) (b : Bool) : outerCore :=
  outerLeft q * outerRight r * if b then outerSwap else 1

theorem leftLift_neg : leftLift (QuaternionGroup.a 2) = z := by
  apply Subtype.ext
  change (quaternionWord leftI leftJ (QuaternionGroup.a 2)).val = z.val
  rw [quaternionWord_left_val, z_val]
  decide +kernel

theorem rightLift_neg : rightLift (QuaternionGroup.a 2) = z := by
  apply Subtype.ext
  change (quaternionWord rightI rightJ (QuaternionGroup.a 2)).val = z.val
  rw [quaternionWord_right_val, z_val]
  decide +kernel

theorem distinguished_le_outerCore : distinguished ≤ outerCore := by
  apply Subgroup.zpowers_le.mpr
  rw [← leftLift_neg]
  exact (outerLeft (QuaternionGroup.a 2)).property

/-- Centrality uses the actual generators, independently of the inner-model identification. -/
theorem outerCore_centralizes_z : outerCore ≤ firstParabolic := by
  apply sup_le
  · apply sup_le
    · rintro _ ⟨q,rfl⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      change (quaternionWord leftI leftJ q).val * z.val =
        z.val * (quaternionWord leftI leftJ q).val
      rw [quaternionWord_left_val, z_val]
      have h : ∀ q : QuaternionGroup 2,
          quaternionPerm leftIPerm leftJPerm q * zPerm =
          zPerm * quaternionPerm leftIPerm leftJPerm q := by decide +kernel
      exact h q
    · rintro _ ⟨q,rfl⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      change (quaternionWord rightI rightJ q).val * z.val =
        z.val * (quaternionWord rightI rightJ q).val
      rw [quaternionWord_right_val, z_val]
      have h : ∀ q : QuaternionGroup 2,
          quaternionPerm rightIPerm rightJPerm q * zPerm =
          zPerm * quaternionPerm rightIPerm rightJPerm q := by decide +kernel
      exact h q
  · exact Subgroup.zpowers_le.mpr nonsplitSwap_mem_firstParabolic

theorem distinguished_subgroupOf_le_center :
    distinguished.subgroupOf outerCore ≤ Subgroup.center outerCore := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  change y.val * x.val = x.val * y.val
  rcases (mem_distinguished x.val).mp hx with h | h
  · simp [h]
  · rw [h]
    exact Subgroup.mem_centralizer_singleton_iff.mp (outerCore_centralizes_z y.property)

instance distinguished_normal_outerCore : (distinguished.subgroupOf outerCore).Normal :=
  ⟨fun x hx g => by
    have h := Subgroup.mem_center_iff.mp (distinguished_subgroupOf_le_center hx) g
    rw [h, mul_inv_cancel_right]
    exact hx⟩

theorem coordinate_surjective (m : InnerModel) (x : outerCore) :
    ∃ q r b, coordinate q r b = x := by
  rcases (mem_outerCore m x.val).mp x.property with hx | ⟨y,hy,he⟩
  · obtain ⟨q,r,hr⟩ := (mem_quaternionCore m x.val).mp hx
    exact ⟨q,r,false,Subtype.ext (by simpa [coordinate, outerLeft, outerRight] using hr)⟩
  · obtain ⟨q,r,rfl⟩ := (mem_quaternionCore m y).mp hy
    exact ⟨q,r,true,Subtype.ext he⟩

def coordinatePerm (q r : QuaternionGroup 2) (b : Bool) : Equiv.Perm (Fin 24) :=
  quaternionPerm leftIPerm leftJPerm q * quaternionPerm rightIPerm rightJPerm r *
    if b then nonsplitSwapPerm else 1

theorem coordinate_val (q r : QuaternionGroup 2) (b : Bool) :
    (coordinate q r b).val.val = coordinatePerm q r b := by
  cases b
  · change (quaternionWord leftI leftJ q).val * (quaternionWord rightI rightJ r).val * 1 = _
    rw [quaternionWord_left_val, quaternionWord_right_val]
    rfl
  · change (quaternionWord leftI leftJ q).val * (quaternionWord rightI rightJ r).val * nonsplitSwap.val = _
    rw [quaternionWord_left_val, quaternionWord_right_val]
    unfold nonsplitSwap
    rfl

private theorem center_coordinate_check : ∀ q r : QuaternionGroup 2, ∀ b : Bool,
    leftIPerm * coordinatePerm q r b = coordinatePerm q r b * leftIPerm →
    leftJPerm * coordinatePerm q r b = coordinatePerm q r b * leftJPerm →
    rightIPerm * coordinatePerm q r b = coordinatePerm q r b * rightIPerm →
    rightJPerm * coordinatePerm q r b = coordinatePerm q r b * rightJPerm →
    coordinatePerm q r b = 1 ∨ coordinatePerm q r b = zPerm := by decide +kernel

theorem mem_center_outerCore (m : InnerModel) (x : outerCore) :
    x ∈ Subgroup.center outerCore ↔ x.val = 1 ∨ x.val = z := by
  constructor
  · intro hx
    obtain ⟨q,r,b,rfl⟩ := coordinate_surjective m x
    have hc := Subgroup.mem_center_iff.mp hx
    have hl (a : QuaternionGroup 2) := congrArg (fun g : outerCore => g.val.val) (hc (outerLeft a))
    have hr (a : QuaternionGroup 2) := congrArg (fun g : outerCore => g.val.val) (hc (outerRight a))
    have hl' (a : QuaternionGroup 2) :
        quaternionPerm leftIPerm leftJPerm a * coordinatePerm q r b =
        coordinatePerm q r b * quaternionPerm leftIPerm leftJPerm a := by
      have h := hl a
      change (quaternionWord leftI leftJ a).val * (coordinate q r b).val.val =
        (coordinate q r b).val.val * (quaternionWord leftI leftJ a).val at h
      simpa only [quaternionWord_left_val, coordinate_val] using h
    have hr' (a : QuaternionGroup 2) :
        quaternionPerm rightIPerm rightJPerm a * coordinatePerm q r b =
        coordinatePerm q r b * quaternionPerm rightIPerm rightJPerm a := by
      have h := hr a
      change (quaternionWord rightI rightJ a).val * (coordinate q r b).val.val =
        (coordinate q r b).val.val * (quaternionWord rightI rightJ a).val at h
      simpa only [quaternionWord_right_val, coordinate_val] using h
    have hi : ∀ i j : Equiv.Perm (Fin 24), quaternionPerm i j (QuaternionGroup.a 1) = i := by
      intro i j
      simp [quaternionPerm, ZMod.val_one_eq_one_mod]
    have hj : ∀ i j : Equiv.Perm (Fin 24), quaternionPerm i j (QuaternionGroup.xa 0) = j := by
      intro i j
      simp [quaternionPerm]
    rcases center_coordinate_check q r b (by simpa [hi] using hl' (QuaternionGroup.a 1))
      (by simpa [hj] using hl' (QuaternionGroup.xa 0))
      (by simpa [hi] using hr' (QuaternionGroup.a 1))
      (by simpa [hj] using hr' (QuaternionGroup.xa 0)) with h | h
    · exact Or.inl (Subtype.ext ((coordinate_val q r b).trans h))
    · exact Or.inr (Subtype.ext ((coordinate_val q r b).trans (h.trans z_val.symm)))
  · rintro (hx | hx)
    · have he : x = 1 := Subtype.ext hx
      rw [he]
      exact (Subgroup.center outerCore).one_mem
    · apply Subgroup.mem_center_iff.mpr
      intro y
      apply Subtype.ext
      change y.val * x.val = x.val * y.val
      rw [hx]
      exact Subgroup.mem_centralizer_singleton_iff.mp (outerCore_le_firstParabolic m y.property)

theorem center_outerCore_image (m : InnerModel) :
    (Subgroup.center outerCore).map outerCore.subtype = distinguished := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (mem_distinguished _).mpr ((mem_center_outerCore m a).mp ha)
  · intro hx
    have ho : x ∈ outerCore := by
      rcases (mem_distinguished x).mp hx with rfl | rfl
      · exact outerCore.one_mem
      · exact (show quaternionCore ≤ outerCore from le_sup_left) (z_mem_quaternionCore m)
    exact ⟨⟨x,ho⟩,(mem_center_outerCore m _).mpr ((mem_distinguished x).mp hx),rfl⟩

theorem center_outerCore_eq (m : InnerModel) :
    Subgroup.center outerCore = distinguished.subgroupOf outerCore := by
  ext x
  exact (mem_center_outerCore m x).trans (mem_distinguished x.val).symm

theorem card_center_outerCore (m : InnerModel) : Nat.card (Subgroup.center outerCore) = 2 := by
  rw [← card_distinguished, ← center_outerCore_image m]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).toEquiv

theorem center_outerCore_square (m : InnerModel) (x : outerCore)
    (hx : x ∈ Subgroup.center outerCore) : x ^ 2 = 1 := by
  apply Subtype.ext
  rcases (mem_center_outerCore m x).mp hx with h | h
  · change x.val^2 = 1
    rw [h, one_pow]
  · change x.val^2 = 1
    rw [h, z_square]

theorem no_central_order_four (m : InnerModel) (x : outerCore)
    (hx : x ∈ Subgroup.center outerCore) : orderOf x ≠ 4 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one (center_outerCore_square m x hx)
  rw [h] at hd
  norm_num at hd

/-- In particular, no faithful central C4 factor can occur in a central-product presentation. -/
theorem no_central_cyclic_four_embedding (m : InnerModel)
    (f : Multiplicative (ZMod 4) →* outerCore) (hf : Function.Injective f)
    (hc : f.range ≤ Subgroup.center outerCore) : False := by
  let a : Multiplicative (ZMod 4) := Multiplicative.ofAdd 1
  have ha := center_outerCore_square m (f a) (hc ⟨a,rfl⟩)
  have hh : a ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using ha)
  exact (by decide +kernel : (Multiplicative.ofAdd (1 : ZMod 4))^2 ≠ 1) hh

end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic

namespace QuaternionSwapModel
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem card_diagonalCenter : Nat.card diagonalCenter = 2 := by
  have he : (diagonalCenter : Set Raw) = {1,killed} := rfl
  rw [← SetLike.coe_sort_coe, he, Nat.card_coe_set_eq]
  exact Set.ncard_pair (by decide +kernel)

private theorem count_raw_square :
    Nat.card {r : Raw // r^2 = 1 ∨ r^2 = killed} = 56 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem count_raw_core_square :
    Nat.card {r : Raw // r.right = 1 ∧ (r^2 = 1 ∨ r^2 = killed)} = 40 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_square_one_QH : Nat.card {x : QH // x^2 = 1} = 28 := by
  have hc := QuotientGroup.card_preimage_mk diagonalCenter {x : QH | x^2 = 1}
  have he : QuotientGroup.mk ⁻¹' {x : QH | x^2 = 1} =
      {r : Raw | r^2 = 1 ∨ r^2 = killed} := by
    ext r
    change (projection r)^2 = 1 ↔ _
    rw [← map_pow]
    exact QuotientGroup.eq_one_iff (r^2)
  rw [he] at hc
  change Nat.card {r : Raw // r^2 = 1 ∨ r^2 = killed} =
    Nat.card diagonalCenter * Nat.card {x : QH // x^2 = 1} at hc
  rw [count_raw_square, card_diagonalCenter] at hc
  omega

theorem card_square_one_QK : Nat.card {x : QK // x^2 = 1} = 20 := by
  have hc := QuotientGroup.card_preimage_mk diagonalCenter {x : QH | x ∈ QK ∧ x^2 = 1}
  have he : QuotientGroup.mk ⁻¹' {x : QH | x ∈ QK ∧ x^2 = 1} =
      {r : Raw | r.right = 1 ∧ (r^2 = 1 ∨ r^2 = killed)} := by
    ext r
    change (projection r ∈ QK ∧ (projection r)^2 = 1) ↔ _
    rw [QK_eq_comap_base]
    change (r.right = 1 ∧ (projection r)^2 = 1) ↔ _
    rw [← map_pow]
    exact and_congr_right (fun _ => QuotientGroup.eq_one_iff (r^2))
  let e : {x : QK // x^2 = 1} ≃ {x : QH // x ∈ QK ∧ x^2 = 1} := {
    toFun x := ⟨x.val.val, x.val.property, congrArg (fun y : QK => (y : QH)) x.property⟩
    invFun x := ⟨⟨x.val,x.property.1⟩,Subtype.ext x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [he] at hc
  change Nat.card {r : Raw // r.right = 1 ∧ (r^2 = 1 ∨ r^2 = killed)} =
    Nat.card diagonalCenter * Nat.card {x : QH // x ∈ QK ∧ x^2 = 1} at hc
  rw [count_raw_core_square, card_diagonalCenter, ← Nat.card_congr e] at hc
  omega
end QuaternionSwapModel

namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic

theorem card_square_one_quaternionCore (m : InnerModel) :
    Nat.card {x : quaternionCore // x^2 = 1} = 20 := by
  let e := splitQuaternionCoreEquiv m
  let f := Equiv.subtypeEquiv (p := fun x => x^2 = 1) (q := fun x => x^2 = 1) e.toEquiv (fun x => by
    change x^2 = 1 ↔ (e x)^2 = 1
    rw [← map_pow, ← map_one e]
    exact e.injective.eq_iff.symm)
  rw [← Nat.card_congr f]
  exact QuaternionSwapModel.card_square_one_QK

theorem card_square_one_outerCore (m : InnerModel) :
    Nat.card {x : outerCore // x^2 = 1} = 20 := by
  let e : {x : quaternionCore // x^2 = 1} ≃ {x : outerCore // x^2 = 1} := {
    toFun x := ⟨⟨x.val.val,(show quaternionCore ≤ outerCore from le_sup_left) x.val.property⟩,
      Subtype.ext (congrArg (fun y : quaternionCore => (y : Carrier)) x.property)⟩
    invFun x := ⟨⟨x.val.val,outerCore_square_one_mem_quaternionCore m _ x.val.property
      (congrArg (fun y : outerCore => (y : Carrier)) x.property)⟩,Subtype.ext (congrArg (fun y : outerCore => (y : Carrier)) x.property)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [← Nat.card_congr e, card_square_one_quaternionCore m]

theorem outerCore_not_equiv_split (m : InnerModel) :
    ¬ Nonempty (outerCore ≃* QuaternionSwapModel.QH) := by
  rintro ⟨e⟩
  let f := Equiv.subtypeEquiv (p := fun x => x^2 = 1) (q := fun x => x^2 = 1) e.toEquiv (fun x => by
    change x^2 = 1 ↔ (e x)^2 = 1
    rw [← map_pow, ← map_one e]
    exact e.injective.eq_iff.symm)
  have hc := Nat.card_congr f
  rw [card_square_one_outerCore m, QuaternionSwapModel.card_square_one_QH] at hc
  omega
end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
