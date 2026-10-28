module
public import Theory.GroupTheory.CyclicSylowCenterNormalIntersection
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Quotient transfer for a cyclic Sylow center

The image of a normal subgroup disjoint from an odd normal kernel is controlled
by the image of a cyclic Sylow center whenever it lies in the kernel-plus-center
join.  The quotient image is a 2-group, and disjointness makes the quotient map
injective on the subgroup; normality then places it in the chosen Sylow
2-subgroup.  This is the Theory-layer transfer used in the ABG normal-kernel
reduction, avoiding any assumption that the odd kernel itself is a 2-group.
-/

namespace Subgroup

public theorem cyclic_sylow_center_normal_kernel_image_transfer
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (N K : Subgroup G) [N.Normal] [K.Normal]
    (_hN : Nat.Coprime 2 (Nat.card N))
    (_hZ : IsCyclic (center S))
    (hK : K ≤ N ⊔ (center S).map (S : Subgroup G).subtype)
    (hKN : Disjoint K N) :
    let q : G →* (G ⧸ N) := QuotientGroup.mk' N
    IsPGroup 2 (K.map q) ∧ K.map q ≤ ((center S).map (S : Subgroup G).subtype).map q ∧
      K ≤ (S : Subgroup G) := by
  let q : G →* (G ⧸ N) := QuotientGroup.mk' N
  have hNbot : N.map q = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn, rfl⟩ := hx
      change q n = 1
      exact (QuotientGroup.eq_one_iff n).2 hn
    · exact bot_le
  let C : Subgroup G := (center S).map (S : Subgroup G).subtype
  have hcenterP : IsPGroup 2 (C.map q) :=
    IsPGroup.map (IsPGroup.map (S.isPGroup'.to_subgroup (center S)) (S : Subgroup G).subtype) q
  have himage : K.map q ≤ C.map q := by
    calc
      K.map q ≤ (N ⊔ C).map q := Subgroup.map_mono hK
      _ = N.map q ⊔ C.map q := Subgroup.map_sup _ _ q
      _ = ⊥ ⊔ C.map q := by rw [hNbot]
      _ ≤ C.map q := sup_le bot_le le_rfl
  have hqK : Function.Injective (q.comp K.subtype) := by
    intro x y hxy
    have hxy' : (x : G) * (y : G)⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change q ((x : G) * (y : G)⁻¹) = 1
      change q (x : G) * (q (y : G))⁻¹ = 1
      rw [show q (x : G) = q (y : G) from hxy, mul_inv_cancel]
    have hmem : (x : G) * (y : G)⁻¹ ∈ K :=
      K.mul_mem x.property (K.inv_mem y.property)
    have hbot : (x : G) * (y : G)⁻¹ = 1 := by
      have : (x : G) * (y : G)⁻¹ ∈ K ⊓ N := ⟨hmem, hxy'⟩
      rw [disjoint_iff.mp hKN, Subgroup.mem_bot] at this
      exact this
    exact Subtype.ext (mul_inv_eq_one.mp hbot)
  let i : K.map q →* C.map q := (K.map q).subtype.codRestrict (C.map q) (by
    intro x
    exact himage x.property)
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : C.map q => (z : G ⧸ N)) hxy
  have himageP : IsPGroup 2 (K.map q) := IsPGroup.of_injective hcenterP i hi
  let r : K →* K.map q := (q.comp K.subtype).codRestrict (K.map q) (by
    intro x
    exact ⟨x, x.property, rfl⟩)
  have hr : Function.Injective r := by
    intro x y hxy
    apply Subtype.ext
    have hqxy : (q.comp K.subtype) x = (q.comp K.subtype) y :=
      congrArg (fun z : K.map q => (z : G ⧸ N)) hxy
    exact congrArg Subtype.val (hqK hqxy)
  have hKp : IsPGroup 2 K := IsPGroup.of_injective himageP r hr
  have hKS : K ≤ (S : Subgroup G) := hKp.le_sylow_of_normal S
  exact ⟨himageP, himage, hKS⟩

end Subgroup

#print axioms Subgroup.cyclic_sylow_center_normal_kernel_image_transfer
