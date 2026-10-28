module
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# Normalizer images with the kernel inside the local Sylow

If the action kernel in K join B lies in B, an element of K normalizes B
exactly when its image normalizes the image of B. An embedded rank-one
normalizer, alone or on a direct-product axis, therefore contributes its
whole order to the original K-normalizer intersection. No central cover
is split. Source application: Aschbacher--Smith 10.2.3(4), pp.746--747.
-/
public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]
theorem map_inf_normalizer_of_kernel_le_join
    (q : G →* H) (K B : Subgroup G)
    (hk : q.ker ⊓ (K ⊔ B) ≤ B) :
    (K ⊓ normalizer (B : Set G)).map q =
      K.map q ⊓ normalizer (B.map q : Set H) := by
  apply le_antisymm
  · exact le_inf (map_mono inf_le_left)
      ((map_mono inf_le_right).trans (B.le_normalizer_map q))
  · rintro x ⟨⟨k,hkK,rfl⟩,hkN⟩
    refine ⟨k,⟨hkK,?_⟩,rfl⟩
    have forward (g : G) (hgK : g ∈ K)
        (hgN : q g ∈ normalizer (B.map q : Set H)) :
        ∀ b ∈ B, g*b*g⁻¹ ∈ B := by
      intro b hb
      have hm : q (g*b*g⁻¹) ∈ B.map q := by
        rw [map_mul,map_mul,map_inv]
        exact (mem_normalizer_iff.mp hgN (q b)).mp (mem_map_of_mem q hb)
      obtain ⟨c,hc,he⟩ := hm
      have hker : g*b*g⁻¹*c⁻¹ ∈ q.ker := by
        rw [MonoidHom.mem_ker,map_mul,map_inv,←he,mul_inv_cancel]
      have hjoin : g*b*g⁻¹*c⁻¹ ∈ K ⊔ B := by
        exact (K ⊔ B).mul_mem ((K ⊔ B).mul_mem
          ((K ⊔ B).mul_mem ((show K ≤ K ⊔ B from le_sup_left) hgK)
            ((show B ≤ K ⊔ B from le_sup_right) hb))
          ((show K ≤ K ⊔ B from le_sup_left) (K.inv_mem hgK)))
          ((show B ≤ K ⊔ B from le_sup_right) (B.inv_mem hc))
      have hh := B.mul_mem (hk ⟨hker,hjoin⟩) hc
      simpa only [inv_mul_cancel_right] using hh
    apply mem_normalizer_iff.mpr
    intro b
    constructor
    · exact forward k hkK hkN b
    · intro hb
      have hgN : q k⁻¹ ∈ normalizer (B.map q : Set H) := by
        rw [map_inv]
        exact (normalizer (B.map q : Set H)).inv_mem hkN
      have hh := forward k⁻¹ (K.inv_mem hkK) hgN (k*b*k⁻¹) hb
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
end Subgroup
namespace Subgroup
variable {G H A D : Type*} [Group G] [Group H] [Group A] [Group D]


theorem first_axis_normalizer_card_dvd
    (q : G →* H) (K B : Subgroup G)
    (hk : q.ker ⊓ (K ⊔ B) ≤ B)
    (j : A × D →* H) (hj : Function.Injective j)
    (P : Subgroup A) (Q : Subgroup D)
    (hK : K.map q = ((⊤ : Subgroup A).prod ⊥).map j)
    (hB : B.map q = (P.prod Q).map j) :
    Nat.card (normalizer (P : Set A)) ∣ Nat.card (K ⊓ normalizer (B : Set G) : Subgroup G) := by
  let I := K.map q ⊓ normalizer (B.map q : Set H)
  let f : normalizer (P : Set A) →* H := j.comp ((MonoidHom.inl A D).comp (normalizer (P : Set A)).subtype)
  have hf (a : normalizer (P : Set A)) : f a ∈ I := by
    constructor
    · rw [hK]
      exact ⟨(a,1),⟨mem_top _,mem_bot.mpr rfl⟩,rfl⟩
    · rw [hB]
      apply (P.prod Q).le_normalizer_map j
      refine ⟨(a,1),?_,rfl⟩
      apply mem_normalizer_iff.mpr
      rintro ⟨x,y⟩
      change (x ∈ P ∧ y ∈ Q) ↔
        ((a:A)*x*(a:A)⁻¹ ∈ P ∧ (1:D)*y*1⁻¹ ∈ Q)
      simpa only [one_mul,mul_one,inv_one] using
        (mem_normalizer_iff.mp a.property x).and (Iff.rfl : y ∈ Q ↔ y ∈ Q)
  let g := f.codRestrict I hf
  have hg : Function.Injective g := by
    intro a b he
    have hh := hj (congrArg Subtype.val he)
    exact Subtype.ext (congrArg Prod.fst hh)
  have hd := card_dvd_of_injective g hg
  have hi : I = (K ⊓ normalizer (B : Set G)).map q :=
    (map_inf_normalizer_of_kernel_le_join q K B hk).symm
  rw [hi] at hd
  exact hd.trans (card_map_dvd _ q)

theorem marked_normalizer_card_dvd
    (q : G →* H) (K B : Subgroup G)
    (hk : q.ker ⊓ (K ⊔ B) ≤ B)
    (j : A →* H) (hj : Function.Injective j)
    (P : Subgroup A)
    (hK : K.map q = (⊤ : Subgroup A).map j)
    (hB : B.map q = P.map j) :
    Nat.card (normalizer (P : Set A)) ∣ Nat.card (K ⊓ normalizer (B : Set G) : Subgroup G) := by
  let I := K.map q ⊓ normalizer (B.map q : Set H)
  let f := j.comp (normalizer (P : Set A)).subtype
  have hf (a : normalizer (P : Set A)) : f a ∈ I := by
    constructor
    · rw [hK]
      exact mem_map_of_mem j (mem_top _)
    · rw [hB]
      exact P.le_normalizer_map j (mem_map_of_mem j a.property)
  let g := f.codRestrict I hf
  have hg : Function.Injective g := by
    intro a b he
    exact Subtype.ext (hj (congrArg Subtype.val he))
  have hd := card_dvd_of_injective g hg
  have hi : I = (K ⊓ normalizer (B : Set G)).map q :=
    (map_inf_normalizer_of_kernel_le_join q K B hk).symm
  rw [hi] at hd
  exact hd.trans (card_map_dvd _ q)
end Subgroup
