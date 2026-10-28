module
public import Theory.GroupTheory.CyclicFixerDisjointConjugate
/-!
# Equal-size disjoint cyclic kernels make the preimage abelian

A disjoint conjugate of the cyclic kernel embeds in the target. If their
orders agree, this embedding is surjective and the preimage is the product
of the two kernels. Their commutation makes it abelian. The conjugating
element can be external to the preimage.
Source application: Aschbacher--Smith 2.5.15, printed p.559.
-/
public section
namespace Subgroup
variable {G A : Type*} [Group G] [Group A] [Finite A]

theorem centralizes_self_of_disjoint_cyclic_kernel_conjugate
    (C : Subgroup G) (f : C →* A)
    (N : Subgroup G) (hNC : N ≤ C) (hker : f.ker = N.subgroupOf C)
    [IsCyclic N] (hcard : Nat.card N = Nat.card A)
    (x : G) (hx : x ∈ normalizer (C : Set G))
    (hd : Disjoint N (N.conjBy x)) (hcomm : N ≤ centralizer (N.conjBy x : Set G)) :
    C ≤ centralizer (C : Set G) := by
  let W := N.conjBy x
  let e : N ≃* W := N.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
  let : IsCyclic W := isCyclic_of_surjective e.toMonoidHom e.surjective
  have hWC : W ≤ C := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hNC
    have he : C.map (MulAut.conj x).toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp hx
    rw [he] at hh
    exact hh
  let a : W →* A := f.comp (inclusion hWC)
  have hi : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply bot_unique
    intro w hw
    have hfw : inclusion hWC w ∈ f.ker := hw
    rw [hker] at hfw
    exact mem_bot.mpr (Subtype.ext (disjoint_def.mp hd hfw w.property))
  have ha : Function.Surjective a :=
    ((Nat.bijective_iff_injective_and_card a).mpr ⟨hi,(Nat.card_congr e.toEquiv).symm.trans hcard⟩).2
  have hspan : C = N ⊔ W := by
    apply le_antisymm
    · intro c hc
      obtain ⟨w,hw⟩ := ha (f ⟨c,hc⟩)
      have hm : (⟨c,hc⟩ : C) * (inclusion hWC w)⁻¹ ∈ f.ker := by
        change f _ = 1
        rw [map_mul,map_inv,show f (inclusion hWC w) = f ⟨c,hc⟩ from hw,mul_inv_cancel]
      rw [hker] at hm
      have hh := (N ⊔ W).mul_mem (mem_sup_left hm) (mem_sup_right w.property)
      change (c * (w : G)⁻¹) * (w : G) ∈ N ⊔ W at hh
      simpa only [inv_mul_cancel_right] using hh
    · exact sup_le hNC hWC
  rw [hspan]
  apply sup_le
  · exact le_centralizer_iff.mpr (sup_le N.le_centralizer (le_centralizer_iff.mp hcomm))
  · exact le_centralizer_iff.mpr (sup_le hcomm W.le_centralizer)
end Subgroup
