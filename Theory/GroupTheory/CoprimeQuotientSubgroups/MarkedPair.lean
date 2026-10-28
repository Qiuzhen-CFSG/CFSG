module

public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Lifting a marked pair through a coprime kernel

An elementary abelian subgroup contained in a homomorphism's range lifts
isomorphically when the kernel has coprime order. Lifting the join of two
marked subgroups at once then preserves both image subgroups, their orders,
disjointness, and commutation. Their lifted join remains elementary with
the original order.

The construction takes the two inverse images inside the common elementary
lift, where the original map is injective. This supplies the compatible
cubic pair needed by Aschbacher--Smith, 13.5.6, printed p.917.
-/

public section

open Subgroup
namespace Subgroup

private theorem exists_elementary_lift_of_le_range
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H)
    (hker : Nat.Coprime p (Nat.card f.ker))
    (E : Subgroup H) [IsElementaryAbelian p E] (hE : E ≤ f.range) :
    ∃ P : Subgroup G, IsElementaryAbelian p P ∧ P.map f=E ∧ Nat.card P=Nat.card E := by
  let D := E.subgroupOf f.range
  let _ : IsElementaryAbelian p D := IsElementaryAbelian.subgroupOf hE
  have hc : Nat.Coprime p (Nat.card f.rangeRestrict.ker) := by
    simpa only [MonoidHom.ker_rangeRestrict] using hker
  obtain ⟨P,hP,hmap,hcard⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    f.rangeRestrict f.rangeRestrict_surjective hc D
  refine ⟨P,hP,?_,hcard.trans (Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv)⟩
  have hm := congrArg (Subgroup.map f.range.subtype) hmap
  rw [Subgroup.map_map,Subgroup.map_subgroupOf_eq_of_le hE] at hm
  exact hm

private theorem card_map_of_injective_restriction
    {G H : Type*} [Group G] [Group H] (f : G →* H) (P : Subgroup G)
    (hf : Function.Injective (f.comp P.subtype)) : Nat.card (P.map f)=Nat.card P := by
  let e : P ≃* P.map f := MulEquiv.ofBijective (f.subgroupMap P)
    ⟨fun x y h => hf (congrArg Subtype.val h),f.subgroupMap_surjective P⟩
  exact Nat.card_congr e.symm.toEquiv

/-- Two prescribed disjoint subgroups of an elementary image lift together,
with their literal images, commutation, and all orders preserved. -/
theorem exists_elementary_pair_lift
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H)
    (hker : Nat.Coprime p (Nat.card f.ker))
    (A B : Subgroup H) [IsElementaryAbelian p (A⊔B : Subgroup H)]
    (hrange : A⊔B ≤ f.range) (hdis : Disjoint A B) :
    ∃ P Q : Subgroup G,
      P.map f=A ∧ Q.map f=B ∧ Nat.card P=Nat.card A ∧ Nat.card Q=Nat.card B ∧
      Disjoint P Q ∧ (∀ a∈P,∀ b∈Q,Commute a b) ∧
      IsElementaryAbelian p (P⊔Q : Subgroup G) ∧
      Nat.card (P⊔Q : Subgroup G)=Nat.card (A⊔B : Subgroup H) := by
  obtain ⟨E,hE,hmap,hcard⟩ := exists_elementary_lift_of_le_range f hker (A⊔B) hrange
  let _ := hE
  have hi := injective_comp_subtype_of_coprime_ker f hker E (IsElementaryAbelian.isPGroup p E)
  let P := E ⊓ A.comap f
  let Q := E ⊓ B.comap f
  have hPE : P ≤ E := inf_le_left
  have hQE : Q ≤ E := inf_le_left
  have hP : P.map f=A := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro a ha
      obtain ⟨x,hx,hxa⟩ := hmap.symm ▸ (mem_sup_left ha : a ∈ A⊔B)
      exact ⟨x,⟨hx,by change f x∈A;rw [hxa];exact ha⟩,hxa⟩
  have hQ : Q.map f=B := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro b hb
      obtain ⟨x,hx,hxb⟩ := hmap.symm ▸ (mem_sup_right hb : b ∈ A⊔B)
      exact ⟨x,⟨hx,by change f x∈B;rw [hxb];exact hb⟩,hxb⟩
  have hPQ : P⊔Q=E := by
    apply le_antisymm (sup_le hPE hQE)
    intro x hx
    have him : f x ∈ (P⊔Q).map f := by
      rw [Subgroup.map_sup,hP,hQ,← hmap]
      exact mem_map_of_mem f hx
    obtain ⟨y,hy,hyx⟩ := him
    have he : (⟨y,(sup_le hPE hQE) hy⟩ : E)=⟨x,hx⟩ := hi hyx
    have hyx' : y=x := congrArg (fun z : E => (z : G)) he
    rw [← hyx']
    exact hy
  have hc (K : Subgroup G) (hK : K ≤ E) : Nat.card (K.map f)=Nat.card K := by
    apply card_map_of_injective_restriction f K
    intro x y hxy
    have he : (⟨(x : G),hK x.property⟩ : E)=⟨(y : G),hK y.property⟩ := hi hxy
    exact Subtype.ext (congrArg (fun z : E => (z : G)) he)
  refine ⟨P,Q,hP,hQ,(hc P hPE).symm.trans (congrArg (fun K : Subgroup H => Nat.card K) hP),
    (hc Q hQE).symm.trans (congrArg (fun K : Subgroup H => Nat.card K) hQ),?_,?_,?_,?_⟩
  · apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hf1 : f x=1 := hdis.le_bot ⟨hx.1.2,hx.2.2⟩
    have he : (⟨x,hPE hx.1⟩ : E)=1 := by
      apply hi
      change f x=f 1
      rw [map_one]
      exact hf1
    exact mem_bot.mpr (congrArg (fun z : E => (z : G)) he)
  · intro a ha b hb
    change a*b=b*a
    exact congrArg Subtype.val (mul_comm' (⟨a,hPE ha⟩ : E) ⟨b,hQE hb⟩)
  · rw [hPQ]
    exact hE
  · rw [hPQ]
    exact hcard

end Subgroup
