module
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.PGroup

/-!
# Lifting odd subgroups through two-group kernels

A surjective homomorphism of finite groups with two-group kernel lifts
any odd-order subgroup injectively. The lift has the same cardinality,
its image is exactly the specified subgroup, and together with the kernel
it generates precisely the subgroup's full inverse image.

Restrict the original homomorphism to that inverse image. Its kernel
has two-power order and index equal to the odd subgroup's order, so
Schur–Zassenhaus supplies a complement. Mapping the complement into the
original group retains both its exact image and injectivity.

This standard lifting step is used for the order-three actor D* in
Stellmacher (9.1), Journal of Algebra190 (1997), p.48. The theorem has no
campaign-specific assumptions and retains the supplied homomorphism.
-/
namespace MonoidHom
open Subgroup
public theorem exists_odd_subgroup_lift
    {P X : Type*} [Group P] [Finite P] [Group X] [Finite X]
    (f : P →* X) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    (Dbar : Subgroup X) (hodd : Odd (Nat.card Dbar)) :
    ∃ D : Subgroup P, D.map f = Dbar ∧ Function.Injective (f.comp D.subtype) ∧
      Nat.card D = Nat.card Dbar ∧ f.ker ⊔ D = Dbar.comap f := by
  let L := Dbar.comap f
  let g : L →* Dbar := (f.comp L.subtype).codRestrict Dbar (fun x => x.property)
  have hg : Function.Surjective g := by
    intro d
    obtain ⟨p,hp⟩ := hf d
    exact ⟨⟨p, show f p ∈ Dbar from hp ▸ d.property⟩, Subtype.ext hp⟩
  have hker_eq : g.ker = f.ker.subgroupOf L := by
    ext x
    change g x = 1 ↔ f x = 1
    exact Subtype.ext_iff
  have hpg : IsPGroup 2 g.ker := hker_eq ▸ hker.comap_subtype
  have hindex : g.ker.index = Nat.card Dbar := by
    rw [index_ker, range_eq_top.mpr hg, card_top]
  have hcop : Nat.Coprime (Nat.card g.ker) g.ker.index := by
    obtain ⟨n,hn⟩ := hpg.exists_card_eq
    rw [hn, hindex]
    exact hodd.coprime_two_left.pow_left n
  obtain ⟨D0,hD0⟩ := exists_right_complement'_of_coprime hcop
  let D := D0.map L.subtype
  have hmap : D.map f = Dbar := by
    apply le_antisymm
    · rintro _ ⟨d, ⟨d0, hd0, rfl⟩, rfl⟩
      exact d0.property
    · intro d hd
      obtain ⟨p,hp⟩ := hg ⟨d,hd⟩
      obtain ⟨⟨k,d0⟩,hk⟩ := hD0.2 p
      have hh := congrArg g hk
      rw [map_mul, show g k = 1 from mem_ker.mp k.property, one_mul] at hh
      exact ⟨d0, mem_map_of_mem L.subtype d0.property,
        (congrArg Subtype.val hh).trans (congrArg Subtype.val hp)⟩
  have hinj : Function.Injective (f.comp D.subtype) := by
    apply (ker_eq_bot_iff _).mp
    rw [eq_bot_iff_forall]
    intro d hd
    obtain ⟨d0,hd0,heq⟩ := d.property
    have hk : d0 ∈ g.ker := by
      apply mem_ker.mpr
      apply Subtype.ext
      change f d0 = 1
      change (d0 : P) = (d : P) at heq
      rw [heq]
      exact mem_ker.mp hd
    have hdone : d0 = 1 := disjoint_def.mp hD0.disjoint hk hd0
    apply Subtype.ext
    rw [← heq, hdone]
    rfl
  have hcard : Nat.card D = Nat.card Dbar := by
    rw [card_map_of_injective L.subtype_injective, ← hD0.symm.index_eq_card, hindex]
  have hkerL : f.ker ≤ L := by
    intro p hp
    change f p ∈ Dbar
    rw [mem_ker.mp hp]
    exact Dbar.one_mem
  have hcover : f.ker ⊔ D = L := by
    have hh := congrArg (Subgroup.map L.subtype) hD0.sup_eq_top
    rw [Subgroup.map_sup, hker_eq, map_subgroupOf_eq_of_le hkerL,
      ← range_eq_map, range_subtype] at hh
    exact hh
  exact ⟨D, hmap, hinj, hcard, hcover⟩
end MonoidHom
