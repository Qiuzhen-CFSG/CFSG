module
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Involutory inner actions at a Sylow center of order at most two

An involutory inner automorphism of a centerless finite group, fixing a
Sylow two-subgroup pointwise, is conjugation by an involution in its center.
Every automorphism preserving that Sylow subgroup fixes this element when
the center has at most two elements. This supplies the common fixed-hexad
and fixed-heptad choice in the original M₂₂ and M₂₃ E.6.8 exclusions.
-/

public section
open Subgroup
namespace Theory.GroupAction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_inner_involution_in_sylow_center (hZ : center G = ⊥) (S : Sylow 2 G)
    (a : MulAut G) (ho : orderOf a = 2) (hi : a ∈ (MulAut.conj (G := G)).range)
    (hfix : ∀ x ∈ (S : Subgroup G), a x = x) :
    ∃ t : G, orderOf t = 2 ∧ MulAut.conj t = a ∧
      t ∈ (center S).map (S : Subgroup G).subtype := by
  obtain ⟨t,rfl⟩ := hi
  have ht : orderOf t = 2 :=
    (orderOf_injective (MulAut.conj (G := G)) (MulAut.conj_injective_of_center_eq_bot hZ) t).symm.trans ho
  have hc : t ∈ centralizer (S : Set G) := by
    intro x hx
    exact (mul_inv_eq_iff_eq_mul.mp (hfix x hx)).symm
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ht,pow_one])
  have hmem : t ∈ (S : Subgroup G) :=
    ((hp.inf_normalizer_sylow S).le ⟨mem_zpowers t,centralizer_le_normalizer _ hc⟩).2
  refine ⟨t,ht,rfl,⟨⟨t,hmem⟩,?_,rfl⟩⟩
  exact mem_center_iff.mpr (fun x => Subtype.ext (hc x x.property))

theorem fixes_small_sylow_center (S : Sylow 2 G) (hS : Nat.card (center S) ≤ 2)
    (t : G) (ht : t ∈ (center S).map (S : Subgroup G).subtype)
    (a : MulAut G) (ha : (S : Subgroup G).map a.toMonoidHom = S) : a t = t := by
  let e : MulAut S := (a.subgroupMap (S : Subgroup G)).trans (MulEquiv.subgroupCongr ha)
  let c : MulAut (center S) := centerCongr e
  have hc : c = 1 := by
    by_cases hone : Nat.card (center S) ≤ 1
    · let _ := Finite.card_le_one_iff_subsingleton.mp hone
      apply MulEquiv.ext
      intro x
      exact Subsingleton.elim _ _
    · have htwo : Nat.card (center S) = 2 := by omega
      obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : center S)).mp htwo
      apply MulEquiv.ext
      intro w
      change c w = w
      by_cases hw : w = 1
      · simpa only [hw] using c.map_one
      · have hn : c w ≠ 1 := fun he => hw (c.injective (he.trans c.map_one.symm))
        exact (hz _ hn).trans (hz _ hw).symm
  obtain ⟨x,hx,rfl⟩ := ht
  exact congrArg (fun y : center S => ((y : S) : G)) (DFunLike.congr_fun hc ⟨x,hx⟩)
end Theory.GroupAction
