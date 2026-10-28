module

public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic

/-!
# Cubic automorphisms of groups of order four

A nontrivial cubic automorphism has no nonidentity fixed point: a point
stabilizer in the automorphism group has order at most two. A nontrivial
invariant subgroup consequently contains three distinct elements, so its
order divides four and exceeds two, forcing it to be the whole group.

For an elementary abelian four-group this is irreducibility over F₂.
The covering-kernel application is the multiplier argument in
Aschbacher--Smith, I.2.2(7a), printed p.412, `refs/quasithin.pdf`.
-/

namespace Theory.GroupAction.CardFourCubic

open Subgroup

/-- A nontrivial cubic automorphism of a group of order four is fixed-point-free
away from the identity. -/
public theorem moves_nonidentity {W : Type*} [Group W] [Finite W]
    (hW : Nat.card W = 4) (a : MulAut W) (ha : a ^ 3 = 1) (hne : a ≠ 1)
    (w : W) (hw : w ≠ 1) : a w ≠ w := by
  intro hfix
  have hR : Nat.card (zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha hne]
  have hbound := card_mulAut_subgroup_le_two_of_fixed_point hW w hw (zpowers a)
    (fun b hb => smul_eq_self_of_mem_zpowers hb hfix)
  omega

/-- Every subgroup invariant under a nontrivial cubic automorphism is trivial
or the whole group. Only forward invariance is needed. -/
public theorem invariant_subgroup {W : Type*} [Group W] [Finite W]
    (hW : Nat.card W = 4) (a : MulAut W) (ha : a ^ 3 = 1) (hne : a ≠ 1)
    (H : Subgroup W) (hH : ∀ x ∈ H, a x ∈ H) : H = ⊥ ∨ H = ⊤ := by
  classical
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hw' : (w : W) ≠ 1 := fun he => hw (Subtype.ext he)
  let v : H := ⟨a w, hH w w.property⟩
  have hv : v ≠ 1 := by
    intro he
    have hval := congrArg Subtype.val he
    exact hw' (a.injective (hval.trans (map_one a).symm))
  have hwv : w ≠ v := by
    intro he
    exact moves_nonidentity hW a ha hne w hw' (congrArg Subtype.val he).symm
  let := Fintype.ofFinite H
  have hgt : 2 < Nat.card H := by
    rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
    exact ⟨1, w, v, hw.symm, hv.symm, hwv⟩
  have hd : Nat.card H ∣ 4 := hW ▸ H.card_subgroup_dvd_card
  have he : Nat.card H = 4 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases h : Nat.card H <;> norm_num at *
  exact H.eq_top_of_card_eq (he.trans hW.symm)

/-- Such an action admits no nontrivial invariant homomorphism to a group of
order at most two, as needed for a central double cover. -/
public theorem invariant_hom_eq_one {W T : Type*} [Group W] [Finite W]
    [Group T] [Finite T] (hW : Nat.card W = 4) (hT : Nat.card T ≤ 2)
    (a : MulAut W) (ha : a ^ 3 = 1) (hne : a ≠ 1)
    (f : W →* T) (hf : ∀ x, f (a x) = f x) : f = 1 := by
  rcases invariant_subgroup hW a ha hne f.ker
      (fun x hx => (hf x).trans hx) with hbot | htop
  · have hinj := (MonoidHom.ker_eq_bot_iff f).mp hbot
    have hle := Nat.card_le_card_of_injective f hinj
    omega
  · exact MonoidHom.ker_eq_top_iff.mp htop

end Theory.GroupAction.CardFourCubic
