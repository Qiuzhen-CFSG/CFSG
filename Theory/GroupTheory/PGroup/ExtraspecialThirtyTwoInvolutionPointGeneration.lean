module

public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Theory.GroupTheory.FrattiniInvolutionPoints

/-!
# Involution generation for the extraspecial group of order thirty-two

Under the elementary-rank bound, the embedded quaternion and dihedral factors
show that square-one elements generate the group. Reflections generate the
dihedral factor. An element of the quaternion factor with nontrivial square
has the same square as the dihedral rotation, so their commuting product has
square one and recovers that element inside the generated subgroup.

Passing to the Frattini quotient and discarding identity images proves that
its intrinsic involution points generate. This uses neither their cardinality
nor a permutation action.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389.
-/

open Subgroup

namespace IsExtraspecial

/-- Square-one elements generate a rank-two extraspecial group of order thirty-two. -/
public theorem closure_square_eq_one_eq_top_of_card_thirty_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8)
    (hP : Nat.card P = 32) : closure {x : P | x ^ 2 = 1} = ⊤ := by
  obtain ⟨U, V, _, ⟨e⟩, hc, hg, _⟩ :=
    dihedral_quaternion_factors_of_card_thirty_two hrank hP
  let K := closure {x : P | x ^ 2 = 1}
  let f : DihedralGroup 4 →* P := V.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hs (i : ZMod 4) : f (DihedralGroup.sr i) ∈ K := by
    apply Subgroup.subset_closure
    change f (DihedralGroup.sr i) ^ 2 = 1
    rw [← map_pow]
    have hi : (DihedralGroup.sr i) ^ 2 = 1 := by simp [pow_two]
    rw [hi, map_one]
  have hV : V ≤ K := by
    intro v hv
    obtain ⟨d, hd⟩ := e.symm.surjective (⟨v, hv⟩ : V)
    have hd' : f d = v := congrArg Subtype.val hd
    rw [← hd']
    cases d with
    | sr i => exact hs i
    | r i =>
      have he : DihedralGroup.r i = DihedralGroup.sr 0 * DihedralGroup.sr i := by simp
      rw [he, map_mul]
      exact K.mul_mem (hs 0) (hs i)
  let r : P := f (DihedralGroup.r 1)
  have hrV : r ∈ V := (e.symm (DihedralGroup.r 1)).property
  have hrK : r ∈ K := hV hrV
  have hr2 : r ^ 2 ≠ 1 := by
    intro h
    have he : f ((DihedralGroup.r 1) ^ 2) = f 1 := by simpa only [map_pow, map_one] using h
    have hn : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 ≠ 1 := by decide
    exact hn (hf he)
  have hU : U ≤ K := by
    intro x hx
    by_cases hx2 : x ^ 2 = 1
    · exact subset_closure hx2
    have he : x ^ 2 = r ^ 2 := by
      obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp
        (center_order_p 2 P)
      exact congrArg Subtype.val
        ((hz ⟨x ^ 2, square_mem_center x⟩ (fun h => hx2 (congrArg Subtype.val h))).trans
          (hz ⟨r ^ 2, square_mem_center r⟩ (fun h => hr2 (congrArg Subtype.val h))).symm)
    have hcomm : Commute x r := hc hrV x hx
    have hxr : x * r ∈ K := by
      apply Subgroup.subset_closure
      change (x * r) ^ 2 = 1
      rw [hcomm.mul_pow, he, ← pow_add]
      exact pow_four_eq_one r
    simpa only [mul_inv_cancel_right] using K.mul_mem hxr (K.inv_mem hrK)
  apply top_unique
  rw [← hg]
  exact sup_le hU hV

/-- The intrinsic involution points generate the Frattini quotient of a rank-two
extraspecial group of order thirty-two. -/
public theorem closure_frattiniInvolutionPoints_eq_top_of_card_thirty_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8)
    (hP : Nat.card P = 32) : closure (frattiniInvolutionPoints P) = ⊤ := by
  let q := QuotientGroup.mk' (frattini P)
  let H := closure (frattiniInvolutionPoints P)
  have hle : closure {x : P | x ^ 2 = 1} ≤ H.comap q := by
    apply (closure_le _).mpr
    intro x hx
    change q x ∈ H
    by_cases hq : q x = 1
    · rw [hq]
      exact H.one_mem
    · exact subset_closure ((mem_frattiniInvolutionPoints _).mpr ⟨hq, x, hx, rfl⟩)
  rw [closure_square_eq_one_eq_top_of_card_thirty_two hrank hP] at hle
  apply top_unique
  intro v _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) v
  exact hle (mem_top x)

end IsExtraspecial
