module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Theory.GroupTheory.QuotientNormalImage
public import Mathlib.Tactic

/-!
# Uniqueness of the quaternion subgroup of GL₂(3)

Every embedded Q₈ has the same eight matrices: I, -I, and the six
matrices whose square is -I. The order-four assertion and the count are
finite calculations on the 81 two-by-two matrices over ZMod 3, checked
by the kernel. Consequently every quaternion subgroup is normal.

This supplies the uniqueness assertion used in Aschbacher–Smith,
16.4.9(2), printed p.1191. No identification from group order alone or
solvability premise is used.
-/

open Matrix
namespace Matrix.GeneralLinearGroup
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)
private abbrev G := GL (Fin 2) (ZMod 3)

private theorem order_four_square : ∀ A : M, A ^ 4 = 1 → A ^ 2 ≠ 1 → A ^ 2 = -1 := by
  decide +kernel

private def quaternionMatrices : Set M := { A | A = 1 ∨ A = -1 ∨ A ^ 2 = -1 }

private theorem quaternionMatrices_card : Nat.card quaternionMatrices = 8 := by
  change Nat.card { A : M // A = 1 ∨ A = -1 ∨ A ^ 2 = -1 } = 8
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem quaternion_image_mem (f : QuaternionGroup 2 →* G)
    (hf : Function.Injective f) (q : QuaternionGroup 2) :
    (f q).val ∈ quaternionMatrices := by
  have h4 : f (QuaternionGroup.a 1) ^ 4 = 1 := by
    rw [← map_pow]
    have hh : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 := by decide
    rw [hh, map_one]
  have h2 : f (QuaternionGroup.a 1) ^ 2 ≠ 1 := by
    intro he
    have hh : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = 1 :=
      hf (by simpa only [map_pow, map_one] using he)
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1) hh
  have hm : (f (QuaternionGroup.a 1)).val ^ 2 = -1 :=
    order_four_square _ (congrArg Units.val h4)
      (fun he => h2 (Units.ext he))
  have hc : ∀ q : QuaternionGroup 2, q = 1 ∨ q = QuaternionGroup.a 1 ^ 2 ∨
      q ^ 2 = QuaternionGroup.a 1 ^ 2 := by decide
  rcases hc q with rfl | he | he
  · exact Or.inl (congrArg Units.val (map_one f))
  · right; left
    simpa only [he, map_pow, Units.val_pow_eq_pow_val] using hm
  · right; right
    calc
      (f q).val ^ 2 = (f (q ^ 2)).val := (congrArg Units.val (map_pow f q 2)).symm
      _ = (f (QuaternionGroup.a 1)).val ^ 2 := by rw [he, map_pow]; rfl
      _ = -1 := hm

/-- Exact matrix membership in any quaternion subgroup. -/
public theorem three_mem_quaternion_iff (P : Subgroup (GL (Fin 2) (ZMod 3))) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (x : GL (Fin 2) (ZMod 3)) : x ∈ P ↔ x.val = 1 ∨ x.val = -1 ∨ x.val ^ 2 = -1 := by
  classical
  obtain ⟨e⟩ := hP
  let f : QuaternionGroup 2 →* G := P.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.symm.injective
  have hmem (p : P) : p.val.val ∈ quaternionMatrices := by
    have he : f (e p) = p.val := by simp [f]
    have hh := quaternion_image_mem f hf (e p)
    rw [he] at hh
    exact hh
  let j : P → quaternionMatrices := fun p => ⟨p.val.val, hmem p⟩
  have hj : Function.Injective j := by
    intro p q he
    exact Subtype.ext (Units.ext (congrArg Subtype.val he))
  have hcard : Nat.card P = Nat.card quaternionMatrices := by
    rw [quaternionMatrices_card, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  have hs := ((Nat.bijective_iff_injective_and_card j).mpr ⟨hj, hcard⟩).surjective
  constructor
  · intro hx
    exact hmem ⟨x, hx⟩
  · intro hx
    obtain ⟨p, hp⟩ := hs ⟨x.val, hx⟩
    have he : p.val = x := Units.ext (congrArg Subtype.val hp)
    exact he ▸ p.property

/-- Any two actual quaternion subgroups of GL₂(3) coincide. -/
public theorem three_quaternion_subgroup_eq (P Q : Subgroup (GL (Fin 2) (ZMod 3)))
    (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hQ : Nonempty (Q ≃* QuaternionGroup 2)) : P = Q := by
  ext x
  rw [three_mem_quaternion_iff P hP, three_mem_quaternion_iff Q hQ]

/-- The quaternion subgroup is normal in the full general linear group. -/
public theorem three_quaternion_subgroup_normal (P : Subgroup (GL (Fin 2) (ZMod 3)))
    (hP : Nonempty (P ≃* QuaternionGroup 2)) : P.Normal := by
  apply Subgroup.normal_iff_map_conj_eq.mpr
  intro g
  obtain ⟨e⟩ := hP
  exact three_quaternion_subgroup_eq _ P
    ⟨((MulAut.conj g).subgroupMap P).symm.trans e⟩ ⟨e⟩

open Subgroup

variable {H : Type*} [Group H]

/-- A quaternion subgroup modulo F is normal whenever the actual quotient is GL₂(3). -/
public theorem normal_of_three_quotient (F Q : Subgroup H) [F.Normal] (hFQ : F ≤ Q)
    (e : H ⧸ F ≃* GL (Fin 2) (ZMod 3))
    (hQ : Nonempty ((Q ⧸ F.subgroupOf Q) ≃* QuaternionGroup 2)) : Q.Normal := by
  obtain ⟨eQ⟩ := hQ
  let q := QuotientGroup.mk' F
  let f := q.comp Q.subtype
  have hk : f.ker = F.subgroupOf Q := by
    ext x
    simp [f, q, mem_subgroupOf]
  let a : (Q ⧸ F.subgroupOf Q) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hr : f.range = Q.map q := by rw [MonoidHom.range_comp, range_subtype]
  let b : Q.map q ≃* QuaternionGroup 2 :=
    ((MulEquiv.subgroupCongr hr).symm.trans a.symm).trans eQ
  let P := (Q.map q).map e.toMonoidHom
  let c : P ≃* QuaternionGroup 2 := ((e.subgroupMap (Q.map q)).symm).trans b
  let _ : P.Normal := three_quaternion_subgroup_normal P ⟨c⟩
  exact normal_of_faithful_quotient_image F Q hFQ e.toMonoidHom e.injective P rfl


end Matrix.GeneralLinearGroup
