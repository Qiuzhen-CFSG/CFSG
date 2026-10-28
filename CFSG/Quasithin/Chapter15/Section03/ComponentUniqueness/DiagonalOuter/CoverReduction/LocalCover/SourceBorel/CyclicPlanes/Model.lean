module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import Theory.GroupTheory.WreathTwoSylowModel
public import Theory.GroupTheory.PPerfectHom
public import Theory.PGroupCore

/-!
# Cyclic actors in the natural orthogonal wreath product

A two-perfect image lies in the order-nine base subgroup. Its two-core
therefore acts trivially, so an order-three two-core quotient has image of
order dividing three. A nontrivial cyclic image normalized by the base part
of a Sylow two-subgroup occupies one coordinate axis: conjugation by a
single-coordinate transvection excludes either diagonal. Sylow conjugacy
preserves the two original axes, possibly interchanging them. The same
conjugacy supplies an element of the specified Sylow which swaps the axes.

The cube subgroup calculation follows the checked finite-matrix argument in
`Theory/GroupTheory/WreathTwoOddInverter.lean`; the Sylow embedding is the
existing `wreathTwoDihedralHom`. All finite checks use kernel reduction.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
pp.1121--1122 and the first paragraph of p.1136.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.CyclicModel

private instance : DecidableEq OrthogonalActor := fun a b => decidable_of_iff
  (a.left = b.left ∧ a.right = b.right) RegularWreathProduct.ext_iff.symm
private instance : Fintype OrthogonalActor := Fintype.ofEquiv
  ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
  (RegularWreathProduct.equivProd _ _).symm

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem cube_mul : ∀ a b : OrthogonalPlaneActor,
    a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by decide +kernel

def cubeBase : Subgroup OrthogonalActor where
  carrier a := a.right = 1 ∧ ∀ i, (a.left i) ^ 3 = 1
  one_mem' := ⟨rfl, by intro i; simp⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨by simp [ha.1, hb.1], fun i => cube_mul _ _ (ha.2 i) (hb.2 _)⟩
  inv_mem' := by
    intro a ha
    refine ⟨by simp [ha.1], fun i => ?_⟩
    simpa only [RegularWreathProduct.inv_left, Pi.inv_apply, inv_pow, inv_one]
      using congrArg Inv.inv (ha.2 (a.right * i))

instance : cubeBase.Normal where
  conj_mem a ha g := by
    refine ⟨by simp [ha.1], fun i => ?_⟩
    have he : (g * a * g⁻¹).left i =
        g.left i * a.left (g.right⁻¹ * i) * (g.left i)⁻¹ := by simp [ha.1]
    rw [he, conj_pow, ha.2]
    simp

private theorem cubeBase_card : Nat.card cubeBase = 9 := by
  let e : cubeBase ≃ (OrthogonalPlaneIndex → {a : OrthogonalPlaneActor // a ^ 3 = 1}) := {
    toFun := fun a i => ⟨a.val.left i, a.property.2 i⟩
    invFun := fun f => ⟨⟨fun i => (f i).val, 1⟩, rfl, fun i => (f i).property⟩
    left_inv := fun a => Subtype.ext (RegularWreathProduct.ext rfl a.property.1.symm)
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_fun]
  have hc : Nat.card {a : OrthogonalPlaneActor // a ^ 3 = 1} = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hc]
  norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]

private theorem wreath_card : Nat.card OrthogonalActor = 72 := by
  rw [RegularWreathProduct.card]
  have hc : Nat.card OrthogonalPlaneActor = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hc]
  norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]

private theorem cubeBase_quotient_two : IsPGroup 2 (OrthogonalActor ⧸ cubeBase) := by
  apply IsPGroup.of_card (n := 3)
  have hc := card_eq_card_quotient_mul_card_subgroup cubeBase
  rw [cubeBase_card, wreath_card] at hc
  omega

theorem range_le_cubeBase {A : Type*} [Group A] (f : A →* OrthogonalActor)
    (hA : IsPPerfect 2 A) : f.range ≤ cubeBase := by
  have he := hA.hom_eq_one_of_isPGroup cubeBase_quotient_two
    ((QuotientGroup.mk' cubeBase).comp f)
  rintro _ ⟨a, rfl⟩
  exact (QuotientGroup.eq_one_iff (f a)).mp (DFunLike.congr_fun he a)

private theorem core_le_ker {A : Type*} [Group A] (f : A →* OrthogonalActor)
    (hA : IsPPerfect 2 A) : pCore 2 A ≤ f.ker := by
  have hd := IsPGroup.disjoint_of_coprime (pCore_isPGroup.map f)
    (IsPGroup.of_card (p := 3) (n := 2) cubeBase_card) (by decide : Nat.Coprime 2 3)
  intro a ha
  exact Subgroup.disjoint_def.mp hd ⟨a, ha, rfl⟩ (range_le_cubeBase f hA ⟨a, rfl⟩)

theorem range_card_dvd_three {A : Type*} [Group A] [Finite A]
    (f : A →* OrthogonalActor) (hA : IsPPerfect 2 A)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) : Nat.card f.range ∣ 3 := by
  let q := QuotientGroup.lift (pCore 2 A) f (core_le_ker f hA)
  have hr : q.range = f.range := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) a
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 A) a, rfl⟩
  rw [← hr, ← hc]
  exact card_range_dvd q


private def flip : OrthogonalActor := wreathTwoDihedralHom (.sr 1)

private theorem flip_right : flip.right = 1 := by decide +kernel

private theorem flip_axis : ∀ a : OrthogonalActor, a ∈ cubeBase →
    (flip * a * flip⁻¹ = 1 ∨ flip * a * flip⁻¹ = a ∨ flip * a * flip⁻¹ = a ^ 2) →
    a.left 1 = 1 ∨ a.left (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  change ∀ a : OrthogonalActor,
    (a.right = 1 ∧ ∀ i, (a.left i) ^ 3 = 1) →
    (flip * a * flip⁻¹ = 1 ∨ flip * a * flip⁻¹ = a ∨ flip * a * flip⁻¹ = a ^ 2) →
    a.left 1 = 1 ∨ a.left (Multiplicative.ofAdd (1 : ZMod 2)) = 1
  decide +kernel

private theorem axis_of_flip (H : Subgroup OrthogonalActor) (hH : H ≤ cubeBase)
    (hc : Nat.card H = 3) (hf : flip ∈ normalizer (H : Set OrthogonalActor)) :
    ∃ i : OrthogonalPlaneIndex, ∀ x ∈ H, x.left i = 1 := by
  classical
  let _ := isCyclic_of_prime_card hc
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := H)
  have hpow (x : H) : (x : OrthogonalActor) = 1 ∨
      (x : OrthogonalActor) = a ∨ (x : OrthogonalActor) = (a : OrthogonalActor) ^ 2 := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (ha x)
    have he := (zpow_mod_natCard a k).trans hk
    rw [hc] at he
    change a ^ (k % 3 : ℤ) = x at he
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with hk3 | hk3 | hk3
    · left
      simpa only [hk3, zpow_zero, OneMemClass.coe_one] using congrArg Subtype.val he.symm
    · right; left
      simpa only [hk3, zpow_one] using congrArg Subtype.val he.symm
    · right; right
      simpa only [hk3, zpow_ofNat, Subgroup.coe_pow] using congrArg Subtype.val he.symm
  have hfa : flip * (a : OrthogonalActor) * flip⁻¹ ∈ H :=
    (mem_normalizer_iff.mp hf _).mp a.property
  rcases flip_axis a (hH a.property) (hpow ⟨_, hfa⟩) with h0 | h1
  · refine ⟨1, fun x hx => ?_⟩
    have hh := hpow ⟨x, hx⟩
    change x = 1 ∨ x = a ∨ x = (a : OrthogonalActor) ^ 2 at hh
    rcases hh with rfl | rfl | rfl <;> simp [pow_two, (hH a.property).1, h0]
  · refine ⟨Multiplicative.ofAdd (1 : ZMod 2), fun x hx => ?_⟩
    have hh := hpow ⟨x, hx⟩
    change x = 1 ∨ x = a ∨ x = (a : OrthogonalActor) ^ 2 at hh
    rcases hh with rfl | rfl | rfl <;> simp [pow_two, (hH a.property).1, h1]

/-- A cyclic three-subgroup invariant under the base part of a Sylow two-subgroup
is supported on a single original coordinate. -/
theorem axis_of_sylow_normalized (P : Sylow 2 OrthogonalActor)
    (H : Subgroup OrthogonalActor) (hH : H ≤ cubeBase) (hc : Nat.card H = 3)
    (hn : ∀ s ∈ (P : Subgroup OrthogonalActor), s.right = 1 →
      s ∈ normalizer (H : Set OrthogonalActor)) :
    ∃ i : OrthogonalPlaneIndex, ∀ x ∈ H, x.left i = 1 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq OrthogonalActor wreathTwoSylow P
  have hmap : (wreathTwoSylow : Subgroup OrthogonalActor).map
      (MulAut.conj g).toMonoidHom = P :=
    congrArg (fun Q : Sylow 2 OrthogonalActor => (Q : Subgroup OrthogonalActor)) hg
  have hfP : g * flip * g⁻¹ ∈ (P : Subgroup OrthogonalActor) := by
    rw [← hmap]
    refine ⟨flip, ?_, rfl⟩
    rw [wreathTwoSylow_coe]
    exact ⟨.sr 1, rfl⟩
  have hfH := hn _ hfP (by simp [flip_right])
  let H' := H.map (MulAut.conj g⁻¹).toMonoidHom
  have hH' : H' ≤ cubeBase := by
    rintro _ ⟨x, hx, rfl⟩
    exact (inferInstance : cubeBase.Normal).conj_mem _ (hH hx) g⁻¹
  have hc' : Nat.card H' = 3 := by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hc]
  have hfH' : flip ∈ normalizer (H' : Set OrthogonalActor) := by
    apply le_normalizer_map (H := H) (MulAut.conj g⁻¹).toMonoidHom
    refine ⟨g * flip * g⁻¹, hfH, ?_⟩
    simp [mul_assoc]
  obtain ⟨i, hi⟩ := axis_of_flip H' hH' hc' hfH'
  refine ⟨g.right * i, fun x hx => ?_⟩
  have he := hi ((MulAut.conj g⁻¹) x) ⟨x, hx, rfl⟩
  have he' : (g⁻¹).left i * x.left (g.right * i) * ((g⁻¹).left i)⁻¹ = 1 := by
    simpa [MulAut.conj_apply, (hH hx).1] using he
  exact (MulAut.conj ((g⁻¹).left i)).map_eq_one_iff.mp he'

/-- The actual Sylow image contains an element interchanging the coordinates. -/
theorem exists_shift (P : Sylow 2 OrthogonalActor) :
    ∃ t ∈ (P : Subgroup OrthogonalActor), t.right ≠ 1 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq OrthogonalActor wreathTwoSylow P
  have hmap : (wreathTwoSylow : Subgroup OrthogonalActor).map
      (MulAut.conj g).toMonoidHom = P :=
    congrArg (fun Q : Sylow 2 OrthogonalActor => (Q : Subgroup OrthogonalActor)) hg
  let t := wreathTwoDihedralHom (.sr 0)
  have ht : t.right = Multiplicative.ofAdd (1 : ZMod 2) := by decide +kernel
  refine ⟨g * t * g⁻¹, ?_, ?_⟩
  · rw [← hmap]
    refine ⟨t, ?_, rfl⟩
    rw [wreathTwoSylow_coe]
    exact ⟨.sr 0, rfl⟩
  · simp [ht, mul_comm]

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.CyclicModel
