module

import Mathlib.Algebra.Field.ZMod
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore
public import Theory.GroupTheory.CharacteristicSelfCentralizingAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The outer group of the M23 heptad stabilizer is a two-group

Write H for the actual heptad stabilizer and V for its pointwise kernel.
The quotient H/V is A7, so the normal E16 subgroup V is exactly O₂(H).
It is characteristic and self-centralizing. Thus the kernel of
Aut(H) → Aut(V) is a two-group. The image of Inn(H) on V has order 2520,
whereas Aut(V) is GL₄(2) of order 20160. Its index eight forces the
remaining part of Out(H) to be a two-group as well.

The binary coordinates, alternating section and centralizer condition come
from the concrete Witt-design model. No premise on abstract automorphisms
of M23 or of H is assumed. This is the local restriction step for GLS3,
Table 5.3d (Out(M23) = 1); the weaker two-group conclusion suffices for the
outer-group inspection in Aschbacher–Smith, printed p.510.
-/

open Subgroup
namespace Sporadic.Mathieu.M23Geometry.OuterRestriction

private theorem kernel_eq_core : heptadKernel = pCore 2 heptadStabilizer := by
  have hk : heptadKernel ≤ pCore 2 heptadStabilizer :=
    le_sSup ⟨inferInstance, heptadKernel_isTwoGroup⟩
  apply le_antisymm hk
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let f := heptadAlternatingAction
  have hf : Function.Surjective f := fun a => ⟨AlternatingSection.s a,
    heptadAlternatingAction_section a⟩
  have hn : ((pCore 2 heptadStabilizer).map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  have hp : IsPGroup 2 ((pCore 2 heptadStabilizer).map f) := pCore_isPGroup.map f
  have hb : (pCore 2 heptadStabilizer).map f = ⊥ := by
    rcases hn.eq_bot_or_eq_top with h | h
    · exact h
    · have htwo : IsPGroup 2 (alternatingGroup (Fin 7)) :=
        (h ▸ hp).of_surjective (⊤ : Subgroup (alternatingGroup (Fin 7))).subtype
          (fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
      obtain ⟨n, hn⟩ := htwo.exists_card_dvd_pow
      have hc : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
      have hd : 3 ∣ 2 ^ n := (show 3 ∣ 2520 by decide).trans (hc ▸ hn)
      exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
  rw [← heptadAlternatingAction_ker]
  intro x hx
  have h : f x ∈ (⊥ : Subgroup (alternatingGroup (Fin 7))) :=
    hb ▸ (mem_map.mpr ⟨x, hx, rfl⟩)
  exact h

private instance kernel_characteristic : heptadKernel.Characteristic := by
  rw [kernel_eq_core]
  infer_instance

private theorem kernel_aut_card : Nat.card (MulAut heptadKernel) = 20160 := by
  let V := Fin 4 → ZMod 2
  let e : MulAut (Multiplicative V) ≃* (V ≃ₗ[ZMod 2] V) :=
    { toFun := fun a =>
        { toFun := fun v => (a (Multiplicative.ofAdd v)).toAdd
          invFun := fun v => (a.symm (Multiplicative.ofAdd v)).toAdd
          left_inv := a.left_inv
          right_inv := a.right_inv
          map_add' := fun v w => congrArg Multiplicative.toAdd (map_mul a _ _)
          map_smul' := by
            intro c v
            have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
            rcases hc c with rfl | rfl
            · simp only [zero_smul, RingHom.id_apply]; exact map_one a
            · simp only [one_smul, RingHom.id_apply] }
      invFun := fun a =>
        { toFun := fun v => Multiplicative.ofAdd (a v.toAdd)
          invFun := fun v => Multiplicative.ofAdd (a.symm v.toAdd)
          left_inv := a.left_inv
          right_inv := a.right_inv
          map_mul' := fun v w => congrArg Multiplicative.ofAdd (map_add a _ _) }
      left_inv := by intro a; ext; rfl
      right_inv := by intro a; ext; rfl
      map_mul' := by intro a b; ext; rfl }
  let m := ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
    (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod 2) (Fin 4))).symm)
  rw [Nat.card_congr ((MulAut.congr heptadBinaryEquiv.symm).trans (e.trans m)).toEquiv,
    Matrix.card_GL_field (𝔽 := ZMod 2) 4]
  norm_num [Fin.prod_univ_succ, ZMod.card]

private theorem conjugation_kernel :
    (MulAut.conjNormal : heptadStabilizer →* MulAut heptadKernel).ker = heptadKernel := by
  rw [MulAut.conjNormal_ker_eq_centralizer]
  apply le_antisymm heptadKernel_selfCentralizing
  intro x hx y hy
  exact congrArg Subtype.val (heptadKernel_mul_comm ⟨y, hy⟩ ⟨x, hx⟩)

private theorem conjugation_index :
    (MulAut.conjNormal : heptadStabilizer →* MulAut heptadKernel).range.index = 8 := by
  have h1 := Subgroup.card_mul_index heptadKernel
  rw [heptadKernel_card, heptadStabilizer_card] at h1
  have h2 : Nat.card (MulAut.conjNormal : heptadStabilizer →* MulAut heptadKernel).range = 2520 := by
    rw [← Subgroup.index_ker, conjugation_kernel]
    omega
  have h3 := (MulAut.conjNormal : heptadStabilizer →* MulAut heptadKernel).range.card_mul_index
  rw [h2, kernel_aut_card] at h3
  omega

private theorem inner_image :
    (MulAut.innerSubgroup heptadStabilizer).map (MulAut.characteristic heptadKernel) =
      (MulAut.conjNormal : heptadStabilizer →* MulAut heptadKernel).range := by
  ext a
  constructor
  · rintro ⟨b, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, rfl⟩

/-- The full outer automorphism group of the concrete heptad stabilizer is a two-group. -/
public theorem heptad_outer_isTwoGroup : IsPGroup 2 (MulAut.Outer heptadStabilizer) := by
  let I := MulAut.innerSubgroup heptadStabilizer
  let r := MulAut.characteristic heptadKernel
  have hk : IsPGroup 2 r.ker :=
    heptadKernel.isPGroup_characteristic_restriction_kernel_of_centralizer_le
      heptadKernel_isTwoGroup heptadKernel_selfCentralizing
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hmap : (I.map r).index = 8 := inner_image ▸ conjugation_index
  have hs : (I ⊔ r.ker).index ∣ 2 ^ 3 := by
    have h := I.index_map r
    rw [hmap] at h
    exact ⟨r.range.index, h⟩
  have hr : I.relIndex (I ⊔ r.ker) ∣ 2 ^ n := by
    rw [Subgroup.relIndex_sup_left]
    exact hn ▸ I.relIndex_dvd_card r.ker
  apply IsPGroup.of_card_dvd_pow (n := n + 3)
  change I.index ∣ _
  rw [← Subgroup.relIndex_mul_index (show I ≤ I ⊔ r.ker from le_sup_left), pow_add]
  exact Nat.mul_dvd_mul hr hs

end Sporadic.Mathieu.M23Geometry.OuterRestriction
