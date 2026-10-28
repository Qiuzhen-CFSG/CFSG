module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Geometry.Marking
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Transporting marked G₂ parabolics through the central kernel

An element of S ∩ N_G(L) acts on L and preserves S ∩ L. The model kernel
is characteristic, being either trivial or the center, so this action descends
to the actual derived G₂ model. Consequently invariance under automorphisms
preserving the standard Sylow subgroup suffices to construct the relative
normalizer fields of the parabolic coordinates, including central two-covers.

This module proves the transport, not the intrinsic parabolic-invariance
premise. Source: the invariant-parabolic step of Aschbacher–Smith 2.3.9(7),
printed p.526, with the model cases of 1.1.5(3), pp.501–502.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2
open Subgroup

private theorem descend_automorphism {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) [f.ker.Characteristic]
    (a : MulAut A) : ∃ b : MulAut B, ∀ x, b (f x) = f (a x) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let b : MulAut B := e.symm.trans ((quotientAut f.ker a).trans e)
  refine ⟨b, ?_⟩
  intro x
  have he (y : A) : e (QuotientGroup.mk' f.ker y) = f y := rfl
  change e (quotientAut f.ker a (e.symm (f x))) = f (a x)
  rw [← he x, e.symm_apply_apply, quotientAut_apply_mk, he]

private theorem preserves_intersection {G : Type*} [Group G]
    (L S : Subgroup G) (s : normalizer (L : Set G)) (hs : (s : G) ∈ S) :
    (S.subgroupOf L).map (L.normalizerMonoidHom s).toMonoidHom = S.subgroupOf L := by
  have hf (u : normalizer (L : Set G)) (hu : (u : G) ∈ S) {x : L}
      (hx : x ∈ S.subgroupOf L) : L.normalizerMonoidHom u x ∈ S.subgroupOf L := by
    change (L.normalizerMonoidHom u x : G) ∈ S
    rw [normalizerMonoidHom_apply_apply_coe]
    exact S.mul_mem (S.mul_mem hu hx) (S.inv_mem hu)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hf s hs hy
  · intro hx
    refine ⟨L.normalizerMonoidHom s⁻¹ x, hf s⁻¹ (S.inv_mem hs) hx, ?_⟩
    rw [map_inv]
    exact (L.normalizerMonoidHom s).apply_symm_apply x

private theorem normalizes_comap_of_stabilizer_invariant
    {G K : Type*} [Group G] [Group K] {L S : Subgroup G}
    (f : L →* K) (hf : Function.Surjective f) [f.ker.Characteristic]
    (R P : Subgroup K) (hR : (S.subgroupOf L).map f = R)
    (hP : ∀ b : MulAut K, R.map b.toMonoidHom = R → P.map b.toMonoidHom = P) :
    S ⊓ normalizer (L : Set G) ≤ normalizer ((P.comap f).map L.subtype : Set G) := by
  intro s hs
  let n : normalizer (L : Set G) := ⟨s, hs.2⟩
  let a := L.normalizerMonoidHom n
  have haR : (S.subgroupOf L).map a.toMonoidHom = S.subgroupOf L :=
    preserves_intersection L S n hs.1
  obtain ⟨b, hb⟩ := descend_automorphism f hf a
  have hbf : b.toMonoidHom.comp f = f.comp a.toMonoidHom := by
    ext x
    exact hb x
  have hbR : R.map b.toMonoidHom = R := by
    rw [← hR, Subgroup.map_map, hbf, ← Subgroup.map_map, haR]
  have hbP (x : K) : b x ∈ P ↔ x ∈ P := by
    constructor
    · intro hx
      rw [← hP b hbR] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact b.injective he ▸ hy
    · intro hx
      rw [← hP b hbR]
      exact mem_map_of_mem b.toMonoidHom hx
  have haP : (P.comap f).map a.toMonoidHom = P.comap f := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change f (a y) ∈ P
      rw [← hb]
      exact (hbP _).mpr hy
    · intro hx
      refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
      change f (a.symm x) ∈ P
      apply (hbP _).mp
      rw [hb, a.apply_symm_apply]
      exact hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he : ((MulAut.conj s : MulAut G) : G →* G).comp L.subtype = L.subtype.comp a.toMonoidHom := by
    ext x
    exact (normalizerMonoidHom_apply_apply_coe L n x).symm
  rw [Subgroup.map_map, he, ← Subgroup.map_map, haP]

variable {G : Type*} [Group G] {L S : Subgroup G}
namespace SylowModel

/-- Sylow-stabilizer invariance in the derived model implies the required
relative normalizer invariance after pulling back through the model map. -/
theorem normalizes_pullback (d : SylowModel L S)
    (P : Subgroup (Atlas.G2.Model d.field))
    (hP : ∀ b : MulAut (commutator (Atlas.G2.Model d.field)),
      (Atlas.G2.unipotent.subgroupOf (commutator (Atlas.G2.Model d.field))).map
          b.toMonoidHom = Atlas.G2.unipotent.subgroupOf (commutator (Atlas.G2.Model d.field)) →
      (P.subgroupOf (commutator (Atlas.G2.Model d.field))).map b.toMonoidHom =
        P.subgroupOf (commutator (Atlas.G2.Model d.field))) :
    S ⊓ normalizer (L : Set G) ≤
      normalizer ((P.comap d.modelMap).map L.subtype : Set G) := by
  let D := commutator (Atlas.G2.Model d.field)
  let f : L →* D := d.modelMap.codRestrict D (fun x => by
    change d.modelMap x ∈ commutator (Atlas.G2.Model d.field)
    rw [← d.model_range]
    exact ⟨x, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (show y.val ∈ d.modelMap.range from d.model_range.symm ▸ y.property)
    exact ⟨x, Subtype.ext hx⟩
  have hk : d.modelMap.ker.Characteristic := by
    rcases d.model_kernel with hk | ⟨_, hk, _, _⟩ <;> rw [hk] <;> infer_instance
  have : f.ker.Characteristic := by
    rw [MonoidHom.ker_codRestrict]
    exact hk
  have hR : (S.subgroupOf L).map f = Atlas.G2.unipotent.subgroupOf D := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_map]
    change (S.subgroupOf L).map d.modelMap = _
    rw [d.sylow_image, subgroupOf_map_subtype]
  exact normalizes_comap_of_stabilizer_invariant f hf
    (Atlas.G2.unipotent.subgroupOf D) (P.subgroupOf D) hR hP

/-- Assemble coordinates once the intrinsic Sylow-stabilizer calculation is
proved. No ambient normality of L, injectivity of the model map, or HeOver
claim is used in this construction. -/
def coordinatesOfStabilizerInvariant (d : SylowModel L S)
    (hinv : ∀ b : MulAut (commutator (Atlas.G2.Model d.field)),
      (Atlas.G2.unipotent.subgroupOf (commutator (Atlas.G2.Model d.field))).map
          b.toMonoidHom = Atlas.G2.unipotent.subgroupOf (commutator (Atlas.G2.Model d.field)) →
      ((Atlas.G2.LieParabolicSetup.parabolic₁.subgroupOf
          (commutator (Atlas.G2.Model d.field))).map b.toMonoidHom =
        Atlas.G2.LieParabolicSetup.parabolic₁.subgroupOf (commutator (Atlas.G2.Model d.field))) ∧
      ((Atlas.G2.LieParabolicSetup.parabolic₂.subgroupOf
          (commutator (Atlas.G2.Model d.field))).map b.toMonoidHom =
        Atlas.G2.LieParabolicSetup.parabolic₂.subgroupOf (commutator (Atlas.G2.Model d.field)))) :
    ParabolicCoordinates L S where
  field := d.field
  fieldInstance := d.fieldInstance
  finiteField := d.finiteField
  characteristic := d.characteristic
  exponent := d.exponent
  exponent_pos := d.exponent_pos
  field_card := d.field_card
  modelMap := d.modelMap
  model_range := d.model_range
  model_kernel := d.model_kernel
  sylow_image := d.sylow_image
  first_invariant := d.normalizes_pullback _ (fun b hb => (hinv b hb).1)
  second_invariant := d.normalizes_pullback _ (fun b hb => (hinv b hb).2)

end SylowModel
end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
