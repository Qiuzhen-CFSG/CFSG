module

public import Mathlib.GroupTheory.Sylow

/-!
# Lifting cyclic cubic fusion through a two-group kernel

The inverse image of a common cyclic image contains the two cubic subgroups as
Sylow three-subgroups. Indeed, a larger three-subgroup maps injectively because
its intersection with the two-group kernel is trivial. Sylow conjugacy then
lifts equality of cyclic images. A conjugator in the actual homomorphism image
can first be lifted, reducing image conjugacy to that equality case.

This supplies the group-theoretic lifting step for the octad restriction action
in `octadLocalFusion_of_restriction`; it requires no extraspecial presentation,
splitting, or presumed ambient fusion.
-/

@[expose] public noncomputable section
open Subgroup
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

private def sylowOfFullImage {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hk : IsPGroup 2 f.ker) (P : Subgroup G)
    (hp : IsPGroup 3 P) (hf : P.map f = f.range) : Sylow 3 G where
  toSubgroup := P
  isPGroup' := hp
  is_maximal' := by
    intro Q hQ hPQ
    apply le_antisymm _ hPQ
    intro q hq
    have himage : f q ∈ P.map f := by rw [hf]; exact ⟨q, rfl⟩
    obtain ⟨p, hp, he⟩ := Subgroup.mem_map.mp himage
    have hd : Disjoint Q f.ker := hQ.disjoint_of_coprime hk (by decide)
    have h1 : q * p⁻¹ = 1 := Subgroup.disjoint_def.mp hd
      (Q.mul_mem hq (Q.inv_mem (hPQ hp))) (by simp [MonoidHom.mem_ker, he])
    exact mul_inv_eq_one.mp h1 ▸ hp

private theorem cyclic_fusion_of_equal_image {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hk : IsPGroup 2 f.ker) {x y : G}
    (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hxy : Subgroup.zpowers (f x) = Subgroup.zpowers (f y)) :
    ∃ c : G, Subgroup.zpowers x = (Subgroup.zpowers y).map (MulAut.conj c).toMonoidHom := by
  let K := (Subgroup.zpowers (f x)).comap f
  let xK : K := ⟨x, Subgroup.mem_zpowers _⟩
  let yK : K := ⟨y, by change f y ∈ Subgroup.zpowers (f x); rw [hxy]; exact Subgroup.mem_zpowers _⟩
  let fK := f.comp K.subtype
  have hkK : IsPGroup 2 fK.ker := hk.comap_of_injective K.subtype Subtype.val_injective
  have hpX : IsPGroup 3 (Subgroup.zpowers xK) := by
    apply IsPGroup.of_card (n := 1)
    exact (Nat.card_zpowers xK).trans ((Subgroup.orderOf_coe xK).symm.trans hx)
  have hpY : IsPGroup 3 (Subgroup.zpowers yK) := by
    apply IsPGroup.of_card (n := 1)
    exact (Nat.card_zpowers yK).trans ((Subgroup.orderOf_coe yK).symm.trans hy)
  have hiX : (Subgroup.zpowers xK).map fK = fK.range := by
    apply le_antisymm
    · rintro z hz
      obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp hz
      exact ⟨u, rfl⟩
    · rintro z ⟨q, rfl⟩
      rw [MonoidHom.map_zpowers]
      exact q.prop
  have hiY : (Subgroup.zpowers yK).map fK = fK.range := by
    apply le_antisymm
    · rintro z hz
      obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp hz
      exact ⟨u, rfl⟩
    · rintro z ⟨q, rfl⟩
      rw [MonoidHom.map_zpowers]
      change f q.val ∈ Subgroup.zpowers (f y)
      rw [← hxy]
      exact q.prop
  let SX := sylowOfFullImage fK hkK (Subgroup.zpowers xK) hpX hiX
  let SY := sylowOfFullImage fK hkK (Subgroup.zpowers yK) hpY hiY
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K SY SX
  have he : (Subgroup.zpowers yK).map (MulAut.conj c).toMonoidHom =
      Subgroup.zpowers xK := congrArg Sylow.toSubgroup hc
  have he' := congrArg (fun P : Subgroup K => P.map K.subtype) he
  simp only [MonoidHom.map_zpowers] at he'
  refine ⟨c.val, ?_⟩
  simpa [MonoidHom.map_zpowers, xK, yK, MulAut.conj_apply] using he'.symm

/-- Cyclic subgroup conjugacy lifts through a finite two-group kernel. -/
theorem cyclic_fusion_of_image_fusion {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hk : IsPGroup 2 f.ker) {x y : G}
    (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hxy : ∃ c : f.range, Subgroup.zpowers (f x) =
      (Subgroup.zpowers (f y)).map (MulAut.conj c.val).toMonoidHom) :
    ∃ c : G, Subgroup.zpowers x = (Subgroup.zpowers y).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨c, hc⟩ := hxy
  obtain ⟨d, hd⟩ := c.prop
  have he : Subgroup.zpowers (f x) = Subgroup.zpowers (f (MulAut.conj d y)) := by
    simpa [MonoidHom.map_zpowers, MulAut.conj_apply, hd] using hc
  obtain ⟨e, he⟩ := cyclic_fusion_of_equal_image f hk hx
    ((MulAut.conj d).orderOf_eq y |>.trans hy) he
  refine ⟨e * d, ?_⟩
  simpa [MonoidHom.map_zpowers, MulAut.conj_apply, mul_assoc] using he

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
