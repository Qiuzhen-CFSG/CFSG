module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.GeometryInterface
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Geometry
public import Mathlib.FieldTheory.Finiteness

/-!
# A binary anisotropic moved plane determines its cubic rotation

For an isometry `a` with `a³ = 1`, its displacement range satisfies
`a²v = v + av`. Hence it contains no nonzero fixed vector. On an
anisotropic moved plane, any nonzero `v` and `av` form a basis of quadratic
values one and polar value one.

Two isometries with displacement in this plane and the same basis rotation
are equal: their difference lies in the plane and pairs to zero with its
nondegenerate basis. Consequently an actual transport of rotation bases
conjugates the original isometries on the whole eight-dimensional space.
The final consumer is `OmegaGeometry.anisotropic_cyclic_fusion`.

Source: the binary orthogonal geometry underlying Aschbacher,
*Sporadic Groups* (1994), §25 and the quaternion class in §46, p.251.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.SelectedGeometry

private theorem binary_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

private theorem binary_one {t : ZMod 2} (ht : t ≠ 0) : t = 1 := by
  exact (binary_cases t).resolve_left ht

private theorem preserves (a : Orthogonal) (v : Space) : form (a.val v) = form v :=
  (mem_quadraticIsometrySubgroup form _).mp a.prop v

private theorem preserves_polar (a : Orthogonal) (v w : Space) :
    form.polarBilin (a.val v) (a.val w) = form.polarBilin v w := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, preserves]

private theorem polar_self_zero (v : Space) : form.polarBilin v v = 0 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    ZModModule.add_self, map_zero]
  simp

private theorem polar_symm (v w : Space) : form.polarBilin v w = form.polarBilin w v := by
  exact QuadraticMap.polar_comm form v w

theorem cubic_on_moved (a : Orthogonal) (ha : a ^ 3 = 1) (v : Space)
    (hv : v ∈ movedSpace a) : a.val (a.val v) = v + a.val v := by
  obtain ⟨x, rfl⟩ := hv
  have h3 : a.val (a.val (a.val x)) = x := by
    simpa only [pow_succ, pow_zero, mul_one, Subgroup.coe_mul, LinearEquiv.mul_apply, Subgroup.coe_one, LinearEquiv.coe_one, id_eq]
      using congrArg (fun g : Orthogonal => g.val x) ha
  change a.val (a.val (a.val x - x)) = (a.val x - x) + a.val (a.val x - x)
  rw [map_sub, map_sub, h3]
  have he : (a.val x - x) + (a.val (a.val x) - a.val x) = a.val (a.val x) - x := by abel
  rw [he]
  simp only [ZModModule.sub_eq_add, add_comm]

theorem cubic_moved_no_fixed (a : Orthogonal) (ha : a ^ 3 = 1) (v : Space)
    (hv : v ∈ movedSpace a) (hf : a.val v = v) : v = 0 := by
  have h := cubic_on_moved a ha v hv
  rw [hf, hf, ZModModule.add_self] at h
  exact h

theorem apply_mem_moved (a : Orthogonal) (v : Space) (hv : v ∈ movedSpace a) :
    a.val v ∈ movedSpace a := by
  obtain ⟨x, rfl⟩ := hv
  refine ⟨a.val x, ?_⟩
  exact (map_sub a.val (a.val x) x).symm

theorem exists_rotation_pair (a : Orthogonal) (ha : a ^ 3 = 1)
    (hplane : AnisotropicPlane a) :
    ∃ v w : Space, form v = 1 ∧ form w = 1 ∧ form.polarBilin v w = 1 ∧
      movedSpace a = Submodule.span (ZMod 2) {v, w} ∧
      a.val v = w ∧ a.val w = v + w := by
  have hbot : movedSpace a ≠ ⊥ := by
    intro hz
    have hd := hplane.1
    rw [hz, finrank_bot] at hd
    contradiction
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let w := a.val v
  have hw : w ∈ movedSpace a := apply_mem_moved a v hv
  have hw0 : w ≠ 0 := fun h => hv0 (a.val.injective (h.trans (map_zero _).symm))
  have hvw : v ≠ w := fun h => hv0 (cubic_moved_no_fixed a ha v hv h.symm)
  have hqv : form v = 1 := binary_one (hplane.2 v hv hv0)
  have hqw : form w = 1 := (preserves a v).trans hqv
  have hsum : v + w ≠ 0 := by
    intro h
    apply hvw
    have ht := congrArg (fun x : Space => x + w) h
    simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using ht
  have hqs : form (v + w) = 1 := binary_one
    (hplane.2 _ ((movedSpace a).add_mem hv hw) hsum)
  have hpol : form.polarBilin v w = 1 := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hqv, hqw, hqs]
    decide
  have hspan : Submodule.span (ZMod 2) {v, w} = movedSpace a := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (Set.insert_subset hv (Set.singleton_subset_iff.mpr hw))
    · have hi : LinearIndependent (ZMod 2) ![v, w] := by
        rw [linearIndependent_fin2]
        refine ⟨hw0, ?_⟩
        intro t
        rcases binary_cases t with rfl | rfl
        · simpa using hv0.symm
        · simpa using hvw.symm
      have hd := finrank_span_eq_card hi
      have hr : Set.range (![v, w] : Fin 2 → Space) = {v, w} := by
        ext z
        simp [eq_comm, or_comm]
      rw [hr] at hd
      simpa only [Fintype.card_fin, hplane.1] using hd
  exact ⟨v, w, hqv, hqw, hpol, hspan.symm, rfl, cubic_on_moved a ha v hv⟩

/-- The rotation on a polar-nondegenerate moved plane determines the isometry. -/
theorem eq_of_rotation_pair (a b : Orthogonal) (v w : Space)
    (hab : form.polarBilin v w = 1)
    (ha : movedSpace a ≤ Submodule.span (ZMod 2) {v, w})
    (hb : movedSpace b ≤ Submodule.span (ZMod 2) {v, w})
    (hav : a.val v = w) (haw : a.val w = v + w)
    (hbv : b.val v = w) (hbw : b.val w = v + w) : a = b := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply sub_eq_zero.mp
  have hd : a.val x - b.val x ∈ Submodule.span (ZMod 2) {v, w} := by
    have hh := (Submodule.span (ZMod 2) {v, w}).sub_mem
      (ha (LinearMap.mem_range_self (a.val.toLinearMap - LinearMap.id) x))
      (hb (LinearMap.mem_range_self (b.val.toLinearMap - LinearMap.id) x))
    simpa only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_sub_sub_cancel_right] using hh
  have hpw : form.polarBilin (a.val x - b.val x) w = 0 := by
    have hap := preserves_polar a x v
    have hbp := preserves_polar b x v
    rw [hav] at hap
    rw [hbv] at hbp
    simp only [map_sub, LinearMap.sub_apply, hap, hbp, sub_self]
  have hpvw : form.polarBilin (a.val x - b.val x) (v + w) = 0 := by
    have hap := preserves_polar a x w
    have hbp := preserves_polar b x w
    rw [haw] at hap
    rw [hbw] at hbp
    simp only [map_sub, LinearMap.sub_apply, hap, hbp, sub_self]
  have hpv : form.polarBilin (a.val x - b.val x) v = 0 := by
    simpa only [map_add, hpw, add_zero] using hpvw
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hd
  have hs : s = 0 := by
    have hh := congrArg (fun z : Space => form.polarBilin z w) hst
    simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hab, polar_self_zero, smul_eq_mul, mul_one, mul_zero, add_zero, hpw] using hh
  have ht : t = 0 := by
    have hh := congrArg (fun z : Space => form.polarBilin z v) hst
    simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      polar_self_zero, polar_symm w v, hab, smul_eq_mul, mul_zero, mul_one, zero_add, hpv] using hh
  simp only [← hst, hs, ht, zero_smul, zero_add]

/-- The literal range of `a - 1` transforms covariantly under conjugation. -/
theorem movedSpace_conjugate (a c : Orthogonal) :
    movedSpace ((MulAut.conj c) a) = (movedSpace a).map c.val.toLinearMap := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨a.val (c.val.symm v) - c.val.symm v, ⟨c.val.symm v, rfl⟩, ?_⟩
    change c.val (a.val (c.val.symm v) - c.val.symm v) =
      c.val (a.val (c.val.symm v)) - v
    rw [map_sub, c.val.apply_symm_apply]
  · rintro hx
    obtain ⟨v, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_map.mp hx
    refine ⟨c.val w, ?_⟩
    change c.val (a.val (c.val.symm (c.val w))) - c.val w =
      c.val (a.val w - w)
    rw [c.val.symm_apply_apply, map_sub]

/-- Transporting an ordered rotation basis transports the whole orthogonal cubic. -/
theorem conjugate_of_rotation_pair (a b c : Orthogonal) (v w u t : Space)
    (hp : form.polarBilin v w = 1)
    (ha : movedSpace a = Submodule.span (ZMod 2) {v, w})
    (hb : movedSpace b = Submodule.span (ZMod 2) {u, t})
    (hav : a.val v = w) (haw : a.val w = v + w)
    (hbu : b.val u = t) (hbt : b.val t = u + t)
    (hcu : c.val u = v) (hct : c.val t = w) :
    a = (MulAut.conj c) b := by
  have hcvi : c.val.symm v = u := c.val.symm_apply_eq.mpr hcu.symm
  have hcwi : c.val.symm w = t := c.val.symm_apply_eq.mpr hct.symm
  apply eq_of_rotation_pair a ((MulAut.conj c) b) v w hp ha.le
  · rw [movedSpace_conjugate, hb, Submodule.map_span]
    simp only [Set.image_pair, LinearEquiv.coe_coe, hcu, hct]
    exact le_rfl
  · exact hav
  · exact haw
  · change c.val (b.val (c.val.symm v)) = w
    rw [hcvi, hbu, hct]
  · change c.val (b.val (c.val.symm w)) = v + w
    rw [hcwi, hbt, map_add, hcu, hct]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.SelectedGeometry
