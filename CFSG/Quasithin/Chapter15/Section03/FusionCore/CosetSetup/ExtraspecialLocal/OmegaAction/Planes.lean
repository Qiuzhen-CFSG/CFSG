module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.Setup
public import Theory.GroupTheory.WreathTwoSylowModel

/-!
# The orthogonal Sylow center preserves the definite planes

The standard dihedral Sylow center has trivial coordinate permutation.
Conjugating the actual Sylow subgroup preserves that property. Compatibility
of the specified natural action then transports coordinate-plane invariance
back to the two planes in G. This gives the geometric descent needed after
the quotient-centralizer computation; it assumes no property of a conjugate
span.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the calculation
after 15.3.49(b), printed p.1143.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem standard_center_shift : ∀ a : DihedralGroup 4,
    (∀ b : DihedralGroup 4, b * a = a * b) → (wreathTwoDihedralHom a).right = 1 := by
  decide +kernel

theorem orthogonal_sylow_center_shift (P : Sylow 2 OrthogonalActor) {z : OrthogonalActor}
    (hz : z ∈ (center P).map (P : Subgroup OrthogonalActor).subtype) : z.right = 1 := by
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq OrthogonalActor wreathTwoSylow P
  let e := MulAut.conj u
  have hmap : wreathTwoDihedralHom.range.map e.toMonoidHom = (P : Subgroup OrthogonalActor) := by
    have hh := congrArg (fun S : Sylow 2 OrthogonalActor => (S : Subgroup OrthogonalActor)) hu
    change (wreathTwoSylow : Subgroup OrthogonalActor).map e.toMonoidHom = _ at hh
    rwa [wreathTwoSylow_coe] at hh
  let j : DihedralGroup 4 →* OrthogonalActor := e.toMonoidHom.comp wreathTwoDihedralHom
  have hjinj : Function.Injective j := e.injective.comp wreathTwoDihedralHom_injective
  have hjrange : j.range = (P : Subgroup OrthogonalActor) := by
    rw [MonoidHom.range_comp]
    exact hmap
  obtain ⟨z, hz, rfl⟩ := hz
  obtain ⟨a, ha⟩ := (show (z : OrthogonalActor) ∈ j.range from hjrange.symm ▸ z.property)
  have hac : ∀ b : DihedralGroup 4, b * a = a * b := by
    intro b
    apply hjinj
    rw [map_mul, map_mul, ha]
    exact congrArg Subtype.val ((mem_center_iff.mp hz)
      ⟨j b, hjrange ▸ (show j b ∈ j.range from ⟨b, rfl⟩)⟩)
  have hs := standard_center_shift a hac
  change (z : OrthogonalActor).right = 1
  rw [← ha]
  change (u * wreathTwoDihedralHom a * u⁻¹).right = 1
  simp [hs]

variable {G : Type*} [Group G]

theorem normalizes_plane_of_image_shift_one {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M)
    (hshift : ∀ z ∈ d.image X, z.right = 1) (i : OrthogonalPlaneIndex) :
    X ≤ normalizer (d.plane i : Set G) := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  apply le_normalizer_iff.mpr
  intro x hx v hv
  obtain ⟨v, hv, rfl⟩ := hv
  let m : M := ⟨x, hXM hx⟩
  let w : V := V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v
  refine ⟨w, ?_, rfl⟩
  have hs : (d.actor m).right = 1 := hshift _ ⟨m, hx, rfl⟩
  change ∀ j, j ≠ i → d.coordinates w j = 1
  intro j hj
  rw [show d.coordinates w = d.actor m • d.coordinates v from d.compatible m v]
  change (d.actor m).left j • d.coordinates v ((d.actor m).right⁻¹ * j) = 1
  rw [hs, inv_one, one_mul, show d.coordinates v j = 1 from hv j hj]
  exact smul_one _

theorem le_planeStabilizer_of_image_le_center [Finite G] {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hXT : X ≤ (T : Subgroup G))
    (himage : d.image X ≤ (center (d.image (T : Subgroup G))).map
      (d.image (T : Subgroup G)).subtype) (i : OrthogonalPlaneIndex) :
    X ≤ planeStabilizer T (d.plane i) := by
  refine le_inf hXT (normalizes_plane_of_image_shift_one d (hXT.trans hTM) ?_ i)
  intro z hz
  apply orthogonal_sylow_center_shift (orthogonalSylowImage d T hTM)
  exact himage hz

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
