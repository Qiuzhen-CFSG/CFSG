module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceMarking
public import Theory.Representation.PSL3Two.NaturalOrbits
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
/-!
# The original point residual in the fixed qL marking

The original involution z determines a nonzero vector in the original natural
coordinates. Transitivity carries the standard point to this vector without
changing qL. Equivariance identifies L ∩ H with its stabilizer, and surjective
residual transport identifies the image of L₁ = O²(L ∩ H) with a conjugate of
the literal order-twelve point residual. This supplies the earlier marking
needed by the Steinberg commutator calculation for S = [S,L₁].

Source: Aschbacher–Smith, 14.7.73, printed p.1076, with the point-parabolic
setup of 12.8.1; combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images
open Chapter12.Section08 CriticalFusion.Source Matrix.PSL3Two
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The point-residual image in the original qL marking is an actual
conjugate of pointA. No alternate quotient marking is introduced. -/
theorem exists_point_residual_image : ∃ g : BinaryLinearThree.Group,
    ((F.Li L 1).subgroupOf L).map d.qL =
      MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom := by
  have hzV : d.z ∈ V := F.le_seed 1 (d.point ▸ mem_zpowers d.z)
  let zV : V := ⟨d.z, hzV⟩
  let v := (d.naturalCoordinates zV).toAdd
  have hv : v ≠ 0 := by
    intro h
    exact d.z_ne_one (congrArg Subtype.val
      (d.naturalCoordinates_bijective.1 (h.trans d.naturalCoordinates.map_one.symm)))
  obtain ⟨g, hg⟩ := BinaryLinearThree.natural_transitive_nonzero ![1,0,0] v (by simp) hv
  have hbase (a : BinaryLinearThree.Group) :
      BinaryLinearThree.W a ![1,0,0] = ![1,0,0] ↔ a ∈ pointParabolicSL := by
    change (a • flagPoint).val = flagPoint.val ↔ _
    rw [← Subtype.ext_iff, ← MulAction.mem_stabilizer_iff, Fano.stabilizer_flagPoint_SL]
  let J := pointParabolicSL.map (MulAut.conj g).toMonoidHom
  have hJ (a : BinaryLinearThree.Group) : a ∈ J ↔ BinaryLinearThree.W a v = v := by
    constructor
    · rintro ⟨b, hb, rfl⟩
      change BinaryLinearThree.W (g * b * g⁻¹) v = v
      rw [← hg]
      simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply,
        (hbase b).mpr hb]
    · intro ha
      refine ⟨g⁻¹ * a * g, (hbase _).mp ?_, ?_⟩
      · simp only [map_mul, Module.End.mul_apply]
        rw [hg, ha, ← hg, Representation.inv_self_apply]
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc,
          mul_inv_cancel, mul_one, mul_inv_cancel_left]
  have hmem (l : L) : (l : G) ∈ F.H ↔ d.qL l ∈ J := by
    rw [hJ, ← d.naturalCoordinates_equivariant l zV]
    change (l : G) ∈ F.H ↔ d.naturalCoordinates _ = d.naturalCoordinates zV
    rw [d.naturalCoordinates_bijective.1.eq_iff, Subtype.ext_iff,
      d.centralizer_eq, mem_centralizer_singleton_iff]
    change (l : G) * d.z = d.z * l ↔ (l : G) * d.z * (l : G)⁻¹ = d.z
    exact ⟨fun h => by rw [h, mul_inv_cancel_right], fun h => by
      have hh := congrArg (fun x : G => x * l) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh⟩
  let N := L ⊓ F.H
  let f : N →* J := (d.qL.comp (inclusion (inf_le_left : N ≤ L))).codRestrict J
    (fun n => (hmem ⟨n, n.property.1⟩).mp n.property.2)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨l, hl⟩ := d.qL_surjective a
    exact ⟨⟨l, l.property, (hmem l).mpr (hl ▸ a.property)⟩, Subtype.ext hl⟩
  have hres : F.Li L 1 = (pResidual 2 N).map N.subtype := by
    simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,
      if_false]
    rfl
  have himage : ((F.Li L 1).subgroupOf L).map d.qL =
      (pResidual 2 J).map J.subtype := by
    ext a
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨n, hn, he⟩ := hres ▸ hl
      have he' : l = ⟨n, n.property.1⟩ := Subtype.ext he.symm
      subst l
      refine ⟨f n, ?_, rfl⟩
      rw [← map_pResidual_of_surjective 2 f hf]
      exact mem_map_of_mem f hn
    · rintro ⟨a, ha, rfl⟩
      rw [← map_pResidual_of_surjective 2 f hf] at ha
      obtain ⟨n, hn, he⟩ := ha
      exact ⟨⟨n, n.property.1⟩, hres ▸ mem_map_of_mem N.subtype hn,
        congrArg Subtype.val he⟩
  refine ⟨g, himage.trans ?_⟩
  change (pResidual 2 (pointParabolicSL.map (MulAut.conj g).toMonoidHom)).map
    (pointParabolicSL.map (MulAut.conj g).toMonoidHom).subtype = _
  rw [← map_embedded_pResidual]
  exact congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) MarkedAutomorphisms.point_residual

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images
