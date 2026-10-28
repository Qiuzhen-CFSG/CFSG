module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.Preparation

/-!
# Ambient cubic fusion through an octad centralizer

Place both fixed-free cubics in the centralizer of the same marked octad
involution, fuse their cyclic subgroups there, and compose the three actual
ambient conjugators. For Lean's left conjugation the result is `ga⁻¹ * c * gb`.
The integral version consumes the polynomial lifts constructed in Preparation.
The last theorem applies this to the existing relative-fusion reduction.

These are conditional assembly theorems. The geometric octad placement and
fusion inside its centralizer remain separate concrete model obligations.
In particular this module does not yet prove unconditional `AmbientFusion`.

Source: Aschbacher, *Sporadic Groups* (1994), 25.9 and Chapter 9,
Exercise 6 (p.141), 46.6 and 49.1–49.3 (pp.280–281).
-/

@[expose] public noncomputable section
open Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

/-- The two octad-centralizer obligations imply the exact published ambient fusion statement. -/
theorem ambientFusion_of_octad_data (hplacement : OctadPlacement)
    (hlocal : OctadLocalFusion) : AmbientFusion := by
  intro a b hoa hob hfa hfb
  obtain ⟨ga, hga⟩ := hplacement a hoa hfa
  obtain ⟨gb, hgb⟩ := hplacement b hob hfb
  obtain ⟨c, _, hc⟩ := hlocal (MulAut.conj ga a) (MulAut.conj gb b) hga hgb
    ((MulAut.conj ga).orderOf_eq a |>.trans hoa)
    ((MulAut.conj gb).orderOf_eq b |>.trans hob)
    (cubicFixedFree_conj hfa ga) (cubicFixedFree_conj hfb gb)
  refine ⟨ga⁻¹ * c * gb, ?_⟩
  have he := congrArg (fun P : Subgroup LeechCentralQuotient =>
    P.map (MulAut.conj ga⁻¹).toMonoidHom) hc
  simp only [MonoidHom.map_zpowers] at he ⊢
  simpa [MulAut.conj_apply, mul_assoc] using he

/-- The integral geometric premise and the local group premise together suffice. -/
theorem ambientFusion_of_integral_octad_data (hplacement : IntegralOctadPlacement)
    (hlocal : OctadLocalFusion) : AmbientFusion :=
  ambientFusion_of_octad_data (octadPlacement_of_integral hplacement) hlocal

/-- The actual relative-fusion consumer, retaining only the two octad obligations
and the independently owned tetrahedral orbit and action obligations. -/
theorem fixedFreeCubicFusion_of_integral_octad_data
    (hplacement : IntegralOctadPlacement) (hlocal : OctadLocalFusion)
    (horbit : TetrahedralOrbit) (haction : TetrahedralNormalizerAction) :
    FixedFreeCubicFusion :=
  fixedFreeCubicFusion_of_conjugacy_data
    (ambientFusion_of_integral_octad_data hplacement hlocal) horbit haction

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
