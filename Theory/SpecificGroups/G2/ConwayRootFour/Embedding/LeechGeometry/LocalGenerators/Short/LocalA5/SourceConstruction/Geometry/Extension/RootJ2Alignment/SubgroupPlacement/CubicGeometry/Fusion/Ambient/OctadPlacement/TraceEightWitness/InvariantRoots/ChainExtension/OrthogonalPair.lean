module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension.Geometry
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumVectorStabilizer

/-!
# Placement of the first orthogonal pair

Transitivity on the minimal shell places the first vector. The proved
orthogonal-shell orbit theorem then places the second vector using an
isometry fixing the first. Both vectors, including their signs, are retained.
The final theorem applies this construction to a marked D₄ configuration.

Source: the coordinate and orbit arguments of Aschbacher, *Sporadic Groups*
(1994), Chapter 8, as implemented by the imported ATLAS-port minimal-vector
and orthogonal-vector transitivity theorems.
-/

open Atlas.Lattices Atlas.Codes Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness.ChainExtension

@[expose] public noncomputable section

/-- Simultaneous placement of an ordered orthogonal pair of minimal vectors. -/
theorem orthogonal_pair_placement (x y : leech)
    (hx : integerDot x.val x.val = 32) (hy : integerDot y.val y.val = 32)
    (hxy : integerDot x.val y.val = 0) (a b : Omega) (hab : a ≠ b) :
    ∃ g : LeechIsometryGroup,
      g.val x = minimumPairPlus a b ∧ g.val y = minimumPairMinus a b := by
  let := full_minimum_pretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (α := LeechShell 4) LeechIsometryGroup
    (⟨x, hx⟩ : LeechShell 4)
    (⟨minimumPairPlus a b, minimumPairPlus_norm a b hab⟩ : LeechShell 4)
  have hxg : g.val x = minimumPairPlus a b := congrArg Subtype.val hg
  have hgy : integerDot (g.val y).val (g.val y).val = 32 := (g.prop y y).trans hy
  have horth : integerDot (minimumPairPlus a b).val (g.val y).val = 0 := by
    rw [← hxg, g.prop, hxy]
  have horb := strict_overgroup_orthogonal_orbit_full ⊤ monomial_lt_full a b hab
    (⟨g.val y, hgy⟩ : LeechShell 4) horth
    (⟨minimumPairMinus a b, minimumPairMinus_norm a b hab⟩ : LeechShell 4)
    (minimumPair_orthogonal a b hab)
  obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp horb
  refine ⟨k.val.val * g, ?_, ?_⟩
  · change k.val.val.val (g.val x) = _
    rw [hxg]
    exact k.prop
  · exact congrArg Subtype.val hk

/-- Actual application to the first two roots of every marked D₄ configuration. -/
theorem D4Configuration.place_first_pair (f : D4Configuration) :
    ∃ g : LeechIsometryGroup,
      g.val (f.root 0) = standardD4 0 ∧ g.val (f.root 1) = standardD4 1 := by
  have hn (i : Fin 4) : integerDot (f.root i).val (f.root i).val = 32 := by
    rw [← leechIntegralPairing_mul, f.gram]
    fin_cases i <;> norm_num [d4Gram]
  have ho : integerDot (f.root 0).val (f.root 1).val = 0 := by
    rw [← leechIntegralPairing_mul, f.gram]
    norm_num [d4Gram]
  exact orthogonal_pair_placement (f.root 0) (f.root 1) (hn 0) (hn 1) ho
    (frameCoordinate 0) (frameCoordinate 1) (by decide)

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness.ChainExtension
