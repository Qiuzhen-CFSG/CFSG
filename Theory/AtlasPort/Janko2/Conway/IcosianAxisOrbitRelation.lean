/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisOrbitRelation.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianCoordinateAxisOrbits
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisNormInvariant

/-!
# IcosianAxisOrbitRelation

The full axis stabilizer defines an orbit relation on root points. Shape-and-norm
transitivity and transport provide its working criteria.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisOrbitRelation.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

abbrev icosianFullAxisStabilizer :=
  MulAction.stabilizer icosianHermitianGroup (icosianRootAxisPoint 0)

def IcosianSameAxisOrbit (p q : IcosianRootPoint) : Prop :=
  MulAction.orbit icosianFullAxisStabilizer p=MulAction.orbit icosianFullAxisStabilizer q

theorem icosianSameAxisOrbit_of_map (g : icosianHermitianGroup)
    (hg : g • icosianRootAxisPoint 0=icosianRootAxisPoint 0)
    (p q : IcosianRootPoint) (h : g • p=q) : IcosianSameAxisOrbit p q := by
  exact (MulAction.orbit_eq_iff.mpr (show q∈MulAction.orbit icosianFullAxisStabilizer p from
    ⟨⟨g,hg⟩,h⟩)).symm

theorem icosianSameAxisOrbit_of_shape_norm (a : Fin 4) (p q : IcosianRootPoint)
    (hp : HasIcosianRootPointShape p a) (hq : HasIcosianRootPointShape q a)
    (hn : icosianRootPointNormWord p 0=icosianRootPointNormWord q 0) :
    IcosianSameAxisOrbit p q := by
  obtain ⟨g,hg,he⟩ := icosianCoordinateAxis_shape_norm_transitive a p q hp hq hn
  exact icosianSameAxisOrbit_of_map g.val hg p q he

theorem icosianSameAxisOrbit_norm (p q : IcosianRootPoint) (h : IcosianSameAxisOrbit p q) :
    icosianRootPointNormWord p 0=icosianRootPointNormWord q 0 := by
  obtain ⟨g,hg⟩ := MulAction.orbit_eq_iff.mp h
  change g.val • q=p at hg
  rw [← hg]
  exact icosianAxisStabilizer_point_norm g.val g.property q

/-- Transport one verified link between two local pieces to arbitrary members
of those pieces, retaining their common intrinsic norm value. -/
theorem icosianSameAxisOrbit_transport {a b : Fin 4} {v : GoldenInteger}
    (p₀ q₀ : IcosianRootPoint) (hp₀ : HasIcosianRootPointShape p₀ a)
    (hq₀ : HasIcosianRootPointShape q₀ b)
    (hnp₀ : icosianRootPointNormWord p₀ 0=v)
    (hnq₀ : icosianRootPointNormWord q₀ 0=v)
    (h₀ : IcosianSameAxisOrbit p₀ q₀)
    (p q : IcosianRootPoint) (hp : HasIcosianRootPointShape p a)
    (hq : HasIcosianRootPointShape q b)
    (hnp : icosianRootPointNormWord p 0=v)
    (hnq : icosianRootPointNormWord q 0=v) : IcosianSameAxisOrbit p q := by
  exact (icosianSameAxisOrbit_of_shape_norm a p p₀ hp hp₀ (hnp.trans hnp₀.symm)).trans
    (h₀.trans (icosianSameAxisOrbit_of_shape_norm b q₀ q hq₀ hq (hnq₀.trans hnq.symm)))

end Atlas.Conway
